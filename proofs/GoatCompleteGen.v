(* Completeness of algorithm W, stage 7.5, part L1: generalization is monotone
   (docs/design/phase7-proof-plan.md).

   [gen_mono] is the let case's scheme comparison.  The derivation generalizes
   [T1 = S2 T'] over its context [Gq] (the pin included) and records the sorts
   [k] and kinds [rk]; the algorithm generalizes [T'] over its context [Gp] and
   records the sorts [Dal] gives (GoatInfer.v, [gen_ren]).  Applying [S2] to the
   algorithm's scheme, as the induction does to its whole context, gives a
   scheme whose instances include every instance of the derivation's.  The
   quantified variables of the algorithm's scheme are odd atoms [S2] leaves
   alone, so an instance of the derivation's scheme becomes one of the
   algorithm's by sending the odd atom that stands for [a] to what the instance
   sends [S2 a] to; [kres Dal Dd S2] (the induction's hypothesis, with [Dd] the
   environment the derivation's premise lives in) carries the sorts across.

   What the comparison needs of the context is that [S2] sends the variables the
   algorithm keeps free (the free variables of [Gp]) to types over the
   variables the derivation keeps free ([frozen]).  The pin enters through
   [Gp] and [Gq], which are both [pin_ctx] of the contexts, so a numeral
   variable that the algorithm pins ([let_pin], GoatInfer.v) is frozen by the
   derivation's [lit_pinned] premise ([lit_pin_frozen]). *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferKnot.
Require Import Goat.GoatInferGen.
Require Import Goat.GoatCompleteInst.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- sorts and kinds read only the variables of the type ---- *)

Lemma sat_loc_mut : forall (D D' : denv),
  (forall T, (forall k, (forall a, a `in` ftv_typ T -> D' a = D a) ->
                        (forall r, r `in` frv_typ T -> drk D' r = drk D r) ->
                        sat D k T -> sat D' k T) /\
             (forall w j, (forall a, a `in` ftv_typ T -> D' a = D a) ->
                          (forall r, r `in` frv_typ T -> drk D' r = drk D r) ->
                          spine_sat D w j T -> spine_sat D' w j T)) /\
  (forall R k, (forall a, a `in` ftv_row R -> D' a = D a) ->
               (forall r, r `in` frv_row R -> drk D' r = drk D r) ->
               rsat D k R -> rsat D' k R).
Proof.
  intros D D'. apply typ_row_mutind; simpl.
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - intros T1 [IH1 _] T2 [_ IH2]. split; [ intros; assumption | ].
    intros w j Hv Hr [Hu Hs]. split.
    + intros Hc. refine (IH1 k_Eq _ _ (Hu Hc)); intros; [ apply Hv | apply Hr ]; fsetdec.
    + refine (IH2 w (S j) _ _ Hs); intros; [ apply Hv | apply Hr ]; fsetdec.
  - intros R IH. split; [ | intros; contradiction ]. intros k Hv Hr. destruct k; simpl;
      first [ (intros _; exact I) | (intros HH; contradiction) | exact (IH _ Hv Hr) ].
  - intros a. split; [ intros k Hv Hr Hs; rewrite Hv; [ exact Hs | fsetdec ] | intros; contradiction ].
  - intros i. split; intros; first [ assumption | contradiction ].
  - intros B IH. split; [ | intros; contradiction ]. intros k Hv Hr Hs.
    destruct k; try exact I; try contradiction.
    exact (proj1 IH k_Eq Hv Hr Hs).
  - intros w A IH. split; [ | intros; contradiction ]. intros k Hv Hr Hs.
    destruct k; try exact I; try contradiction.
    exact (proj2 IH w 0 Hv Hr Hs).
  - intros k _ _ _. exact I.
  - intros r k Hv Hr Hs. rewrite Hr; [ exact Hs | fsetdec ].
  - intros l T [IHT _] R IHR k Hv Hr [Hs1 Hs2]. split.
    + refine (IHT k _ _ Hs1); intros; [ apply Hv | apply Hr ]; fsetdec.
    + refine (IHR k _ _ Hs2); intros; [ apply Hv | apply Hr ]; fsetdec.
  - intros l P _ T [IHT _] R IHR k Hv Hr [Hs1 Hs2]. split.
    + destruct Hs1 as [Hp | Hs1]; [ left; exact Hp | right ].
      refine (IHT k _ _ Hs1); intros; [ apply Hv | apply Hr ]; fsetdec.
    + refine (IHR k _ _ Hs2); intros; [ apply Hv | apply Hr ]; fsetdec.
Qed.

Lemma sat_loc : forall (D D' : denv) k T,
  (forall a, a `in` ftv_typ T -> D' a = D a) ->
  (forall r, r `in` frv_typ T -> drk D' r = drk D r) ->
  sat D k T -> sat D' k T.
Proof. intros D D' k T Hv Hr Hs. exact (proj1 (proj1 (sat_loc_mut D D') T) k Hv Hr Hs). Qed.

Lemma rsat_loc : forall (D D' : denv) k R,
  (forall a, a `in` ftv_row R -> D' a = D a) ->
  (forall r, r `in` frv_row R -> drk D' r = drk D r) ->
  rsat D k R -> rsat D' k R.
Proof. intros D D' k R Hv Hr Hs. exact (proj2 (sat_loc_mut D D') R k Hv Hr Hs). Qed.

Lemma rlacksD_loc : forall (D D' : denv) l R,
  (forall r, r `in` frv_row R -> drk D' r = drk D r) ->
  rlacksD D' l R = rlacksD D l R.
Proof.
  intros D D' l R Hr. induction R as [|r|l' T R IH|l' P T R IH]; simpl in *; auto.
  - rewrite Hr; [ reflexivity | fsetdec ].
  - rewrite IH; [ reflexivity | intros; apply Hr; fsetdec ].
  - rewrite IH; [ reflexivity | intros; apply Hr; fsetdec ].
Qed.

Lemma rkok_loc : forall (D D' : denv) K R,
  (forall a, a `in` ftv_row R -> D' a = D a) ->
  (forall r, r `in` frv_row R -> drk D' r = drk D r) ->
  rkok D K R -> rkok D' K R.
Proof.
  intros D D' K R Hv Hr [H1 H2]. split; [ eapply rsat_loc; eauto | ].
  intros l Hl. rewrite (rlacksD_loc D D' l R Hr). apply H2. exact Hl.
Qed.

(* ---- an instance of a generalization, moved into the environment of an
   instance of another ---- *)

(* The environment in which an instance [st'], [sr'] of a scheme with
   quantified sets [Vt], [Vr] and kinds [k], [rk] respects the kinds. *)
Lemma kres_star : forall (D' : denv) (Vt Vr : atoms) k rk st' sr',
  (forall a, a `notin` Vt -> st' a = typ_Var a) ->
  (forall r, r `notin` Vr -> sr' r = row_Var r) ->
  (forall a, a `in` Vt -> sat D' (k a) (st' a)) ->
  (forall r, r `in` Vr -> rkok D' (rk r) (sr' r)) ->
  kres (extr (ext D' Vt k) Vr rk) D' st' /\ rkres (extr (ext D' Vt k) Vr rk) D' sr'.
Proof.
  intros D' Vt Vr k rk st' sr' H1 H2 H3 H4. split.
  - intros a. rewrite extr_dsort.
    destruct (AtomSetProperties.In_dec a Vt) as [Hi|Hn].
    + rewrite (ext_in _ _ _ _ Hi). apply H3. exact Hi.
    + rewrite (ext_out _ _ _ _ Hn). rewrite (H1 a Hn). cbn [sat]. apply finer_refl.
  - intros r.
    destruct (AtomSetProperties.In_dec r Vr) as [Hi|Hn].
    + rewrite (extr_in _ _ _ _ Hi). apply H4. exact Hi.
    + rewrite (extr_out _ _ _ _ Hn). rewrite ext_drk. rewrite (H2 r Hn). apply rkok_self.
Qed.

Lemma gm_sat : forall (D D' : denv) (Vt Vr : atoms) k rk st' sr' K Y,
  (forall a, a `notin` Vt -> st' a = typ_Var a) ->
  (forall r, r `notin` Vr -> sr' r = row_Var r) ->
  (forall a, a `in` Vt -> sat D' (k a) (st' a)) ->
  (forall r, r `in` Vr -> rkok D' (rk r) (sr' r)) ->
  (forall c, c `in` ftv_typ Y -> c `notin` Vt -> D' c = D c) ->
  (forall p, p `in` frv_typ Y -> p `notin` Vr -> drk D' p = drk D p) ->
  sat (extr (ext D Vt k) Vr rk) K Y -> sat D' K (ap_typ st' sr' Y).
Proof.
  intros D D' Vt Vr k rk st' sr' K Y H1 H2 H3 H4 Ha Hb Hs.
  destruct (kres_star D' Vt Vr k rk st' sr' H1 H2 H3 H4) as [Hk Hr].
  eapply sat_ap; [ exact Hk | exact Hr | ].
  eapply sat_loc; [ | | exact Hs ].
  - intros c Hc. rewrite !extr_dsort.
    destruct (AtomSetProperties.In_dec c Vt) as [Hi|Hn].
    + rewrite !(ext_in _ _ _ _ Hi). reflexivity.
    + rewrite !(ext_out _ _ _ _ Hn). apply Ha; assumption.
  - intros p Hp.
    destruct (AtomSetProperties.In_dec p Vr) as [Hi|Hn].
    + rewrite !(extr_in _ _ _ _ Hi). reflexivity.
    + rewrite !(extr_out _ _ _ _ Hn). rewrite !ext_drk. apply Hb; assumption.
Qed.

Lemma gm_rkok : forall (D D' : denv) (Vt Vr : atoms) k rk st' sr' K R,
  (forall a, a `notin` Vt -> st' a = typ_Var a) ->
  (forall r, r `notin` Vr -> sr' r = row_Var r) ->
  (forall a, a `in` Vt -> sat D' (k a) (st' a)) ->
  (forall r, r `in` Vr -> rkok D' (rk r) (sr' r)) ->
  (forall c, c `in` ftv_row R -> c `notin` Vt -> D' c = D c) ->
  (forall p, p `in` frv_row R -> p `notin` Vr -> drk D' p = drk D p) ->
  rkok (extr (ext D Vt k) Vr rk) K R -> rkok D' K (ap_row st' sr' R).
Proof.
  intros D D' Vt Vr k rk st' sr' K R H1 H2 H3 H4 Ha Hb Hs.
  destruct (kres_star D' Vt Vr k rk st' sr' H1 H2 H3 H4) as [Hk Hr].
  eapply rkok_ap; [ exact Hk | exact Hr | ].
  eapply rkok_loc; [ | | exact Hs ].
  - intros c Hc. rewrite !extr_dsort.
    destruct (AtomSetProperties.In_dec c Vt) as [Hi|Hn].
    + rewrite !(ext_in _ _ _ _ Hi). reflexivity.
    + rewrite !(ext_out _ _ _ _ Hn). apply Ha; assumption.
  - intros p Hp.
    destruct (AtomSetProperties.In_dec p Vr) as [Hi|Hn].
    + rewrite !(extr_in _ _ _ _ Hi). reflexivity.
    + rewrite !(extr_out _ _ _ _ Hn). rewrite !ext_drk. apply Hb; assumption.
Qed.
