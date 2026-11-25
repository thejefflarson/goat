(* Soundness statements that carry held equations (ADR 0033 amendment, issue 667).

   [V Gs D n e T H] says [e] has type [T] in [Gs] after every [Good] step [S]
   from the state [(D, n)] that solves the equations [H].  The soundness
   theorem for a term is a [V]: the type is derivable once the equations the
   algorithm still holds are solved, and not before.  [V_push] moves a [V]
   along a step the algorithm took, and the lemmas after it are the typing
   rules, the coercion step and the [let] proofs over [V].  A [let] discharges
   the equations of its bound term with [dis_sound] first, and generalizes the
   type that results ([V_let]). *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
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
Require Import Goat.GoatElab.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatClose.
Require Import Goat.GoatInferW.
Require Import Goat.GoatInferSound.
Require Import Goat.GoatHeldSound.
Require Import Stdlib.Lists.List.
Import ListNotations.

Definition V (Gs : ctx) (D : denv) (n : nat) (e : exp) (T : typ) (H : list heq) : Prop :=
  forall S D'' n'', Good D n S D'' n'' -> Sol D'' S H -> typing D'' (apC S Gs) e (apT S T).

(* ------------------------------------------------------------------ *)
(* Moving along a step, and weakening the equations                     *)
(* ------------------------------------------------------------------ *)

Lemma V_push : forall Gs D n e T H t D' n',
  Good D n t D' n' -> V Gs D n e T H -> V (apC t Gs) D' n' e (apT t T) (apH t H).
Proof.
  intros Gs D n e T H t D' n' Ht HV S D'' n'' Hg Hs.
  pose proof (HV (scomp S t) D'' n'' (Good_comp _ _ _ _ _ _ _ _ Ht Hg) (proj1 (Sol_apH _ _ _ _) Hs)) as Hty.
  rewrite <- apC_comp, <- apT_comp in Hty. exact Hty.
Qed.

Lemma V_mono : forall Gs D n e T H H',
  (forall S D'' n'', Good D n S D'' n'' -> Sol D'' S H' -> Sol D'' S H) ->
  V Gs D n e T H -> V Gs D n e T H'.
Proof. intros Gs D n e T H H' Hm HV S D'' n'' Hg Hs. exact (HV S D'' n'' Hg (Hm S D'' n'' Hg Hs)). Qed.

Lemma V_weak_l : forall Gs D n e T H1 H2, V Gs D n e T H1 -> V Gs D n e T (H1 ++ H2).
Proof.
  intros. eapply V_mono; [ | eassumption ]. intros S D'' n'' _ Hs. apply Sol_app in Hs. exact (proj1 Hs).
Qed.

Lemma V_weak_r : forall Gs D n e T H1 H2, V Gs D n e T H2 -> V Gs D n e T (H1 ++ H2).
Proof.
  intros. eapply V_mono; [ | eassumption ]. intros S D'' n'' _ Hs. apply Sol_app in Hs. exact (proj2 Hs).
Qed.

(* A derivation with no equations held is a [V] with none. *)
Lemma V_typing : forall Gs D n e T, WfCtx Gs -> typing D Gs e T -> V Gs D n e T nil.
Proof.
  intros Gs D n e T HG Hty S D'' n'' Hg _. exact (typing_ap_G D n S D'' n'' _ _ _ Hg HG Hty).
Qed.

(* The solution of the equations a run of [dis] discharged gives the typing
   at the state it leaves. *)
Lemma V_dis : forall k f Gs D n e T H d D' n',
  V Gs D n e T H -> dis k f D H n = Some (d, D', n') -> DOk D n -> HOk H ->
  Good D n d D' n' /\ typing D' (apC d Gs) e (apT d T).
Proof.
  intros k f Gs D n e T H d D' n' HV E HD HH.
  destruct (dis_sound k f D H n d D' n' E HD HH) as (Hg & Hs).
  exact (conj Hg (HV d D' n' Hg Hs)).
Qed.

(* ------------------------------------------------------------------ *)
(* Typing rules over V                                                  *)
(* ------------------------------------------------------------------ *)

Lemma V_conv : forall Gs D n e T T' H, V Gs D n e T H -> teqD D T T' -> V Gs D n e T' H.
Proof.
  intros Gs D n e T T' H HV Ht S D'' n'' Hg Hs.
  eapply T_ConvD; [ exact (HV S D'' n'' Hg Hs) | exact (lift_teqD _ _ _ _ _ _ _ Hg Ht) ].
Qed.

Lemma V_coerce : forall Gs D n e cs T T' H,
  chainD D cs T T' -> V Gs D n e T H -> V Gs D n (coerce cs e) T' H.
Proof.
  intros Gs D n e cs T T' H Hc HV S D'' n'' Hg Hs.
  exact (coerce_typingD _ _ _ _ _ _ (chainD_apT S D n D'' n'' _ _ _ Hg Hc) (HV S D'' n'' Hg Hs)).
Qed.

Lemma V_app : forall Gs D n e1 e2 A B H1 H2,
  V Gs D n e1 (typ_Arrow A B) H1 -> V Gs D n e2 A H2 -> V Gs D n (e_app e1 e2) B (H1 ++ H2).
Proof.
  intros Gs D n e1 e2 A B H1 H2 V1 V2 S D'' n'' Hg Hs. apply Sol_app in Hs as [Hs1 Hs2].
  eapply T_App; [ exact (V1 S D'' n'' Hg Hs1) | exact (V2 S D'' n'' Hg Hs2) ].
Qed.

Lemma V_if : forall Gs D n c a b T H1 H2 H3,
  V Gs D n c typ_Bool H1 -> V Gs D n a T H2 -> V Gs D n b T H3 ->
  V Gs D n (e_ite c a b) T (H1 ++ H2 ++ H3).
Proof.
  intros Gs D n c a b T H1 H2 H3 V1 V2 V3 S D'' n'' Hg Hs.
  apply Sol_app in Hs as [Hs1 Hs]. apply Sol_app in Hs as [Hs2 Hs3].
  eapply T_If; [ exact (V1 S D'' n'' Hg Hs1) | exact (V2 S D'' n'' Hg Hs2) | exact (V3 S D'' n'' Hg Hs3) ].
Qed.

Lemma V_proj : forall Gs D n e l T R H,
  V Gs D n e (typ_Record (row_Ext l T R)) H -> V Gs D n (e_proj e l) T H.
Proof.
  intros Gs D n e l T R H HV S D'' n'' Hg Hs.
  eapply T_Proj. exact (HV S D'' n'' Hg Hs).
Qed.

Lemma apC_cons_mono : forall s x T G,
  apC s ((x ~ sch_mono T) ++ G) = (x ~ sch_mono (apT s T)) ++ apC s G.
Proof. intros. rewrite apC_app, apC_single, apS_mono. reflexivity. Qed.

Lemma V_abs : forall Gs D n x A B e H,
  V ((x ~ sch_mono A) ++ Gs) D n e B H -> lce 0 e -> x `notin` dom Gs ->
  V Gs D n (e_abs (cl 0 x e)) (typ_Arrow A B) H.
Proof.
  intros Gs D n x A B e H HV Hlc Hx S D'' n'' Hg Hs.
  pose proof (HV S D'' n'' Hg Hs) as Hty. rewrite apC_cons_mono in Hty.
  cbn [apT ap_typ]. fold (apT S A) (apT S B).
  apply T_Abs with (L := dom Gs `union` {{x}}). intros y Hy.
  assert (Hdom : y `notin` dom ((x ~ sch_mono (apT S A)) ++ apC S Gs)) by (simpl; rewrite dom_apC; fsetdec).
  exact (typing_open_cl D'' (apC S Gs) x y (sch_mono (apT S A)) _ _ Hty Hlc Hdom).
Qed.

(* Renaming the variable a [V] binds. *)
Lemma V_open_cl : forall Gs D n x y sc e T H,
  V ((x ~ sc) ++ Gs) D n e T H -> lce 0 e -> y `notin` dom ((x ~ sc) ++ Gs) ->
  V ((y ~ sc) ++ Gs) D n (open_exp_wrt_exp (cl 0 x e) (e_fvar_f y)) T H.
Proof.
  intros Gs D n x y sc e T H HV Hlc Hy S D'' n'' Hg Hs.
  pose proof (HV S D'' n'' Hg Hs) as Hty. rewrite apC_app, apC_single in Hty.
  rewrite apC_app, apC_single.
  assert (Hdom : y `notin` dom ((x ~ apS S sc) ++ apC S Gs)) by (simpl in *; rewrite dom_apC; fsetdec).
  exact (typing_open_cl D'' (apC S Gs) x y (apS S sc) _ _ Hty Hlc Hdom).
Qed.

(* A [let] that keeps its bound term monomorphic, both parts at one state. *)
Lemma V_letmono : forall Gs D n x e1 e2 T1 T2 H1 H2,
  V Gs D n e1 T1 H1 -> V ((x ~ sch_mono T1) ++ Gs) D n e2 T2 H2 -> lce 0 e2 -> x `notin` dom Gs ->
  V Gs D n (e_let e1 (cl 0 x e2)) T2 (H1 ++ H2).
Proof.
  intros Gs D n x e1 e2 T1 T2 H1 H2 V1 V2 Hlc Hx S D'' n'' Hg Hs.
  apply Sol_app in Hs as [Hs1 Hs2].
  pose proof (V2 S D'' n'' Hg Hs2) as Hty. rewrite apC_cons_mono in Hty.
  apply T_LetMono with (L := dom Gs `union` {{x}}) (T1 := apT S T1).
  - exact (V1 S D'' n'' Hg Hs1).
  - intros y Hy.
    assert (Hdom : y `notin` dom ((x ~ sch_mono (apT S T1)) ++ apC S Gs)) by (simpl; rewrite dom_apC; fsetdec).
    exact (typing_open_cl D'' (apC S Gs) x y (sch_mono (apT S T1)) _ _ Hty Hlc Hdom).
Qed.

(* The same when the body ran after a step [s2]: the bound term is moved to the
   body's state and the equations of both stay held. *)
Lemma V_letmono_step : forall G1 D1 n1 x e1 e2 T1 T2 H1 H2 s2 D2 n2,
  Good D1 n1 s2 D2 n2 ->
  V G1 D1 n1 e1 T1 H1 -> V ((x ~ sch_mono (apT s2 T1)) ++ apC s2 G1) D2 n2 e2 T2 H2 ->
  lce 0 e2 -> x `notin` dom G1 ->
  V (apC s2 G1) D2 n2 (e_let e1 (cl 0 x e2)) T2 (apH s2 H1 ++ H2).
Proof.
  intros G1 D1 n1 x e1 e2 T1 T2 H1 H2 s2 D2 n2 Hg V1 V2 Hlc Hx.
  apply (V_letmono (apC s2 G1) D2 n2 x e1 e2 (apT s2 T1) T2 (apH s2 H1) H2);
    [ exact (V_push _ _ _ _ _ _ _ _ _ Hg V1) | exact V2 | exact Hlc | pose proof (dom_apC s2 G1); fsetdec ].
Qed.

(* ------------------------------------------------------------------ *)
(* Field lists                                                          *)
(* ------------------------------------------------------------------ *)

Definition VF (Gs : ctx) (D : denv) (n : nat) (fs : fields) (R : row) (H : list heq) : Prop :=
  forall S D'' n'', Good D n S D'' n'' -> Sol D'' S H -> field_typing D'' (apC S Gs) fs (apR S R).

Lemma VF_push : forall Gs D n fs R H t D' n',
  Good D n t D' n' -> VF Gs D n fs R H -> VF (apC t Gs) D' n' fs (apR t R) (apH t H).
Proof.
  intros Gs D n fs R H t D' n' Ht HV S D'' n'' Hg Hs.
  pose proof (HV (scomp S t) D'' n'' (Good_comp _ _ _ _ _ _ _ _ Ht Hg) (proj1 (Sol_apH _ _ _ _) Hs)) as Hty.
  rewrite <- apC_comp, <- apR_comp in Hty. exact Hty.
Qed.

Lemma VF_nil : forall Gs D n, uniq Gs -> VF Gs D n fs_nil row_Empty nil.
Proof.
  intros Gs D n Hu S D'' n'' Hg _. apply FT_nil. apply uniq_apC. exact Hu.
Qed.

Lemma VF_cons : forall Gs D n l e T fs R H1 H2,
  V Gs D n e T H1 -> VF Gs D n fs R H2 -> VF Gs D n (fs_cons l e fs) (row_Ext l T R) (H1 ++ H2).
Proof.
  intros Gs D n l e T fs R H1 H2 V1 V2 S D'' n'' Hg Hs. apply Sol_app in Hs as [Hs1 Hs2].
  apply FT_cons; [ exact (V1 S D'' n'' Hg Hs1) | exact (V2 S D'' n'' Hg Hs2) ].
Qed.

Lemma V_record : forall Gs D n fs R H,
  VF Gs D n fs R H -> no_meth fs = true -> V Gs D n (e_rec fs) (typ_Record R) H.
Proof.
  intros Gs D n fs R H HV Hnm S D'' n'' Hg Hs. apply T_Record; [ exact (HV S D'' n'' Hg Hs) | exact Hnm ].
Qed.

Lemma V_spread : forall Gs D n e1 e2 l P T R H1 H2,
  V Gs D n e1 (typ_Record (row_Maybe l P T R)) H1 -> V Gs D n e2 T H2 ->
  V Gs D n (e_spread e1 l e2) (typ_Record (row_Ext l T R)) (H1 ++ H2).
Proof.
  intros Gs D n e1 e2 l P T R H1 H2 V1 V2 S D'' n'' Hg Hs. apply Sol_app in Hs as [Hs1 Hs2].
  eapply T_Spread; [ exact (V1 S D'' n'' Hg Hs1) | exact (V2 S D'' n'' Hg Hs2) ].
Qed.

Lemma VF_dis : forall k f Gs D n fs R H d D' n',
  VF Gs D n fs R H -> dis k f D H n = Some (d, D', n') -> DOk D n -> HOk H ->
  Good D n d D' n' /\ field_typing D' (apC d Gs) fs (apR d R).
Proof.
  intros k f Gs D n fs R H d D' n' HV E HD HH.
  destruct (dis_sound k f D H n d D' n' E HD HH) as (Hg & Hs).
  exact (conj Hg (HV d D' n' Hg Hs)).
Qed.
