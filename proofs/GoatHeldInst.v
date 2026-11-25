(* A use of a scheme re-holds the equations of its open entries (ADR 0033
   amendment, issue 667).

   [rh_t] (GoatHeld.v) gives each open entry of an instance a field variable of
   its own and holds that the entry has the field it had when the presence is
   present.  The type it returns is the instance's up to conversion once the
   equations it holds are solved ([rh_sound]): an entry whose presence is
   absent has no field to speak of ([req_absf]), and one whose presence is not
   has the field the equation names.  It is even, holds even equations, and is
   the instance itself when no presence is fresh or the type has no entry. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatConv.
Require Import Goat.GoatInfer.
Require Import Goat.GoatHeld.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferSound.
Require Import Goat.GoatHeldSound.
Require Import Goat.GoatHeldV.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

Lemma HOk_nil : HOk nil.
Proof. constructor. Qed.

Lemma HOk_app : forall H1 H2, HOk H1 -> HOk H2 -> HOk (H1 ++ H2).
Proof. intros H1 H2. unfold HOk. rewrite Forall_app. tauto. Qed.

(* ------------------------------------------------------------------ *)
(* Nothing is held when no presence is fresh                            *)
(* ------------------------------------------------------------------ *)

Lemma fresh_pres_nil : forall P, fresh_pres nil P = false.
Proof. intros P. destruct P; reflexivity. Qed.

Lemma rh_nil_mut :
  (forall T m, rh_t nil T m = (T, nil, m)) /\
  (forall R m, rh_r nil R m = (R, nil, m)).
Proof.
  apply typ_row_mutind; cbn [rh_t rh_r]; try (intros; reflexivity).
  - intros A HA B HB m. rewrite HA, HB. reflexivity.
  - intros R HR m. rewrite HR. reflexivity.
  - intros l T HT R HR m. rewrite HT, HR. reflexivity.
  - intros l P HP T HT R HR m. rewrite HT, HR, fresh_pres_nil. reflexivity.
Qed.

Lemma rh_t_nil : forall T m, rh_t nil T m = (T, nil, m).
Proof. exact (proj1 rh_nil_mut). Qed.

(* ------------------------------------------------------------------ *)
(* Even types, even equations                                           *)
(* ------------------------------------------------------------------ *)

Lemma rh_ev_mut : forall ps, (forall a, In a ps -> ev a) ->
  (forall T m T' H m', rh_t ps T m = (T', H, m') -> EvT T -> EvT T' /\ HOk H /\ m <= m') /\
  (forall R m R' H m', rh_r ps R m = (R', H, m') -> EvR R -> EvR R' /\ HOk H /\ m <= m').
Proof.
  intros ps Hps. apply typ_row_mutind; cbn [rh_t rh_r];
    try (intros; match goal with E : (_, _, _) = (_, _, _) |- _ => inversion E; subst end;
         split; [ assumption | split; [ apply HOk_nil | lia ] ]; fail).
  - intros A HA B HB m T' H m' E Hev.
    destruct (rh_t ps A m) as [[A' H1] m1] eqn:E1.
    destruct (rh_t ps B m1) as [[B' H2] m2] eqn:E2. inversion E; subst; clear E.
    apply EvT_arrow_inv in Hev as [EA0 EB0].
    destruct (HA _ _ _ _ E1 EA0) as (EA & OA & LA).
    destruct (HB _ _ _ _ E2 EB0) as (EB & OB & LB).
    exact (conj (EvT_arrow _ _ EA EB) (conj (HOk_app _ _ OA OB) (Nat.le_trans _ _ _ LA LB))).
  - intros R HR m T' H m' E Hev.
    destruct (rh_r ps R m) as [[R1 H1] m1] eqn:E1. inversion E; subst; clear E.
    apply EvT_Record in Hev.
    destruct (HR _ _ _ _ E1 Hev) as (ER & OR & LR).
    exact (conj (proj2 (EvT_Record _) ER) (conj OR LR)).
  - intros l T HT R HR m R' H m' E Hev.
    destruct (rh_t ps T m) as [[T1 H1] m1] eqn:E1.
    destruct (rh_r ps R m1) as [[R1 H2] m2] eqn:E2. inversion E; subst; clear E.
    apply EvR_ext_inv in Hev as [ET0 ER0].
    destruct (HT _ _ _ _ E1 ET0) as (ET & OT & LT).
    destruct (HR _ _ _ _ E2 ER0) as (ER & OR & LR).
    exact (conj (EvR_ext _ _ _ ET ER) (conj (HOk_app _ _ OT OR) (Nat.le_trans _ _ _ LT LR))).
  - intros l P HP T HT R HR m R' H m' E Hev.
    destruct (rh_t ps T m) as [[F1 H1] m1] eqn:E1.
    destruct (rh_r ps R m1) as [[R1 H2] m2] eqn:E2.
    apply EvR_maybe_inv in Hev as (EP & EF0 & ER0).
    destruct (HT _ _ _ _ E1 EF0) as (EF & OF & LF).
    destruct (HR _ _ _ _ E2 ER0) as (ER & OR & LR).
    destruct (fresh_pres ps P) eqn:Ef.
    + inversion E; subst; clear E.
      assert (Hy : EvT (typ_Var (ea m2))) by (apply EvT_var; exists m2; reflexivity).
      refine (conj (EvR_maybe _ _ _ _ EP Hy ER) (conj _ _)).
      * apply HOk_app; [ exact OF | ]. apply HOk_app; [ exact OR | ].
        constructor; [ | constructor ]. cbn [h_pres h_fld h_val h_rest].
        exact (conj EP (conj Hy (conj EF ER))).
      * lia.
    + inversion E; subst; clear E.
      exact (conj (EvR_maybe _ _ _ _ EP EF ER) (conj (HOk_app _ _ OF OR) (Nat.le_trans _ _ _ LF LR))).
Qed.

(* ------------------------------------------------------------------ *)
(* The re-held type is the instance, once the equations are solved      *)
(* ------------------------------------------------------------------ *)

(* An entry whose presence is absent, or whose field types are equal, is the
   same entry: the conversion a held equation licenses. *)
Lemma reqD_maybe_fld : forall D l P A B R,
  (P = typ_Bool \/ teqD D A B) ->
  reqD D (row_Maybe l P A R) (row_Maybe l P B R).
Proof.
  intros D l P A B R Hc. unfold reqD. rewrite !nfR_maybe.
  destruct (is_abs P && rlacksD D l (nfR D R)) eqn:Hd; [ apply req_refl | ].
  destruct Hc as [-> | Ht].
  - cbn [nfT]. apply req_absf.
  - apply req_maybe; [ apply teq_refl | exact Ht | apply req_refl ].
Qed.

Lemma teqD_maybe_fld : forall D l P A B R,
  (P = typ_Bool \/ teqD D A B) ->
  teqD D (typ_Record (row_Maybe l P A R)) (typ_Record (row_Maybe l P B R)).
Proof. intros. apply teqD_Record_reqD. apply reqD_maybe_fld. assumption. Qed.

Lemma rh_sound_mut : forall ps D S,
  (forall T m T' H m', rh_t ps T m = (T', H, m') -> Sol D S H -> teqD D (apT S T) (apT S T')) /\
  (forall R m R' H m', rh_r ps R m = (R', H, m') -> Sol D S H -> reqD D (apR S R) (apR S R')).
Proof.
  intros ps D S. apply typ_row_mutind; cbn [rh_t rh_r];
    try (intros; match goal with E : (_, _, _) = (_, _, _) |- _ => inversion E; subst end;
         first [ apply teqD_refl | apply reqD_refl ]; fail).
  - intros A HA B HB m T' H m' E Hs.
    destruct (rh_t ps A m) as [[A' H1] m1] eqn:E1.
    destruct (rh_t ps B m1) as [[B' H2] m2] eqn:E2. inversion E; subst; clear E.
    apply Sol_app in Hs as [S1 S2].
    cbn [apT ap_typ]. fold (apT S A) (apT S B) (apT S A') (apT S B').
    exact (teqD_Arrow _ _ _ _ _ (HA _ _ _ _ E1 S1) (HB _ _ _ _ E2 S2)).
  - intros R HR m T' H m' E Hs.
    destruct (rh_r ps R m) as [[R1 H1] m1] eqn:E1. inversion E; subst; clear E.
    cbn [apT ap_typ]. fold (apR S R) (apR S R1).
    exact (teqD_Record_reqD _ _ _ (HR _ _ _ _ E1 Hs)).
  - intros l T HT R HR m R' H m' E Hs.
    destruct (rh_t ps T m) as [[T1 H1] m1] eqn:E1.
    destruct (rh_r ps R m1) as [[R1 H2] m2] eqn:E2. inversion E; subst; clear E.
    apply Sol_app in Hs as [S1 S2].
    cbn [apR ap_row]. fold (apT S T) (apT S T1) (apR S R) (apR S R1).
    pose proof (HT _ _ _ _ E1 S1) as Ht. pose proof (HR _ _ _ _ E2 S2) as Hr.
    unfold reqD in *. rewrite !nfR_ext. apply req_head; [ exact Ht | exact Hr ].
  - intros l P HP T HT R HR m R' H m' E Hs.
    destruct (rh_t ps T m) as [[F1 H1] m1] eqn:E1.
    destruct (rh_r ps R m1) as [[R1 H2] m2] eqn:E2.
    pose proof (HT _ _ _ _ E1) as Hf. pose proof (HR _ _ _ _ E2) as Hr.
    destruct (fresh_pres ps P) eqn:Ef.
    + inversion E; subst; clear E.
      apply Sol_app in Hs as [S1 S2]. apply Sol_app in S2 as [S2 S3].
      inversion S3 as [|? ? Hh _]; subst. cbn [apE h_pres h_fld h_val] in Hh.
      pose proof (Hf S1) as Hf'. pose proof (Hr S2) as Hr'.
      cbn [apR ap_row].
      fold (apT S P) (apT S T) (apT S (typ_Var (ea m2))) (apT S F1) (apR S R) (apR S R1).
      assert (Hc : apT S P = typ_Bool \/ teqD D (apT S T) (apT S (typ_Var (ea m2)))).
      { destruct Hh as [Hb | Ht]; [ left; exact Hb | right ].
        exact (teqD_trans _ _ _ _ Hf' (teqD_sym _ _ _ Ht)). }
      eapply reqD_trans.
      * exact (reqD_maybe _ _ _ _ _ _ _ _ (teqD_refl _ _) (teqD_refl _ _) Hr').
      * exact (reqD_maybe_fld _ _ _ _ _ _ Hc).
    + inversion E; subst; clear E.
      apply Sol_app in Hs as [S1 S2].
      cbn [apR ap_row]. fold (apT S P) (apT S T) (apT S F1) (apR S R) (apR S R1).
      exact (reqD_maybe _ _ _ _ _ _ _ _ (teqD_refl _ _) (Hf S1) (Hr S2)).
Qed.

(* A derivation at the instance is one at the re-held type once the
   equations are solved. *)
Lemma V_conv_sol : forall Gs D n e T T' H,
  V Gs D n e T nil ->
  (forall S D'' n'', Good D n S D'' n'' -> Sol D'' S H -> teqD D'' (apT S T) (apT S T')) ->
  V Gs D n e T' H.
Proof.
  intros Gs D n e T T' H HV Hc S D'' n'' Hg Hs.
  eapply T_ConvD; [ exact (HV S D'' n'' Hg (Sol_nil _ _)) | exact (Hc S D'' n'' Hg Hs) ].
Qed.
