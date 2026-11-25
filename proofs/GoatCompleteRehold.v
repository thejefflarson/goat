(* Completeness of algorithm W, stage 7.8j: what a use of a scheme re-holds
   (docs/design/phase7-proof-plan.md).

   [rh_t] (GoatHeld.v) gives each entry whose presence is a fresh quantified
   atom a field variable of its own and holds the equation that the variable is
   the field it replaced.  [rhf_t] lists those original fields in the order the
   equations come, so the equation at position [j] is about the variable
   [ea (m + j)] and the field [nth j].  [fvx S1 m fl] sends each such variable
   to the image of its field under [S1]; under it the rewritten type is
   convertible to the original ([rh_teq]) and every equation holds.  The
   conversion needs no fact about the presences: an entry whose presence is
   absent has a free field ([req_absf]), and a present one has the field the
   variable is sent to.

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
Require Import Goat.GoatInferW.
Require Import Goat.GoatHeld.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteCtx.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* The fields [rh_t] replaces, in the order of its equations. *)
Fixpoint rhf_t (pl : list atom) (T : typ) (m : nat) {struct T} : list typ :=
  match T with
  | typ_Arrow A B => let a := rhf_t pl A m in a ++ rhf_t pl B (m + length a)
  | typ_Record R => rhf_r pl R m
  | _ => nil
  end
with rhf_r (pl : list atom) (R : row) (m : nat) {struct R} : list typ :=
  match R with
  | row_Ext _ T R0 => let a := rhf_t pl T m in a ++ rhf_r pl R0 (m + length a)
  | row_Maybe _ P F R0 =>
      let a := rhf_t pl F m in
      let b := rhf_r pl R0 (m + length a) in
      a ++ b ++ (if fresh_pres pl P then F :: nil else nil)
  | _ => nil
  end.

Lemma rh_len : forall pl,
  (forall T m, snd (rh_t pl T m) = m + length (rhf_t pl T m) /\
               length (snd (fst (rh_t pl T m))) = length (rhf_t pl T m)) /\
  (forall R m, snd (rh_r pl R m) = m + length (rhf_r pl R m) /\
               length (snd (fst (rh_r pl R m))) = length (rhf_r pl R m)).
Proof.
  intros pl. apply typ_row_mutind; try (intros; cbn; split; lia).
  - intros A IHA B IHB m. cbn [rh_t rhf_t].
    destruct (rh_t pl A m) as [[A' H1] m1] eqn:E1. destruct (rh_t pl B m1) as [[B' H2] m2] eqn:E2.
    pose proof (IHA m) as IA. rewrite E1 in IA. simpl in IA. destruct IA as [IA1 IA2].
    pose proof (IHB m1) as IB. rewrite E2 in IB. simpl in IB. destruct IB as [IB1 IB2].
    simpl. subst m1. subst m2. rewrite !length_app. split; lia.
  - intros R IH m. cbn [rh_t rhf_t].
    destruct (rh_r pl R m) as [[R' H] m1] eqn:E. pose proof (IH m) as I. rewrite E in I. simpl in I. simpl. exact I.
  - intros l T IHT R IHR m. cbn [rh_r rhf_r].
    destruct (rh_t pl T m) as [[T' H1] m1] eqn:E1. destruct (rh_r pl R m1) as [[R' H2] m2] eqn:E2.
    pose proof (IHT m) as IA. rewrite E1 in IA. simpl in IA. destruct IA as [IA1 IA2].
    pose proof (IHR m1) as IB. rewrite E2 in IB. simpl in IB. destruct IB as [IB1 IB2].
    simpl. subst m1. subst m2. rewrite !length_app. split; lia.
  - intros l P IHP T IHT R IHR m. cbn [rh_r rhf_r].
    destruct (rh_t pl T m) as [[T' H1] m1] eqn:E1. destruct (rh_r pl R m1) as [[R' H2] m2] eqn:E2.
    pose proof (IHT m) as IA. rewrite E1 in IA. simpl in IA. destruct IA as [IA1 IA2].
    pose proof (IHR m1) as IB. rewrite E2 in IB. simpl in IB. destruct IB as [IB1 IB2].
    subst m1. subst m2. destruct (fresh_pres pl P); simpl; rewrite ?length_app; simpl; rewrite ?length_app; split; lia.
Qed.

(* ---- the extension that sends each variable to its field ---- *)

Fixpoint fvt (S1 : sub) (fl : list typ) (k : nat) (b : atom) : typ :=
  match fl with
  | nil => sT S1 b
  | F :: fl' => if Atom.eq_dec b (ea k) then apT S1 F else fvt S1 fl' (S k) b
  end.

Definition fvx (S1 : sub) (k : nat) (fl : list typ) : sub := Sub (fvt S1 fl k) (sR S1).

Lemma fvt_at : forall S1 fl k j, j < length fl -> fvt S1 fl k (ea (k + j)) = apT S1 (nth j fl typ_Unit).
Proof.
  intros S1 fl. induction fl as [|F fl IH]; intros k j Hj; [ simpl in Hj; lia | ].
  simpl. destruct j as [|j].
  - destruct (Atom.eq_dec (ea (k + 0)) (ea k)) as [_|N]; [ reflexivity | exfalso; apply N; f_equal; lia ].
  - destruct (Atom.eq_dec (ea (k + S j)) (ea k)) as [E|_].
    + apply ea_inj in E. lia.
    + replace (k + S j) with (S k + j) by lia. apply IH. simpl in Hj. lia.
Qed.

Lemma fvt_out : forall S1 fl k b, (forall j, j < length fl -> b <> ea (k + j)) -> fvt S1 fl k b = sT S1 b.
Proof.
  intros S1 fl. induction fl as [|F fl IH]; intros k b H; [ reflexivity | ].
  simpl. destruct (Atom.eq_dec b (ea k)) as [E|_].
  - exfalso. apply (H 0); [ simpl; lia | rewrite E; f_equal; lia ].
  - apply IH. intros j Hj E. apply (H (S j)); [ simpl; lia | rewrite E; f_equal; lia ].
Qed.

(* ---- the rewritten type is the original, and the equations hold ---- *)

Section Teq.

Variables (pl : list atom) (S1 S2 : sub) (n1 K : nat) (Tab : nat -> typ).

Hypothesis HO : forall b, old n1 b -> sT S2 b = sT S1 b.
Hypothesis HOr : forall r, sR S2 r = sR S1 r.
Hypothesis HF : forall k, n1 <= k -> k < K -> sT S2 (ea k) = apT S1 (Tab k).

Lemma ap_old_eq : (forall T, atT n1 T -> apT S2 T = apT S1 T) /\ (forall R, atR n1 R -> apR S2 R = apR S1 R).
Proof.
  split.
  - intros T [A B]. unfold apT. apply ap_typ_ext; [ intros a Ha; apply HO; apply A; exact Ha | intros r _; apply HOr ].
  - intros R [A B]. unfold apR. apply (proj2 ap_ext_mut); [ intros a Ha; apply HO; apply A; exact Ha | intros r _; apply HOr ].
Qed.

Lemma rh_teq :
  (forall T, pf T -> atT n1 T -> forall m, n1 <= m -> m + length (rhf_t pl T m) <= K ->
     (forall j, j < length (rhf_t pl T m) -> Tab (m + j) = nth j (rhf_t pl T m) typ_Unit) ->
     teq (apT S2 (fst (fst (rh_t pl T m)))) (apT S1 T) /\
     Forall (fun h => teq (apT S2 (h_fld h)) (apT S2 (h_val h))) (snd (fst (rh_t pl T m)))) /\
  (forall R, prf R -> atR n1 R -> forall m, n1 <= m -> m + length (rhf_r pl R m) <= K ->
     (forall j, j < length (rhf_r pl R m) -> Tab (m + j) = nth j (rhf_r pl R m) typ_Unit) ->
     req (apR S2 (fst (fst (rh_r pl R m)))) (apR S1 R) /\
     Forall (fun h => teq (apT S2 (h_fld h)) (apT S2 (h_val h))) (snd (fst (rh_r pl R m)))).
Proof.
  apply typ_row_mutind; cbn [pf prf]; try (intros; contradiction).
  - intros _ _ m _ _ _. cbn. split; [ apply teq_refl | constructor ].
  - intros _ _ m _ _ _. cbn. split; [ apply teq_refl | constructor ].
  - intros _ _ m _ _ _. cbn. split; [ apply teq_refl | constructor ].
  - intros _ _ m _ _ _. cbn. split; [ apply teq_refl | constructor ].
  - intros _ _ m _ _ _. cbn. split; [ apply teq_refl | constructor ].
  - intros A IHA B IHB [PA PB] [AA AB] m Hm HK Htab. cbn [rh_t rhf_t] in *.
    destruct (rh_t pl A m) as [[A' H1] m1] eqn:E1. destruct (rh_t pl B m1) as [[B' H2] m2] eqn:E2.
    pose proof (proj1 (rh_len pl) A m) as La. rewrite E1 in La. simpl in La. destruct La as [La1 La2].
    subst m1.
    assert (atA : atT n1 A) by (split; intros x Hx; [ apply AA | apply AB ]; simpl; fsetdec).
    assert (atB : atT n1 B) by (split; intros x Hx; [ apply AA | apply AB ]; simpl; fsetdec).
    rewrite length_app in HK.
    destruct (IHA PA atA m Hm ltac:(lia) ltac:(intros j Hj; rewrite (Htab j ltac:(rewrite length_app; lia)); apply app_nth1; exact Hj))
      as [TA FA]. rewrite E1 in TA, FA. simpl in TA, FA.
    destruct (IHB PB atB (m + length (rhf_t pl A m)) ltac:(lia) ltac:(lia) ltac:(intros j Hj;
        pose proof (Htab (length (rhf_t pl A m) + j) ltac:(rewrite length_app; lia)) as Hh; rewrite app_nth2 in Hh by lia;
        replace (length (rhf_t pl A m) + j - length (rhf_t pl A m)) with j in Hh by lia;
        replace (m + (length (rhf_t pl A m) + j)) with (m + length (rhf_t pl A m) + j) in Hh by lia;
        exact Hh))
      as [TB FB]. rewrite E2 in TB, FB. simpl in TB, FB.
    simpl. split.
    + rewrite !apT_Arrow. apply teq_arrow; assumption.
    + apply Forall_app. split; assumption.
  - intros R IH HR AR m Hm HK Htab. cbn [rh_t rhf_t] in *.
    destruct (rh_r pl R m) as [[R' H] m1] eqn:E.
    destruct (IH HR AR m Hm HK Htab) as [T1 F1]. rewrite E in T1, F1. simpl in T1, F1. simpl.
    split; [ | exact F1 ].
    change (apT S2 (typ_Record R')) with (typ_Record (apR S2 R')).
    change (apT S1 (typ_Record R)) with (typ_Record (apR S1 R)). apply teq_rec. exact T1.
  - intros a _ At m _ _ _. cbn [rh_t rhf_t fst snd]. split; [ | constructor ].
    rewrite (proj1 ap_old_eq _ At). apply teq_refl.
  - intros w A IH [HA _] At m _ _ _. cbn [rh_t rhf_t fst snd]. split; [ | constructor ].
    rewrite (proj1 ap_old_eq _ At). apply teq_refl.
  - intros _ _ m _ _ _. cbn. split; [ apply req_refl | constructor ].
  - intros r _ Ar m _ _ _. cbn [rh_r rhf_r fst snd]. split; [ | constructor ].
    rewrite (proj2 ap_old_eq _ Ar). apply req_refl.
  - intros l T IHT R IHR [PT PR] [AA AB] m Hm HK Htab. cbn [rh_r rhf_r] in *.
    destruct (rh_t pl T m) as [[T' H1] m1] eqn:E1. destruct (rh_r pl R m1) as [[R' H2] m2] eqn:E2.
    pose proof (proj1 (rh_len pl) T m) as La. rewrite E1 in La. simpl in La. destruct La as [La1 La2].
    subst m1.
    assert (atT' : atT n1 T) by (split; intros x Hx; [ apply AA | apply AB ]; simpl; fsetdec).
    assert (atR' : atR n1 R) by (split; intros x Hx; [ apply AA | apply AB ]; simpl; fsetdec).
    rewrite length_app in HK.
    destruct (IHT PT atT' m Hm ltac:(lia) ltac:(intros j Hj; rewrite (Htab j ltac:(rewrite length_app; lia)); apply app_nth1; exact Hj))
      as [TA FA]. rewrite E1 in TA, FA. simpl in TA, FA.
    destruct (IHR PR atR' (m + length (rhf_t pl T m)) ltac:(lia) ltac:(lia) ltac:(intros j Hj;
        pose proof (Htab (length (rhf_t pl T m) + j) ltac:(rewrite length_app; lia)) as Hh; rewrite app_nth2 in Hh by lia;
        replace (length (rhf_t pl T m) + j - length (rhf_t pl T m)) with j in Hh by lia;
        replace (m + (length (rhf_t pl T m) + j)) with (m + length (rhf_t pl T m) + j) in Hh by lia;
        exact Hh))
      as [TB FB]. rewrite E2 in TB, FB. simpl in TB, FB.
    simpl. split.
    + change (apR S2 (row_Ext l T' R')) with (row_Ext l (apT S2 T') (apR S2 R')).
      change (apR S1 (row_Ext l T R)) with (row_Ext l (apT S1 T) (apR S1 R)). apply req_head; assumption.
    + apply Forall_app. split; assumption.
  - intros l P IHP T IHT R IHR [PP [PT PR]] [AA AB] m Hm HK Htab. cbn [rh_r rhf_r] in *.
    destruct (rh_t pl T m) as [[T' H1] m1] eqn:E1. destruct (rh_r pl R m1) as [[R' H2] m2] eqn:E2.
    pose proof (proj1 (rh_len pl) T m) as La. rewrite E1 in La. simpl in La. destruct La as [La1 La2].
    pose proof (proj2 (rh_len pl) R m1) as Lb. rewrite E2 in Lb. simpl in Lb. destruct Lb as [Lb1 Lb2].
    subst m1.
    assert (atP : atT n1 P) by (split; intros x Hx; [ apply AA | apply AB ]; simpl; fsetdec).
    assert (atT' : atT n1 T) by (split; intros x Hx; [ apply AA | apply AB ]; simpl; fsetdec).
    assert (atR' : atR n1 R) by (split; intros x Hx; [ apply AA | apply AB ]; simpl; fsetdec).
    rewrite !length_app in HK.
    assert (HK' : m + length (rhf_t pl T m) + length (rhf_r pl R (m + length (rhf_t pl T m))) <= K)
      by (destruct (fresh_pres pl P); simpl in HK; lia).
    destruct (IHT PT atT' m Hm ltac:(lia) ltac:(intros j Hj; rewrite (Htab j ltac:(rewrite !length_app; lia));
        rewrite app_nth1 by exact Hj; reflexivity))
      as [TA FA]. rewrite E1 in TA, FA. simpl in TA, FA.
    destruct (IHR PR atR' (m + length (rhf_t pl T m)) ltac:(lia) ltac:(lia) ltac:(intros j Hj;
        pose proof (Htab (length (rhf_t pl T m) + j) ltac:(rewrite !length_app; lia)) as Hh;
        rewrite app_nth2 in Hh by lia;
        replace (length (rhf_t pl T m) + j - length (rhf_t pl T m)) with j in Hh by lia;
        replace (m + (length (rhf_t pl T m) + j)) with (m + length (rhf_t pl T m) + j) in Hh by lia;
        rewrite app_nth1 in Hh by exact Hj; exact Hh))
      as [TB FB]. rewrite E2 in TB, FB. simpl in TB, FB.
    assert (HKf : fresh_pres pl P = true -> m + length (rhf_t pl T m) + length (rhf_r pl R (m + length (rhf_t pl T m))) + 1 <= K)
      by (intro Hf; rewrite Hf in HK; simpl in HK; lia).
    assert (HP : apT S2 P = apT S1 P) by exact (proj1 ap_old_eq _ atP).
    destruct (fresh_pres pl P) eqn:Ef.
    + assert (Hfld : sT S2 (ea m2) = apT S1 T).
      { pose proof (Htab (length (rhf_t pl T m) + length (rhf_r pl R (m + length (rhf_t pl T m)))) ltac:(rewrite !length_app; simpl; lia)) as Hh.
        rewrite app_nth2 in Hh by lia.
        replace (length (rhf_t pl T m) + length (rhf_r pl R (m + length (rhf_t pl T m))) - length (rhf_t pl T m)) with (length (rhf_r pl R (m + length (rhf_t pl T m)))) in Hh by lia.
        rewrite app_nth2 in Hh by lia. rewrite Nat.sub_diag in Hh. simpl in Hh.
        assert (Hm2 : m2 = m + (length (rhf_t pl T m) + length (rhf_r pl R (m + length (rhf_t pl T m))))) by lia.
        rewrite Hm2. rewrite (HF (m + (length (rhf_t pl T m) + length (rhf_r pl R (m + length (rhf_t pl T m))))) ltac:(lia) ltac:(pose proof (HKf eq_refl); lia)), Hh. reflexivity. }
      simpl. split.
      * change (apR S2 (row_Maybe l P (typ_Var (ea m2)) R')) with (row_Maybe l (apT S2 P) (apT S2 (typ_Var (ea m2))) (apR S2 R')).
        change (apR S1 (row_Maybe l P T R)) with (row_Maybe l (apT S1 P) (apT S1 T) (apR S1 R)).
        apply req_maybe; [ rewrite HP; apply teq_refl | | exact TB ].
        rewrite apT_Var, Hfld. apply teq_refl.
      * apply Forall_app. split; [ assumption | ]. apply Forall_app. split; [ assumption | ].
        constructor; [ | constructor ]. cbn [h_fld h_val].
        rewrite apT_Var, Hfld. apply teq_sym. exact TA.
    + simpl. split.
      * change (apR S2 (row_Maybe l P T' R')) with (row_Maybe l (apT S2 P) (apT S2 T') (apR S2 R')).
        change (apR S1 (row_Maybe l P T R)) with (row_Maybe l (apT S1 P) (apT S1 T) (apR S1 R)).
        apply req_maybe; [ rewrite HP; apply teq_refl | exact TA | exact TB ].
      * apply Forall_app. split; assumption.
Qed.

End Teq.
