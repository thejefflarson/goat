(* Completeness of algorithm W, stage 7.8j: the image class of an instance
   (docs/design/phase7-proof-plan.md).

   An instance of a scheme that the derivation reads, and the instance the
   algorithm's run reads of the scheme in its context, are compared by [sch_leT]
   (GoatCompleteSchT.v).  Over the fragment the run's use of a scheme needs three
   facts about the instance's images that [instT] does not record, and
   [instQ] adds them:

   - [PresI]: a quantified atom that stands for the presence of an entry of the
     body is sent to [Unit] or [Bool].  The run's use of the scheme re-holds an
     equation for each such entry ([rh_t], GoatHeld.v), and discharging it
     reads the presence as one of the two.
   - [NNI]: a quantified atom of sort [Numeric] or [Quot] is not sent to a
     record, which is the [NNL] clause of [LiveG] (GoatCompleteLive.v) for the
     fresh atom the run gives it.
   - [RowSorts]: each quantified row has sort [Any] or [Eq], the [Drow] clause
     of the environment the run's instantiation returns.

   [sch_leQ] is [sch_leT] over [instQ].  The presence atoms of a body are
   syntactic, so comparing two schemes with convertible bodies asks that the
   second's presence atoms are among the first's ([sch_leQ_conv]).

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Goat.GoatConv.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferGen.
Require Import Goat.GoatCompleteInst.
Require Import Goat.GoatCompleteGen.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteEr.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteBound.
Require Import Goat.GoatCompleteMono.
Require Import Goat.GoatCompleteSchT.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the presence atoms of a body ---- *)

(* [a] is the presence of some entry of [T]. *)
Fixpoint qprT (a : atom) (T : typ) {struct T} : Prop :=
  match T with
  | typ_Arrow A B => qprT a A \/ qprT a B
  | typ_Record R => qprR a R
  | typ_Grp _ A => qprT a A
  | _ => False
  end
with qprR (a : atom) (R : row) {struct R} : Prop :=
  match R with
  | row_Ext _ T R' => qprT a T \/ qprR a R'
  | row_Maybe _ P T R' => P = typ_Var a \/ qprT a T \/ qprR a R'
  | _ => False
  end.

Lemma qpr_ftv : (forall T a, qprT a T -> a `in` ftv_typ T) /\ (forall R a, qprR a R -> a `in` ftv_row R).
Proof.
  apply typ_row_mutind; cbn [qprT qprR ftv_typ ftv_row]; try (intros; contradiction).
  - intros A IHA B IHB a [H|H]; apply AtomSetFacts.union_iff; [ left; exact (IHA a H) | right; exact (IHB a H) ].
  - intros R IH a H. exact (IH a H).
  - intros w A IH a H. exact (IH a H).
  - intros l T IHT R IHR a [H|H]; apply AtomSetFacts.union_iff; [ left; exact (IHT a H) | right; exact (IHR a H) ].
  - intros l P IHP T IHT R IHR a [H|[H|H]]; apply AtomSetFacts.union_iff.
    + left. subst P. simpl. fsetdec.
    + right. apply AtomSetFacts.union_iff. left. exact (IHT a H).
    + right. apply AtomSetFacts.union_iff. right. exact (IHR a H).
Qed.

(* A substitution that fixes [a], and sends no other atom of the type to a type
   that mentions [a], leaves no presence atom behind that the type lacked. *)
Lemma qpr_ap_mut : forall S a, sT S a = typ_Var a ->
  (forall T, pf T ->
     (forall x, x `in` ftv_typ T -> a `in` ftv_typ (sT S x) -> x = a) ->
     (forall q, q `in` frv_typ T -> a `notin` ftv_row (sR S q)) ->
     qprT a (apT S T) -> qprT a T) /\
  (forall R, prf R ->
     (forall x, x `in` ftv_row R -> a `in` ftv_typ (sT S x) -> x = a) ->
     (forall q, q `in` frv_row R -> a `notin` ftv_row (sR S q)) ->
     qprR a (apR S R) -> qprR a R).
Proof.
  intros S a Ha. apply typ_row_mutind; cbn [pf prf]; try (intros; contradiction);
    try (intros _ _ _ H; exact H).
  - intros A IHA B IHB [PA PB] Hx Hq H. rewrite apT_Arrow in H. cbn [qprT] in H |- *.
    destruct H as [H|H].
    + left. exact (IHA PA (fun x Hx' => Hx x ltac:(simpl; fsetdec)) (fun q Hq' => Hq q ltac:(simpl; fsetdec)) H).
    + right. exact (IHB PB (fun x Hx' => Hx x ltac:(simpl; fsetdec)) (fun q Hq' => Hq q ltac:(simpl; fsetdec)) H).
  - intros R IH HR Hx Hq H. change (apT S (typ_Record R)) with (typ_Record (apR S R)) in H.
    cbn [qprT] in H |- *. exact (IH HR Hx Hq H).
  - intros b _ Hx Hq H. rewrite apT_Var in H. exfalso.
    pose proof (proj1 qpr_ftv _ _ H) as Hin.
    assert (Hb : b = a) by (apply Hx; [ simpl; fsetdec | exact Hin ]). subst b. rewrite Ha in H. exact H.
  - intros w A IH [HA _] Hx Hq H.
    change (apT S (typ_Grp w A)) with (typ_Grp w (apT S A)) in H. cbn [qprT] in H |- *.
    exact (IH HA Hx Hq H).
  - intros r _ Hx Hq H. exfalso. change (apR S (row_Var r)) with (sR S r) in H.
    apply (Hq r ltac:(simpl; fsetdec)). exact (proj2 qpr_ftv _ _ H).
  - intros l T IHT R IHR [PT PR] Hx Hq H.
    change (apR S (row_Ext l T R)) with (row_Ext l (apT S T) (apR S R)) in H. cbn [qprR] in H |- *.
    destruct H as [H|H].
    + left. exact (IHT PT (fun x Hx' => Hx x ltac:(simpl; fsetdec)) (fun q Hq' => Hq q ltac:(simpl; fsetdec)) H).
    + right. exact (IHR PR (fun x Hx' => Hx x ltac:(simpl; fsetdec)) (fun q Hq' => Hq q ltac:(simpl; fsetdec)) H).
  - intros l P IHP T IHT R IHR [PP [PT PR]] Hx Hq H.
    change (apR S (row_Maybe l P T R)) with (row_Maybe l (apT S P) (apT S T) (apR S R)) in H.
    cbn [qprR] in H |- *. destruct H as [H|[H|H]].
    + left. destruct P; simpl in PP; try contradiction;
        try (unfold apT in H; simpl in H; discriminate H).
      assert (Hb : a0 = a) by (apply Hx; [ simpl; fsetdec | change (sT S a0 = typ_Var a) in H; rewrite H; simpl; fsetdec ]).
      rewrite Hb. reflexivity.
    + right. left. exact (IHT PT (fun x Hx' => Hx x ltac:(simpl; fsetdec)) (fun q Hq' => Hq q ltac:(simpl; fsetdec)) H).
    + right. right. exact (IHR PR (fun x Hx' => Hx x ltac:(simpl; fsetdec)) (fun q Hq' => Hq q ltac:(simpl; fsetdec)) H).
Qed.

(* A substitution that fixes [a] keeps it a presence atom. *)
Lemma qpr_ap_fwd : forall S a, sT S a = typ_Var a ->
  (forall T, qprT a T -> qprT a (apT S T)) /\ (forall R, qprR a R -> qprR a (apR S R)).
Proof.
  intros S a Ha. apply typ_row_mutind; cbn [qprT qprR]; try (intros; contradiction).
  - intros A IHA B IHB [H|H]; rewrite apT_Arrow; cbn [qprT]; [ left; apply IHA | right; apply IHB ]; exact H.
  - intros R IH H. change (apT S (typ_Record R)) with (typ_Record (apR S R)). cbn [qprT]. exact (IH H).
  - intros w A IH H. change (apT S (typ_Grp w A)) with (typ_Grp w (apT S A)). cbn [qprT]. exact (IH H).
  - intros l T IHT R IHR [H|H].
    + change (apR S (row_Ext l T R)) with (row_Ext l (apT S T) (apR S R)). cbn [qprR]. left. exact (IHT H).
    + change (apR S (row_Ext l T R)) with (row_Ext l (apT S T) (apR S R)). cbn [qprR]. right. exact (IHR H).
  - intros l P IHP T IHT R IHR [H|[H|H]];
      change (apR S (row_Maybe l P T R)) with (row_Maybe l (apT S P) (apT S T) (apR S R)); cbn [qprR].
    + left. subst P. exact Ha.
    + right. left. exact (IHT H).
    + right. right. exact (IHR H).
Qed.

(* ---- the image class ---- *)

Definition RowSorts (s : scheme) : Prop :=
  forall r, r `in` s_rq s -> rk_sort (s_rk s r) = k_Any \/ rk_sort (s_rk s r) = k_Eq.

Definition NNI (s : scheme) (st : tsub) : Prop :=
  forall a, a `in` s_tq s -> NQ (s_sk s a) -> forall R, st a <> typ_Record R.

Definition PresI (s : scheme) (st : tsub) : Prop :=
  forall a, a `in` s_tq s -> qprT a (s_body s) -> st a = typ_Unit \/ st a = typ_Bool.

(* The images of an instance of [s], as [instT] states them. *)
Definition instAt (Pt : typ -> Prop) (D : denv) (T : typ) (s : scheme) (st : tsub) (sr : rsub) : Prop :=
  (forall a, a `notin` s_tq s -> st a = typ_Var a) /\
  (forall r, r `notin` s_rq s -> sr r = row_Var r) /\
  T = ap_typ st sr (s_body s) /\
  (forall a, a `in` s_tq s -> sat D (s_sk s a) (st a)) /\
  (forall r, r `in` s_rq s -> rkok D (s_rk s r) (sr r)) /\
  lc_sub st sr /\
  (forall a, a `in` s_tq s -> Pt (st a)) /\
  (forall r, r `in` s_rq s -> EvR (sr r)).

Definition instQ (Pt : typ -> Prop) (D : denv) (T : typ) (s : scheme) : Prop :=
  exists st sr, instAt Pt D T s st sr /\ RowSorts s /\ NNI s st /\ PresI s st.

Lemma instQ_instT : forall Pt D T s, instQ Pt D T s -> instT Pt D T s.
Proof. intros Pt D T s (st & sr & H & _). exists st, sr. exact H. Qed.

Definition sch_leQ (Pt : typ -> Prop) (D : denv) (sd sa : scheme) : Prop :=
  ftv_schE sa [<=] ftv_schE sd /\ frv_schE sa [<=] frv_schE sd /\
  forall D' : denv, (forall a, a `in` ftv_schE sd -> D' a = D a) ->
    (forall r, r `in` frv_schE sd -> drk D' r = drk D r) ->
    forall T, instQ Pt D' T sd -> exists T', instQ Pt D' T' sa /\ teq T T'.

Lemma sch_leQ_refl : forall Pt D s, sch_leQ Pt D s s.
Proof.
  intros Pt D s. split; [ fsetdec | split; [ fsetdec | ] ].
  intros D' _ _ T H. exists T. split; [ exact H | apply teq_refl ].
Qed.

Lemma sch_leQ_trans : forall Pt D s1 s2 s3, sch_leQ Pt D s1 s2 -> sch_leQ Pt D s2 s3 -> sch_leQ Pt D s1 s3.
Proof.
  intros Pt D s1 s2 s3 (A1 & B1 & C1) (A2 & B2 & C2).
  split; [ fsetdec | split; [ fsetdec | ] ].
  intros D' Hd Hr T H. destruct (C1 D' Hd Hr T H) as (T2 & H2 & E2).
  destruct (C2 D' (fun a Ha => Hd a (A1 a Ha)) (fun r Hrr => Hr r (B1 r Hrr)) T2 H2) as (T3 & H3 & E3).
  exists T3. split; [ exact H3 | exact (teq_trans _ _ _ E2 E3) ].
Qed.

Lemma sch_leQ_inst : forall Pt D s s' T, sch_leQ Pt D s s' -> instQ Pt D T s ->
  exists T', instQ Pt D T' s' /\ teq T T'.
Proof. intros Pt D s s' T (_ & _ & H) Hi. exact (H D (fun _ _ => eq_refl) (fun _ _ => eq_refl) T Hi). Qed.

Lemma sch_leQ_env : forall Pt (D D2 : denv) s s',
  (forall a, a `in` ftv_schE s -> D2 a = D a) ->
  (forall r, r `in` frv_schE s -> drk D2 r = drk D r) ->
  sch_leQ Pt D s s' -> sch_leQ Pt D2 s s'.
Proof.
  intros Pt D D2 s s' Hv Hr (A & B & C). split; [ exact A | split; [ exact B | ] ].
  intros D' Hd Hdr T H. apply (C D'); [ | | exact H ].
  - intros a Ha. rewrite (Hd a Ha). apply Hv. exact Ha.
  - intros r Hrr. rewrite (Hdr r Hrr). apply Hr. exact Hrr.
Qed.

(* A scheme whose body is replaced by a convertible one, with the same
   quantifiers and presence atoms no more than before, is compared with the
   same instances. *)
Lemma sch_leQ_conv : forall Pt D sa sb,
  s_tq sb = s_tq sa -> s_rq sb = s_rq sa -> s_sk sb = s_sk sa -> s_rk sb = s_rk sa ->
  teq (s_body sa) (s_body sb) ->
  (forall a, a `in` s_tq sa -> qprT a (s_body sb) -> qprT a (s_body sa)) ->
  sch_leQ Pt D sa sb.
Proof.
  intros Pt D sa sb Htq Hrq Hsk Hrk Hb Hpr.
  destruct (proj1 er_inv _ _ Hb) as [E1 E2].
  assert (A : ftv_schE sb [=] ftv_schE sa) by (unfold ftv_schE; rewrite Htq, E1; reflexivity).
  assert (B : frv_schE sb [=] frv_schE sa) by (unfold frv_schE; rewrite Hrq, E2; reflexivity).
  split; [ rewrite A; reflexivity | split; [ rewrite B; reflexivity | ] ].
  intros D' _ _ T (st & sr & (t1 & t2 & t3 & t4 & t5 & t6 & t7 & t8) & Hrs & Hnn & Hpi).
  exists (ap_typ st sr (s_body sb)). split.
  - exists st, sr. unfold instAt. rewrite Htq, Hrq, Hsk, Hrk.
    refine (conj (conj t1 (conj t2 (conj eq_refl (conj t4 (conj t5 (conj t6 (conj t7 t8))))))) (conj _ (conj _ _))).
    + unfold RowSorts in *. rewrite Hrq, Hrk. exact Hrs.
    + unfold NNI in *. rewrite Htq, Hsk. exact Hnn.
    + intros a Ha Hq. rewrite Htq in Ha. exact (Hpi a Ha (Hpr a Ha Hq)).
  - rewrite t3. exact (teq_ap _ _ st sr Hb).
Qed.
