(* Completeness of algorithm W, stage 7.8m (partial): the hypotheses of statement A
   that exclude the unifiable pairs the unifier at [psA] cannot reach
   (docs/design/phase7-proof-plan.md, option B).

   The two occurrence pairs ([bind_row_blocks_absent_tail], [bind_prop_blocks_absent]):
   a variable that occurs in a type only behind entries [Sg] makes absent.  [OccT]
   says a variable that occurs outside a presence position also occurs under
   present entries only ([po]/[pos] of GoatCompleteOcc.v).  [ps_occ] shows it holds
   wherever every entry is present, so the proved unifier's inputs satisfy it.

   The field of an absent entry ([fld]'s first half): the field has the sort the
   enclosing row's kind asks of it ([AF]).

   Both are entry-local or occurrence-local, so they pull back along a unifier step
   as [ps_pull] does, given the same facts about the images the step gives the old
   atoms ([PkgB] adds them to [PkgA]): the images satisfy the predicate at the new
   substitution.  The pull-back lemmas are [occT_pull]/[occR_pull] and
   [af_pull]/[afr_pull]; [PkgB_comp] composes steps.

   The other two pairs ([side_blocks_absent], [field_blocks_absent]) are stated
   ([SideOk], [FieldAgree]) and shown vacuous where every entry is present
   ([ps_sideok], [ps_fieldagree]); they do not pull back along a step (the plan's
   account of stage 7.8m says why).

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatRowNf.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatSatTeq.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteOcc.
Require Import Goat.GoatCompleteRewrite.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompletePsA.
Require Import Goat.GoatCompletePsAUnify.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- an occurrence anywhere outside a presence position ---- *)

Fixpoint ao (vt vr : atom -> Prop) (T : typ) {struct T} : Prop :=
  match T with
  | typ_Var b => vt b
  | typ_Arrow A B => ao vt vr A \/ ao vt vr B
  | typ_Record R => aor vt vr R
  | typ_Grp _ A => ao vt vr A
  | _ => False
  end
with aor (vt vr : atom -> Prop) (R : row) {struct R} : Prop :=
  match R with
  | row_Var q => vr q
  | row_Ext _ T R' => ao vt vr T \/ aor vt vr R'
  | row_Maybe _ _ T R' => ao vt vr T \/ aor vt vr R'
  | row_Empty => False
  end.

Lemma ao_po_ps : forall S vt vr,
  (forall T, ps S T -> ao vt vr T -> po S vt vr T) /\
  (forall R, psr S R -> aor vt vr R -> por S vt vr R).
Proof.
  intros S vt vr. apply typ_row_mutind; simpl; try (intros; contradiction).
  - intros A IHA B IHB [PA PB] [H|H]; [ left; exact (IHA PA H) | right; exact (IHB PB H) ].
  - intros R IH PR H. exact (IH PR H).
  - intros a _ H. exact H.
  - intros w B IH PB H. exact (IH PB H).
  - intros r _ H. exact H.
  - intros l T IHT R IHR [PT PR] [H|H]; [ left; exact (IHT PT H) | right; exact (IHR PR H) ].
  - intros l P IHP T IHT R IHR [PP [PT PR]] [H|H].
    + left. split; [ rewrite PP; reflexivity | exact (IHT PT H) ].
    + right. exact (IHR PR H).
Qed.

(* ---- the predicate ---- *)

Definition OccT (S : sub) (T : typ) : Prop :=
  (forall a, ao (eq a) (fun _ => False) T -> po S (eq a) (fun _ => False) T) /\
  (forall q, ao (fun _ => False) (eq q) T -> po S (fun _ => False) (eq q) T).

Definition OccR (S : sub) (R : row) : Prop :=
  (forall a, aor (eq a) (fun _ => False) R -> por S (eq a) (fun _ => False) R) /\
  (forall q, aor (fun _ => False) (eq q) R -> por S (fun _ => False) (eq q) R) /\
  (forall q, aor (fun _ => False) (eq q) R -> (forall v, R <> row_Var v) ->
     pos S (fun _ => False) (eq q) R).

Lemma ps_occ : forall S,
  (forall T, ps S T -> OccT S T) /\ (forall R, psr S R -> OccR S R).
Proof.
  intros S. split.
  - intros T PT. split; intros x H; exact (proj1 (ao_po_ps S _ _) T PT H).
  - intros R PR. refine (conj _ (conj _ _));
      [ intros x H; exact (proj2 (ao_po_ps S _ _) R PR H)
      | intros x H; exact (proj2 (ao_po_ps S _ _) R PR H) | ].
    intros q H Hnv.
    destruct R as [ | v | l T R' | l P T R' ]; simpl in H.
    + contradiction.
    + exfalso. exact (Hnv v eq_refl).
    + simpl. destruct H as [H|H]; [ left | right ];
        [ exact (proj1 (ao_po_ps S _ _) T (proj1 PR) H) | exact (proj2 (ao_po_ps S _ _) R' (proj2 PR) H) ].
    + destruct PR as [PP [PT PR']]. simpl. left. split; [ rewrite PP; reflexivity | ].
      destruct H as [H|H]; [ left | right ];
        [ exact (proj1 (ao_po_ps S _ _) T PT H) | exact (proj2 (ao_po_ps S _ _) R' PR' H) ].
Qed.

(* ---- where an occurrence in a substituted type comes from ---- *)

Lemma ao_ap : forall s vt vr,
  (forall T, ao vt vr (apT s T) ->
     (exists x, ao (eq x) (fun _ => False) T /\ ao vt vr (sT s x)) \/
     (exists q, ao (fun _ => False) (eq q) T /\ aor vt vr (sR s q))) /\
  (forall R, aor vt vr (apR s R) ->
     (exists x, aor (eq x) (fun _ => False) R /\ ao vt vr (sT s x)) \/
     (exists q, aor (fun _ => False) (eq q) R /\ aor vt vr (sR s q))).
Proof.
  intros s vt vr. unfold apT, apR. apply typ_row_mutind; simpl; try (intros; contradiction).
  - intros A IHA B IHB [H|H].
    + destruct (IHA H) as [[x [H1 H2]]|[q [H1 H2]]]; [ left; exists x | right; exists q ];
        (split; [ left; exact H1 | exact H2 ]).
    + destruct (IHB H) as [[x [H1 H2]]|[q [H1 H2]]]; [ left; exists x | right; exists q ];
        (split; [ right; exact H1 | exact H2 ]).
  - intros R IH H. exact (IH H).
  - intros a H. left. exists a. split; [ reflexivity | exact H ].
  - intros w B IH H. exact (IH H).
  - intros r H. right. exists r. split; [ reflexivity | exact H ].
  - intros l T IHT R IHR [H|H].
    + destruct (IHT H) as [[x [H1 H2]]|[q [H1 H2]]]; [ left; exists x | right; exists q ];
        (split; [ left; exact H1 | exact H2 ]).
    + destruct (IHR H) as [[x [H1 H2]]|[q [H1 H2]]]; [ left; exists x | right; exists q ];
        (split; [ right; exact H1 | exact H2 ]).
  - intros l P IHP T IHT R IHR [H|H].
    + destruct (IHT H) as [[x [H1 H2]]|[q [H1 H2]]]; [ left; exists x | right; exists q ];
        (split; [ left; exact H1 | exact H2 ]).
    + destruct (IHR H) as [[x [H1 H2]]|[q [H1 H2]]]; [ left; exists x | right; exists q ];
        (split; [ right; exact H1 | exact H2 ]).
Qed.

Lemma ao_ftv : forall x,
  (forall T, ao (eq x) (fun _ => False) T -> x `in` ftv_typ T) /\
  (forall R, aor (eq x) (fun _ => False) R -> x `in` ftv_row R).
Proof.
  intros x. apply typ_row_mutind; simpl; try (intros; contradiction).
  - intros A IHA B IHB [H|H]; [ pose proof (IHA H) | pose proof (IHB H) ]; fsetdec.
  - intros R IH H. exact (IH H).
  - intros a H. subst. fsetdec.
  - intros w B IH H. exact (IH H).
  - intros l T IHT R IHR [H|H]; [ pose proof (IHT H) | pose proof (IHR H) ]; fsetdec.
  - intros l P IHP T IHT R IHR [H|H]; [ pose proof (IHT H) | pose proof (IHR H) ]; fsetdec.
Qed.

Lemma ao_frv : forall q,
  (forall T, ao (fun _ => False) (eq q) T -> q `in` frv_typ T) /\
  (forall R, aor (fun _ => False) (eq q) R -> q `in` frv_row R).
Proof.
  intros q. apply typ_row_mutind; simpl; try (intros; contradiction).
  - intros A IHA B IHB [H|H]; [ pose proof (IHA H) | pose proof (IHB H) ]; fsetdec.
  - intros R IH H. exact (IH H).
  - intros w B IH H. exact (IH H).
  - intros r H. subst. fsetdec.
  - intros l T IHT R IHR [H|H]; [ pose proof (IHT H) | pose proof (IHR H) ]; fsetdec.
  - intros l P IHP T IHT R IHR [H|H]; [ pose proof (IHT H) | pose proof (IHR H) ]; fsetdec.
Qed.

(* ---- pulling an occurrence back along a step ---- *)

(* An occurrence under present entries of [Sg] becomes one under present entries of
   [S2] in the substituted type, when the occurring atom's image holds the new
   occurrence and [S2] after [s] is [Sg] on the atoms. *)
Lemma po_pull : forall Sg S2 s vt vr vt' vr',
  (forall T, po Sg vt vr T ->
     (forall x, x `in` ftv_typ T -> teq (sT Sg x) (apT S2 (sT s x))) ->
     (forall q, q `in` frv_typ T -> req (sR Sg q) (apR S2 (sR s q))) ->
     (forall x, vt x -> po S2 vt' vr' (sT s x)) -> (forall q, vr q -> por S2 vt' vr' (sR s q)) ->
     po S2 vt' vr' (apT s T)) /\
  (forall R, por Sg vt vr R ->
     (forall x, x `in` ftv_row R -> teq (sT Sg x) (apT S2 (sT s x))) ->
     (forall q, q `in` frv_row R -> req (sR Sg q) (apR S2 (sR s q))) ->
     (forall x, vt x -> po S2 vt' vr' (sT s x)) -> (forall q, vr q -> por S2 vt' vr' (sR s q)) ->
     por S2 vt' vr' (apR s R)).
Proof.
  intros Sg S2 s vt vr vt' vr'. unfold apT, apR. apply typ_row_mutind; simpl; try (intros; contradiction).
  - intros A IHA B IHB [H|H] Hx Hq Hv Hr.
    + left. apply IHA; [ exact H | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec | exact Hv | exact Hr ].
    + right. apply IHB; [ exact H | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec | exact Hv | exact Hr ].
  - intros R IH H Hx Hq Hv Hr. exact (IH H Hx Hq Hv Hr).
  - intros a H Hx Hq Hv Hr. exact (Hv a H).
  - intros w B IH H Hx Hq Hv Hr. exact (IH H Hx Hq Hv Hr).
  - intros r H Hx Hq Hv Hr. exact (Hr r H).
  - intros l T IHT R IHR [H|H] Hx Hq Hv Hr.
    + left. apply IHT; [ exact H | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec | exact Hv | exact Hr ].
    + right. apply IHR; [ exact H | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec | exact Hv | exact Hr ].
  - intros l P IHP T IHT R IHR H Hx Hq Hv Hr.
    change (ap_typ (sT Sg) (sR Sg) P) with (apT Sg P) in H.
    change (ap_typ (sT S2) (sR S2) (ap_typ (sT s) (sR s) P)) with (apT S2 (apT s P)).
    destruct H as [[Ha H]|H].
    + left. split.
      * assert (Hf : teq (apT Sg P) (apT S2 (apT s P))).
        { apply ap_factor; [ intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]. }
        exact (eq_trans (eq_sym (teq_is_abs _ _ Hf)) Ha).
      * apply IHT; [ exact H | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec | exact Hv | exact Hr ].
    + right. apply IHR; [ exact H | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec | exact Hv | exact Hr ].
Qed.

Lemma pos_pull : forall Sg S2 s vt vr vt' vr' R, pos Sg vt vr R ->
  (forall x, x `in` ftv_row R -> teq (sT Sg x) (apT S2 (sT s x))) ->
  (forall q, q `in` frv_row R -> req (sR Sg q) (apR S2 (sR s q))) ->
  (forall x, vt x -> po S2 vt' vr' (sT s x)) -> (forall q, vr q -> por S2 vt' vr' (sR s q)) ->
  pos S2 vt' vr' (apR s R).
Proof.
  intros Sg S2 s vt vr vt' vr' R. destruct (po_pull Sg S2 s vt vr vt' vr') as [Pt Pr].
  induction R as [ | r | l T R IH | l P T R IH ]; intros H Hx Hq Hv Hr; simpl in H; try contradiction.
  - rewrite apR_Ext. cbn [pos].
    destruct H as [H|H].
    + left. apply Pt; [ exact H | intros x Hx'; apply Hx; simpl; fsetdec | intros q Hq'; apply Hq; simpl; fsetdec | exact Hv | exact Hr ].
    + right. apply Pr; [ exact H | intros x Hx'; apply Hx; simpl; fsetdec | intros q Hq'; apply Hq; simpl; fsetdec | exact Hv | exact Hr ].
  - rewrite apR_Maybe. cbn [pos]. change (ap_typ (sT S2) (sR S2) (ap_typ (sT s) (sR s) P)) with (apT S2 (apT s P)).
    change (ap_typ (sT s) (sR s) P) with (apT s P).
    assert (Hf : teq (apT Sg P) (apT S2 (apT s P))).
    { apply ap_factor; [ intros x Hx'; apply Hx; simpl; fsetdec | intros q Hq'; apply Hq; simpl; fsetdec ]. }
    change (ap_typ (sT Sg) (sR Sg) P) with (apT Sg P) in H.
    destruct H as [[Ha H]|H].
    + left. split; [ exact (eq_trans (eq_sym (teq_is_abs _ _ Hf)) Ha) | ].
      destruct H as [H|H].
      * left. apply Pt; [ exact H | intros x Hx'; apply Hx; simpl; fsetdec | intros q Hq'; apply Hq; simpl; fsetdec | exact Hv | exact Hr ].
      * right. apply Pr; [ exact H | intros x Hx'; apply Hx; simpl; fsetdec | intros q Hq'; apply Hq; simpl; fsetdec | exact Hv | exact Hr ].
    + right. apply IH; [ exact H | intros x Hx'; apply Hx; simpl; fsetdec | intros q Hq'; apply Hq; simpl; fsetdec | exact Hv | exact Hr ].
Qed.

(* With no row-variable target an occurrence through present entries is one through at
   least one present entry. *)
Lemma por_pos : forall S vt R, por S vt (fun _ => False) R -> pos S vt (fun _ => False) R.
Proof.
  intros S vt R. induction R as [ | r | l T R IH | l P T R IH ]; intros H; simpl in H; try contradiction.
  - exact H.
  - destruct H as [[Ha H]|H]; [ left; split; [ exact Ha | left; exact H ] | right; exact (IH H) ].
Qed.

Lemma occT_pull : forall Sg S2 s T, OccT Sg T ->
  (forall x, x `in` ftv_typ T -> teq (sT Sg x) (apT S2 (sT s x)) /\ OccT S2 (sT s x)) ->
  (forall q, q `in` frv_typ T -> req (sR Sg q) (apR S2 (sR s q)) /\ OccR S2 (sR s q)) ->
  OccT S2 (apT s T).
Proof.
  intros Sg S2 s T [O1 O2] Hx Hq.
  assert (Fx : forall x, x `in` ftv_typ T -> teq (sT Sg x) (apT S2 (sT s x))) by (intros x Hx'; exact (proj1 (Hx x Hx'))).
  assert (Fq : forall q, q `in` frv_typ T -> req (sR Sg q) (apR S2 (sR s q))) by (intros q Hq'; exact (proj1 (Hq q Hq'))).
  pose (Pt := fun vt vr vt' vr' => proj1 (po_pull Sg S2 s vt vr vt' vr')). split.
  - intros a Hao. destruct (proj1 (ao_ap s _ _) T Hao) as [[x [H1 H2]]|[q [H1 H2]]].
    + apply (Pt (eq x) (fun _ => False) (eq a) (fun _ => False) T (O1 x H1) Fx Fq).
      * intros y Hy. subst y. exact (proj1 (proj2 (Hx x (proj1 (ao_ftv x) T H1))) a H2).
      * intros q Hq'. contradiction.
    + apply (Pt (fun _ => False) (eq q) (eq a) (fun _ => False) T (O2 q H1) Fx Fq).
      * intros y Hy. contradiction.
      * intros q' Hq'. subst q'. exact (proj1 (proj2 (Hq q (proj1 (ao_frv q) T H1))) a H2).
  - intros a Hao. destruct (proj1 (ao_ap s _ _) T Hao) as [[x [H1 H2]]|[q [H1 H2]]].
    + apply (Pt (eq x) (fun _ => False) (fun _ => False) (eq a) T (O1 x H1) Fx Fq).
      * intros y Hy. subst y. exact (proj2 (proj2 (Hx x (proj1 (ao_ftv x) T H1))) a H2).
      * intros q Hq'. contradiction.
    + apply (Pt (fun _ => False) (eq q) (fun _ => False) (eq a) T (O2 q H1) Fx Fq).
      * intros y Hy. contradiction.
      * intros q' Hq'. subst q'. exact (proj1 (proj2 (proj2 (Hq q (proj1 (ao_frv q) T H1)))) a H2).
Qed.

Lemma occR_pull : forall Sg S2 s R, OccR Sg R ->
  (forall x, x `in` ftv_row R -> teq (sT Sg x) (apT S2 (sT s x)) /\ OccT S2 (sT s x)) ->
  (forall q, q `in` frv_row R -> req (sR Sg q) (apR S2 (sR s q)) /\ OccR S2 (sR s q)) ->
  OccR S2 (apR s R).
Proof.
  intros Sg S2 s R [O1 [O2 O3]] Hx Hq.
  assert (Fx : forall x, x `in` ftv_row R -> teq (sT Sg x) (apT S2 (sT s x))) by (intros x Hx'; exact (proj1 (Hx x Hx'))).
  assert (Fq : forall q, q `in` frv_row R -> req (sR Sg q) (apR S2 (sR s q))) by (intros q Hq'; exact (proj1 (Hq q Hq'))).
  pose (Pr := fun vt vr vt' vr' => proj2 (po_pull Sg S2 s vt vr vt' vr')).
  refine (conj _ (conj _ _)).
  - intros a Hao. destruct (proj2 (ao_ap s _ _) R Hao) as [[x [H1 H2]]|[q [H1 H2]]].
    + apply (Pr (eq x) (fun _ => False) (eq a) (fun _ => False) R (O1 x H1) Fx Fq).
      * intros y Hy. subst y. exact (proj1 (proj2 (Hx x (proj2 (ao_ftv x) R H1))) a H2).
      * intros q Hq'. contradiction.
    + apply (Pr (fun _ => False) (eq q) (eq a) (fun _ => False) R (O2 q H1) Fx Fq).
      * intros y Hy. contradiction.
      * intros q' Hq'. subst q'. exact (proj1 (proj2 (Hq q (proj2 (ao_frv q) R H1))) a H2).
  - intros a Hao. destruct (proj2 (ao_ap s _ _) R Hao) as [[x [H1 H2]]|[q [H1 H2]]].
    + apply (Pr (eq x) (fun _ => False) (fun _ => False) (eq a) R (O1 x H1) Fx Fq).
      * intros y Hy. subst y. exact (proj2 (proj2 (Hx x (proj2 (ao_ftv x) R H1))) a H2).
      * intros q Hq'. contradiction.
    + apply (Pr (fun _ => False) (eq q) (fun _ => False) (eq a) R (O2 q H1) Fx Fq).
      * intros y Hy. contradiction.
      * intros q' Hq'. subst q'. exact (proj1 (proj2 (proj2 (Hq q (proj2 (ao_frv q) R H1)))) a H2).
  - intros q' Hao Hnv. destruct R as [ | v | l T R' | l P T R' ].
    + contradiction.
    + exact (proj2 (proj2 (proj2 (Hq v ltac:(simpl; fsetdec)))) q' Hao Hnv).
    + destruct (proj2 (ao_ap s _ _) _ Hao) as [[x [H1 H2]]|[q [H1 H2]]].
      * refine (pos_pull Sg S2 s (eq x) (fun _ => False) (fun _ => False) (eq q') _ _ Fx Fq _ _).
        -- exact (por_pos _ _ _ (O1 x H1)).
        -- intros y Hy. subst y. exact (proj2 (proj2 (Hx x (proj2 (ao_ftv x) _ H1))) q' H2).
        -- intros q0 Hq0. contradiction.
      * refine (pos_pull Sg S2 s (fun _ => False) (eq q) (fun _ => False) (eq q') _ _ Fx Fq _ _).
        -- exact (O3 q H1 (fun v H => ltac:(discriminate H))).
        -- intros y Hy. contradiction.
        -- intros q0 Hq0. subst q0. exact (proj1 (proj2 (proj2 (Hq q (proj2 (ao_frv q) _ H1)))) q' H2).
    + destruct (proj2 (ao_ap s _ _) _ Hao) as [[x [H1 H2]]|[q [H1 H2]]].
      * refine (pos_pull Sg S2 s (eq x) (fun _ => False) (fun _ => False) (eq q') _ _ Fx Fq _ _).
        -- exact (por_pos _ _ _ (O1 x H1)).
        -- intros y Hy. subst y. exact (proj2 (proj2 (Hx x (proj2 (ao_ftv x) _ H1))) q' H2).
        -- intros q0 Hq0. contradiction.
      * refine (pos_pull Sg S2 s (fun _ => False) (eq q) (fun _ => False) (eq q') _ _ Fx Fq _ _).
        -- exact (O3 q H1 (fun v H => ltac:(discriminate H))).
        -- intros y Hy. contradiction.
        -- intros q0 Hq0. subst q0. exact (proj1 (proj2 (proj2 (Hq q (proj2 (ao_frv q) _ H1)))) q' H2).
Qed.

(* ---- the field of an absent entry ([fld]'s first half) ---- *)

(* An entry [S] makes absent keeps a field of the sort the row's kind asks, which is
   [Eq] at the most (the kinds in the fragment are [Any] and [Eq]). *)
Fixpoint af (DT : denv) (S : sub) (T : typ) {struct T} : Prop :=
  match T with
  | typ_Arrow A B => af DT S A /\ af DT S B
  | typ_Record R => afr DT S R
  | typ_Grp _ A => af DT S A
  | _ => True
  end
with afr (DT : denv) (S : sub) (R : row) {struct R} : Prop :=
  match R with
  | row_Ext _ T R' => af DT S T /\ afr DT S R'
  | row_Maybe _ P T R' => (is_abs (apT S P) = true -> sat DT k_Eq (apT S T)) /\ af DT S T /\ afr DT S R'
  | _ => True
  end.

Lemma ps_af : forall DT S,
  (forall T, ps S T -> af DT S T) /\ (forall R, psr S R -> afr DT S R).
Proof.
  intros DT S. apply typ_row_mutind; cbn [ps psr af afr]; try (intros; exact I).
  - intros A IHA B IHB [PA PB]. exact (conj (IHA PA) (IHB PB)).
  - intros R IH PR. exact (IH PR).
  - intros w A IH PA. exact (IH PA).
  - intros l T IHT R IHR [PT PR]. exact (conj (IHT PT) (IHR PR)).
  - intros l P IHP T IHT R IHR [PP [PT PR]]. refine (conj _ (conj (IHT PT) (IHR PR))).
    intros H. rewrite PP in H. discriminate H.
Qed.

(* With the first half, an image in the fragment with absent entries satisfies the
   field condition at [Any] and [Eq]. *)
Lemma psA_fld : forall DT S k, (k = k_Any \/ k = k_Eq) ->
  (forall T, pf T -> psA S T -> af DT S T -> fld DT S k T) /\
  (forall R, prf R -> psAr S R -> afr DT S R -> frld DT S k R).
Proof.
  intros DT S k Hk. apply typ_row_mutind; cbn [pf prf psA psAr af afr fld frld];
    try (intros; exact I); try (intros; contradiction).
  - intros A IHA B IHB [HA HB] [PA PB] [FA FB]. exact (conj (IHA HA PA FA) (IHB HB PB FB)).
  - intros R IH HR PR FR. exact (IH HR PR FR).
  - intros w A IH [HA _] PA FA. exact (IH HA PA FA).
  - intros l T IHT R IHR [HT HR] [PT PR] [FT FR]. exact (conj (IHT HT PT FT) (IHR HR PR FR)).
  - intros l P IHP T IHT R IHR [HP [HT HR]] [PP [PT PR]] [FP [FT FR]].
    assert (Hsat : sat DT k (apT S P)) by (destruct PP as [E|E]; rewrite E; exact Hk).
    assert (HfP : fld DT S k P).
    { destruct (presA_shape S P HP PP) as [-> | [-> | [v [-> _]]]]; exact I. }
    refine (conj _ (conj Hsat (conj HfP (conj (IHT HT PT FT) (IHR HR PR FR))))).
    intros E. assert (Ha : is_abs (apT S P) = true) by (rewrite E; reflexivity).
    pose proof (FP Ha) as Hs. destruct Hk as [-> | ->]; [ apply sat_any | exact Hs ].
Qed.

(* The first half pulls back along a step, as [ps_pull] does. *)
Lemma af_pull : forall DT Sg S2 s,
  (forall T, pf T -> af DT Sg T ->
     (forall x, x `in` ftv_typ T -> teq (sT Sg x) (apT S2 (sT s x)) /\ af DT S2 (sT s x)) ->
     (forall q, q `in` frv_typ T -> req (sR Sg q) (apR S2 (sR s q)) /\ afr DT S2 (sR s q)) ->
     af DT S2 (apT s T)) /\
  (forall R, prf R -> afr DT Sg R ->
     (forall x, x `in` ftv_row R -> teq (sT Sg x) (apT S2 (sT s x)) /\ af DT S2 (sT s x)) ->
     (forall q, q `in` frv_row R -> req (sR Sg q) (apR S2 (sR s q)) /\ afr DT S2 (sR s q)) ->
     afr DT S2 (apR s R)).
Proof.
  intros DT Sg S2 s. unfold apT, apR. apply typ_row_mutind; simpl; try (intros; exact I);
    try (intros; contradiction).
  - intros A IHA B IHB [HA HB] [FA FB] Hx Hq. split;
      [ apply IHA; [ exact HA | exact FA | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]
      | apply IHB; [ exact HB | exact FB | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ] ].
  - intros R IH HR FR Hx Hq. exact (IH HR FR Hx Hq).
  - intros a _ _ Hx Hq. exact (proj2 (Hx a ltac:(fsetdec))).
  - intros w B IH [HB _] FB Hx Hq. exact (IH HB FB Hx Hq).
  - intros r _ _ Hx Hq. exact (proj2 (Hq r ltac:(fsetdec))).
  - intros l T IHT R IHR [HT HR] [FT FR] Hx Hq. split;
      [ apply IHT; [ exact HT | exact FT | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]
      | apply IHR; [ exact HR | exact FR | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ] ].
  - intros l P IHP T IHT R IHR [HP [HT HR]] [FP [FT FR]] Hx Hq. refine (conj _ (conj _ _)).
    + change (ap_typ (sT S2) (sR S2) (ap_typ (sT s) (sR s) P)) with (apT S2 (apT s P)).
      change (ap_typ (sT S2) (sR S2) (ap_typ (sT s) (sR s) T)) with (apT S2 (apT s T)).
      assert (HfP : teq (apT Sg P) (apT S2 (apT s P))).
      { apply ap_factor; [ intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]. }
      assert (HfT : teq (apT Sg T) (apT S2 (apT s T))).
      { apply ap_factor; [ intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]. }
      intros Ha. apply (sat_teq DT k_Eq _ _ HfT). apply FP.
      exact (eq_trans (teq_is_abs _ _ HfP) Ha).
    + apply IHT; [ exact HT | exact FT | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ].
    + apply IHR; [ exact HR | exact FR | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ].
Qed.

(* ---- the package at option B ---- *)

(* [PkgA] and the facts the pull-backs read off the images: they satisfy the
   occurrence and field predicates at the new substitution. *)
Definition PkgB (DT : denv) (Sg : sub) (n : nat) (s : sub) (D' : denv) (n' : nat) (S2 : sub) : Prop :=
  PkgA DT Sg n s D' n' S2 /\
  (forall x, old n x -> OccT S2 (sT s x) /\ af DT S2 (sT s x)) /\
  (forall q, old n q -> OccR S2 (sR s q) /\ afr DT S2 (sR s q)).

Lemma PkgB_PkgA : forall DT Sg n s D' n' S2, PkgB DT Sg n s D' n' S2 -> PkgA DT Sg n s D' n' S2.
Proof. intros DT Sg n s D' n' S2 H. exact (proj1 H). Qed.

Lemma Pkg_PkgB : forall DT Sg n s D' n' S2, Pkg DT Sg n s D' n' S2 -> PkgB DT Sg n s D' n' S2.
Proof.
  intros DT Sg n s D' n' S2 H. refine (conj (Pkg_PkgA _ _ _ _ _ _ _ H) (conj _ _)).
  - intros x Hox. destruct H as (_ & _ & _ & _ & Hx & _ & _). destruct (Hx x Hox) as (_ & _ & C & _).
    exact (conj (proj1 (ps_occ S2) _ C) (proj1 (ps_af DT S2) _ C)).
  - intros q Hoq. destruct H as (_ & _ & _ & _ & _ & Hq & _). destruct (Hq q Hoq) as (_ & _ & C & _).
    exact (conj (proj2 (ps_occ S2) _ C) (proj2 (ps_af DT S2) _ C)).
Qed.

Lemma PkgB_id : forall DT Sg D n, DOk D n -> Dsrt D Sg -> KR D DT Sg -> PkgB DT Sg n sid D n Sg.
Proof.
  intros DT Sg D n Hd Ht Hk. refine (conj (PkgA_id DT Sg D n Hd Ht Hk) (conj _ _)).
  - intros x _. cbn [sid sT idt]. refine (conj (conj _ _) I); intros a H; exact H.
  - intros q _. cbn [sid sR idr]. refine (conj (conj _ (conj _ _)) I).
    + intros a H. exact H.
    + intros a H. exact H.
    + intros a H Hnv. exfalso. exact (Hnv q eq_refl).
Qed.

Lemma PkgB_comp : forall DT Sg n s1 D1 n1 S2 s2 D2 n2 S3,
  PkgB DT Sg n s1 D1 n1 S2 -> PkgB DT S2 n1 s2 D2 n2 S3 -> PkgB DT Sg n (scomp s2 s1) D2 n2 S3.
Proof.
  intros DT Sg n s1 D1 n1 S2 s2 D2 n2 S3 P1 P2.
  destruct P1 as (A1 & O1x & O1q). destruct P2 as (A2 & O2x & O2q).
  refine (conj (PkgA_comp _ _ _ _ _ _ _ _ _ _ _ A1 A2) (conj _ _)).
  - intros x Hox. destruct A1 as (_ & _ & _ & _ & Hx1 & _ & _). destruct A2 as (_ & _ & _ & _ & Hx2 & Hq2 & _).
    destruct (Hx1 x Hox) as (Hpf & [At1 At2] & _ & _).
    destruct (O1x x Hox) as [Oc Af].
    assert (Hxs : forall y, y `in` ftv_typ (sT s1 x) -> teq (sT S2 y) (apT S3 (sT s2 y)) /\ OccT S3 (sT s2 y)).
    { intros y Hy. pose proof (At1 y Hy) as Hoy. exact (conj (proj2 (proj2 (proj2 (Hx2 y Hoy)))) (proj1 (O2x y Hoy))). }
    assert (Hqs : forall q, q `in` frv_typ (sT s1 x) -> req (sR S2 q) (apR S3 (sR s2 q)) /\ OccR S3 (sR s2 q)).
    { intros q Hq'. pose proof (At2 q Hq') as Hoq. exact (conj (proj2 (proj2 (proj2 (Hq2 q Hoq)))) (proj1 (O2q q Hoq))). }
    change (OccT S3 (apT s2 (sT s1 x)) /\ af DT S3 (apT s2 (sT s1 x))). split.
    + exact (occT_pull S2 S3 s2 _ Oc Hxs Hqs).
    + refine (proj1 (af_pull DT S2 S3 s2) _ Hpf Af _ _).
      * intros y Hy. pose proof (At1 y Hy) as Hoy. exact (conj (proj2 (proj2 (proj2 (Hx2 y Hoy)))) (proj2 (O2x y Hoy))).
      * intros q Hq'. pose proof (At2 q Hq') as Hoq. exact (conj (proj2 (proj2 (proj2 (Hq2 q Hoq)))) (proj2 (O2q q Hoq))).
  - intros q Hoq. destruct A1 as (_ & _ & _ & _ & _ & Hq1 & _). destruct A2 as (_ & _ & _ & _ & Hx2 & Hq2 & _).
    destruct (Hq1 q Hoq) as (Hpf & [At1 At2] & _ & _).
    destruct (O1q q Hoq) as [Oc Af].
    change (OccR S3 (apR s2 (sR s1 q)) /\ afr DT S3 (apR s2 (sR s1 q))). split.
    + refine (occR_pull S2 S3 s2 _ Oc _ _).
      * intros y Hy. pose proof (At1 y Hy) as Hoy. exact (conj (proj2 (proj2 (proj2 (Hx2 y Hoy)))) (proj1 (O2x y Hoy))).
      * intros q' Hq'. pose proof (At2 q' Hq') as Hoq'. exact (conj (proj2 (proj2 (proj2 (Hq2 q' Hoq')))) (proj1 (O2q q' Hoq'))).
    + refine (proj2 (af_pull DT S2 S3 s2) _ Hpf Af _ _).
      * intros y Hy. pose proof (At1 y Hy) as Hoy. exact (conj (proj2 (proj2 (proj2 (Hx2 y Hoy)))) (proj2 (O2x y Hoy))).
      * intros q' Hq'. pose proof (At2 q' Hq') as Hoq'. exact (conj (proj2 (proj2 (proj2 (Hq2 q' Hoq')))) (proj2 (O2q q' Hoq'))).
Qed.

(* ---- the other two pairs, stated ---- *)

(* The first row's front entry is absent under [S], the second row has no entry of its
   label, and the two end in one row variable: the guard [side_av] refuses though [S]
   unifies them ([side_blocks_absent]). *)
Definition SideOk (S : sub) (R1 R2 : row) : Prop :=
  forall l P T R1', row_head R1 = Some (l, P, T, R1') -> apT S P = typ_Bool ->
    raw l R2 = nil -> forall r, row_tail R1 = Some r -> row_tail R2 = Some r -> False.

(* The front entry of the first row and the first entry of its label in the second are
   both absent under [S]: their fields agree under [S] ([field_blocks_absent]). *)
Definition FieldAgree (S : sub) (R1 R2 : row) : Prop :=
  forall l P T R1' Q U es, row_head R1 = Some (l, P, T, R1') -> raw l R2 = (Q, U) :: es ->
    apT S P = typ_Bool -> apT S Q = typ_Bool -> teq (apT S T) (apT S U).

Lemma ps_head_present : forall S R l P T R1', psr S R -> row_head R = Some (l, P, T, R1') ->
  apT S P = typ_Unit.
Proof.
  intros S R l P T R1' PR H. destruct R as [ | | l0 T0 R0 | l0 P0 T0 R0 ]; simpl in H;
    try discriminate; inversion H; subst.
  - reflexivity.
  - exact (proj1 PR).
Qed.

Lemma ps_sideok : forall S R1 R2, psr S R1 -> SideOk S R1 R2.
Proof.
  intros S R1 R2 PR l P T R1' Hh Hb. rewrite (ps_head_present S R1 l P T R1' PR Hh) in Hb. discriminate Hb.
Qed.

Lemma ps_fieldagree : forall S R1 R2, psr S R1 -> FieldAgree S R1 R2.
Proof.
  intros S R1 R2 PR l P T R1' Q U es Hh _ Hb. rewrite (ps_head_present S R1 l P T R1' PR Hh) in Hb. discriminate Hb.
Qed.
