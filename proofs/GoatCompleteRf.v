(* Completeness of algorithm W, stage 7.6j: the unifier on record-free types
   with sorts and a supply (docs/design/phase7-proof-plan.md).

   This is the induction of statement A with the machinery in place and the row
   arms absent.  The types are base types, variables and arrows ([rf]); the
   substitution [Sg] respects the sorts ([KR D DT Sg]) and unifies the two types
   up to [teqD DT]; every atom of the types is below the supply ([old n]).  The
   unifier succeeds from some fuel on ([Stable]), and the extension [S2] of [Sg]
   to the fresh variables it makes respects the new environment, with [Sg]
   factoring through the result ([teqD DT]).  The composite of two steps
   threads [(D', n', S2)]: each call runs at the environment and supply the
   previous one left, with the substitution [S2] that call produced.  What a
   later call needs of an earlier result is [SI]: the images of the old
   variables are record-free, with every atom below the new supply, and no row
   variable is renamed.

   The occurs check and the field condition of [bind_prop] are not hypotheses
   here: with no entry in a type, every occurrence is present ([po]) and no
   field is absent ([fld]).  The measure is the size of the image
   ([tsz], [GoatCompleteRows.v]).

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteRows.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteBindRow.
Require Import Goat.GoatCompleteRewrite.
Require Import Goat.GoatCompleteOcc.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the fragment ---- *)

Fixpoint rf (T : typ) : Prop :=
  match T with
  | typ_Int | typ_Float | typ_Bool | typ_Unit | typ_String | typ_Var _ => True
  | typ_Arrow A B => rf A /\ rf B
  | _ => False
  end.

Lemma rf_facts : forall T, rf T ->
  pf T /\ lcb 0 T = true /\ (forall q, q `notin` frv_typ T) /\ (forall D S k, fld D S k T) /\
  (forall k, lcb k T = true).
Proof.
  induction T; simpl; intros H; try contradiction;
    try (repeat split; intros; first [ exact I | reflexivity | fsetdec ]; fail).
  destruct H as [HA HB]. destruct (IHT1 HA) as (A1 & A2 & A3 & A4 & A5).
  destruct (IHT2 HB) as (B1 & B2 & B3 & B4 & B5).
  refine (conj (conj A1 B1) (conj _ (conj _ (conj _ _)))).
  - rewrite (A5 0), (B5 0). reflexivity.
  - intros q Hq. apply AtomSetFacts.union_iff in Hq. destruct Hq as [Hq|Hq];
      [ exact (A3 q Hq) | exact (B3 q Hq) ].
  - intros D S k. exact (conj (A4 D S k) (B4 D S k)).
  - intros k. rewrite (A5 k), (B5 k). reflexivity.
Qed.

(* A step's effect on the old variables: the supply grows, the images are
   record-free over atoms below the new supply, and no row variable moves. *)
Definition SI (n n' : nat) (s : sub) : Prop :=
  n <= n' /\
  (forall x, old n x -> rf (sT s x) /\ forall y, y `in` ftv_typ (sT s x) -> old n' y) /\
  (forall q, old n q -> sR s q = row_Var q).

Lemma old_le : forall n n' x, n <= n' -> old n x -> old n' x.
Proof. intros n n' x Hl H m Hm. apply H. lia. Qed.

Lemma SI_id : forall n, SI n n sid.
Proof.
  intros n. split; [ lia | split; intros x Hx; [ | reflexivity ] ].
  split; [ exact I | ]. intros y Hy. cbn [sT sid idt] in Hy. simpl in Hy.
  apply AtomSetFacts.singleton_iff in Hy. subst. exact Hx.
Qed.

Lemma rf_ap : forall s T, rf T -> (forall x, x `in` ftv_typ T -> rf (sT s x)) -> rf (apT s T).
Proof.
  intros s T. induction T; simpl; intros H Hs; try contradiction; try exact I.
  - destruct H as [HA HB]. split;
      [ apply IHT1; [ exact HA | intros x Hx; apply Hs; apply AtomSetFacts.union_iff; left; exact Hx ]
      | apply IHT2; [ exact HB | intros x Hx; apply Hs; apply AtomSetFacts.union_iff; right; exact Hx ] ].
  - apply Hs. fsetdec.
Qed.

(* The atoms of an image of a record-free type are the atoms of the images of its variables. *)
Lemma ftv_ap_rf : forall s T y, rf T -> y `in` ftv_typ (apT s T) ->
  exists x, x `in` ftv_typ T /\ y `in` ftv_typ (sT s x).
Proof.
  intros s T y Hrf Hy. unfold apT in Hy. destruct (ftv_ap_typ _ _ _ _ Hy) as [H|[p [Hp _]]];
    [ exact H | exfalso; exact (proj1 (proj2 (proj2 (rf_facts T Hrf))) p Hp) ].
Qed.

Lemma SI_comp : forall n n1 n2 s1 s2, SI n n1 s1 -> SI n1 n2 s2 -> SI n n2 (scomp s2 s1).
Proof.
  intros n n1 n2 s1 s2 (Hl1 & H1 & R1) (Hl2 & H2 & R2). split; [ lia | split ].
  - intros x Hx. destruct (H1 x Hx) as [Hrf Hold].
    change (rf (apT s2 (sT s1 x)) /\ forall y, y `in` ftv_typ (apT s2 (sT s1 x)) -> old n2 y).
    split.
    + apply rf_ap; [ exact Hrf | intros z Hz; exact (proj1 (H2 z (Hold z Hz))) ].
    + intros y Hy. destruct (ftv_ap_rf s2 _ y Hrf Hy) as (z & Hz & Hyz).
      exact (proj2 (H2 z (Hold z Hz)) y Hyz).
  - intros q Hq. change (apR s2 (sR s1 q) = row_Var q). rewrite (R1 q Hq).
    exact (R2 q (old_le n n1 q Hl1 Hq)).
Qed.

