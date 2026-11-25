(* Completeness of algorithm W, stage 7.8k: the fragment with absent entries
   (docs/design/phase7-proof-plan.md).

   [ps] (GoatCompleteRfRows.v) asks that every presence entry of a type be
   present under the substitution.  A scheme instance that sends a quantified
   presence to [Bool] is ordinary goat: a record-generic function applied to a
   record without the field.  [psA] accepts such an entry: its presence is sent
   to [Unit] or [Bool], and its field is in the fragment, whatever its image
   ([req_absf] makes the field of an absent entry free, so nothing relates the
   field's image to anything).  Every entry [ps] accepts is one [psA] accepts
   ([ps_psA]).  The unifier's completeness is still stated at [ps]: it reads
   the presence of an entry as [Unit].

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatInfer.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRfRows.

Fixpoint psA (S : sub) (T : typ) {struct T} : Prop :=
  match T with
  | typ_Arrow A B => psA S A /\ psA S B
  | typ_Record R => psAr S R
  | typ_Grp _ A => psA S A
  | _ => True
  end
with psAr (S : sub) (R : row) {struct R} : Prop :=
  match R with
  | row_Ext _ T R' => psA S T /\ psAr S R'
  | row_Maybe _ P T R' => (apT S P = typ_Unit \/ apT S P = typ_Bool) /\ psA S T /\ psAr S R'
  | _ => True
  end.

Lemma ps_psA : forall S,
  (forall T, ps S T -> psA S T) /\ (forall R, psr S R -> psAr S R).
Proof.
  intros S. apply typ_row_mutind; cbn [ps psr psA psAr]; try (intros; exact I).
  - intros A IHA B IHB [PA PB]. exact (conj (IHA PA) (IHB PB)).
  - intros R IH PR. exact (IH PR).
  - intros w A IH PA. exact (IH PA).
  - intros l T IHT R IHR [PT PR]. exact (conj (IHT PT) (IHR PR)).
  - intros l P IHP T IHT R IHR [PP [PT PR]]. exact (conj (or_introl PP) (conj (IHT PT) (IHR PR))).
Qed.

(* A presence of the fragment that is [Unit] or [Bool] under [S] is [Unit], [Bool] or a
   variable [S] sends there. *)
Lemma presA_shape : forall S P, pf P -> (apT S P = typ_Unit \/ apT S P = typ_Bool) ->
  P = typ_Unit \/ P = typ_Bool \/ exists v, P = typ_Var v /\ (sT S v = typ_Unit \/ sT S v = typ_Bool).
Proof.
  intros S P HP E. destruct P; simpl in HP; try contradiction;
    try (unfold apT in E; simpl in E; destruct E as [E|E]; discriminate E).
  - right. left. reflexivity.
  - left. reflexivity.
  - right. right. exists a. split; [ reflexivity | exact E ].
Qed.

(* Whether an entry is present or absent depends on the images of the variables the type mentions. *)
Lemma psA_agree : forall S S',
  (forall T, pf T -> (forall x, x `in` ftv_typ T -> sT S x = sT S' x) -> psA S T -> psA S' T) /\
  (forall R, prf R -> (forall x, x `in` ftv_row R -> sT S x = sT S' x) -> psAr S R -> psAr S' R).
Proof.
  intros S S'. apply typ_row_mutind; simpl; try (intros; exact I); try (intros; contradiction).
  - intros A IHA B IHB [HA HB] Hx [PA PB]. split;
      [ apply IHA; [ exact HA | intros x Hx'; apply Hx; fsetdec | exact PA ]
      | apply IHB; [ exact HB | intros x Hx'; apply Hx; fsetdec | exact PB ] ].
  - intros R IH HR Hx PR. exact (IH HR Hx PR).
  - intros w B IH [HB _] Hx PB. exact (IH HB Hx PB).
  - intros l T IHT R IHR [HT HR] Hx [PT PR]. split;
      [ apply IHT; [ exact HT | intros x Hx'; apply Hx; fsetdec | exact PT ]
      | apply IHR; [ exact HR | intros x Hx'; apply Hx; fsetdec | exact PR ] ].
  - intros l P IHP T IHT R IHR [HP [HT HR]] Hx [PP [PT PR]]. refine (conj _ (conj _ _)).
    + destruct (presA_shape S P HP PP) as [-> | [-> | [v [-> Hv]]]]; [ left; reflexivity | right; reflexivity | ].
      change (sT S' v = typ_Unit \/ sT S' v = typ_Bool). rewrite <- (Hx v ltac:(simpl; fsetdec)). exact Hv.
    + apply IHT; [ exact HT | intros x Hx'; apply Hx; fsetdec | exact PT ].
    + apply IHR; [ exact HR | intros x Hx'; apply Hx; fsetdec | exact PR ].
Qed.

(* The substitution carries an entry's presence along when [S'] after [s] is [S] on its atoms. *)
Lemma psA_pull : forall S S' s,
  (forall T, pf T -> psA S T ->
     (forall x, x `in` ftv_typ T -> teq (sT S x) (apT S' (sT s x)) /\ psA S' (sT s x)) ->
     (forall q, q `in` frv_typ T -> psAr S' (sR s q)) -> psA S' (apT s T)) /\
  (forall R, prf R -> psAr S R ->
     (forall x, x `in` ftv_row R -> teq (sT S x) (apT S' (sT s x)) /\ psA S' (sT s x)) ->
     (forall q, q `in` frv_row R -> psAr S' (sR s q)) -> psAr S' (apR s R)).
Proof.
  intros S S' s. unfold apT, apR. apply typ_row_mutind; simpl; try (intros; exact I);
    try (intros; contradiction).
  - intros A IHA B IHB [HA HB] [PA PB] Hx Hq. split;
      [ apply IHA; [ exact HA | exact PA | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]
      | apply IHB; [ exact HB | exact PB | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ] ].
  - intros R IH HR PR Hx Hq. exact (IH HR PR Hx Hq).
  - intros a _ _ Hx Hq. exact (proj2 (Hx a ltac:(fsetdec))).
  - intros w B IH [HB _] PB Hx Hq. exact (IH HB PB Hx Hq).
  - intros r _ _ Hx Hq. exact (Hq r ltac:(fsetdec)).
  - intros l T IHT R IHR [HT HR] [PT PR] Hx Hq. split;
      [ apply IHT; [ exact HT | exact PT | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]
      | apply IHR; [ exact HR | exact PR | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ] ].
  - intros l P IHP T IHT R IHR [HP [HT HR]] [PP [PT PR]] Hx Hq. refine (conj _ (conj _ _)).
    + destruct (presA_shape S P HP PP) as [-> | [-> | [v [-> Hv]]]];
        [ left; reflexivity | right; reflexivity | ].
      simpl. pose proof (proj1 (Hx v ltac:(simpl; fsetdec))) as Ht.
      destruct Hv as [Hv|Hv]; rewrite Hv in Ht;
        [ left; exact (teq_Unit_inv _ Ht) | right; exact (teq_Bool_inv _ Ht) ].
    + apply IHT; [ exact HT | exact PT | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ].
    + apply IHR; [ exact HR | exact PR | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ].
Qed.
