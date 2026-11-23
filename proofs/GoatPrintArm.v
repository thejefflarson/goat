(* The body of a match arm, past the bindings of the arm's slots: the printer
   writes it at the depth the bindings reach, and a term that reads the arm as
   [m] bindings and a body is scoped there. *)

From Stdlib Require Import String List Arith Lia.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatPrint.
Open Scope string_scope.
Open Scope list_scope.

Lemma slot_trees_cons2 : forall w c c2 cs,
  slot_trees w (c :: c2 :: cs) = slot_tree w c :: sym "," :: slot_trees w (c2 :: cs).
Proof. reflexivity. Qed.

Lemma scoped_slots_fields : forall fs G n i,
  scoped_slots G n i fs -> scoped_fields G n fs.
Proof.
  induction fs as [| l e rest IH | l e rest IH]; intros G n i H; simpl in H.
  - exact I.
  - destruct H as (_ & He & Hrest). exact (conj He (IH _ _ _ Hrest)).
  - destruct H.
Qed.

(* A tag's payload is the unit or a record of slots. *)
Lemma payload_scoped : forall G n a,
  match a with
  | e_unit => True
  | e_rec (fs_cons i x rest) => i = 0 /\ scoped G n x /\ scoped_slots G n 1 rest
  | _ => False
  end ->
  a = e_unit \/ scoped G n a.
Proof.
  intros G n a H. destruct a; try contradiction.
  - destruct fs as [| i x rest | i x rest]; try contradiction.
    destruct H as (_ & Hx & Hrest). right.
    exact (conj Hx (scoped_slots_fields _ _ _ _ Hrest)).
  - left. reflexivity.
Qed.

Lemma arm_body_block : forall m j b G Q,
  0 < m -> arm_chain m j b ->
  arm_body G Q m b = block G (Q + m) (arm_inner m b).
Proof.
  induction m as [| m IH]; intros j b G Q Hm Hc; [ lia | ].
  destruct b; try (cbn in Hc; contradiction).
  destruct b1; try (cbn in Hc; contradiction).
  destruct b1; try (cbn in Hc; contradiction).
  cbn in Hc. destruct Hc as (_ & _ & Hc).
  destruct m as [| m].
  - cbn [arm_body arm_inner]. replace (Q + 1) with (S Q) by lia. reflexivity.
  - cbn [arm_body arm_inner]. rewrite (IH (S j) b2 G (S Q) (ltac:(lia)) Hc).
    replace (S Q + S m) with (Q + S (S m)) by lia. reflexivity.
Qed.

Lemma lbls_body_inner : forall m j b G Q,
  0 < m -> arm_chain m j b ->
  lbls_body G Q m b = lbls G (Q + m) (arm_inner m b).
Proof.
  induction m as [| m IH]; intros j b G Q Hm Hc; [ lia | ].
  destruct b; try (cbn in Hc; contradiction).
  destruct b1; try (cbn in Hc; contradiction).
  destruct b1; try (cbn in Hc; contradiction).
  cbn in Hc. destruct Hc as (_ & _ & Hc).
  destruct m as [| m].
  - cbn [lbls_body arm_inner]. replace (Q + 1) with (S Q) by lia. reflexivity.
  - cbn [lbls_body arm_inner]. rewrite (IH (S j) b2 G (S Q) (ltac:(lia)) Hc).
    replace (S Q + S m) with (Q + S (S m)) by lia. reflexivity.
Qed.

Lemma tags_in_inner : forall m j b D,
  arm_chain m j b -> tags_in D b -> tags_in D (arm_inner m b).
Proof.
  induction m as [| m IH]; intros j b D Hc Ht.
  - exact Ht.
  - destruct b; try (cbn in Hc; contradiction).
    destruct b1; try (cbn in Hc; contradiction).
    destruct b1; try (cbn in Hc; contradiction).
    cbn in Hc. destruct Hc as (_ & _ & Hc).
    destruct Ht as [_ Ht]. cbn [arm_inner]. exact (IH _ _ _ Hc Ht).
Qed.

(* The labels of an arm's body, past the bindings of its slots. *)
Lemma lbls_arm_eq : forall G P w tg b,
  arm_chain (arm_arity w tg) 0 b ->
  (match arm_arity w tg with 0 => lbls G (S P) b | m => lbls_body G (S P) m b end)
  = lbls G (S P + arm_arity w tg) (arm_inner (arm_arity w tg) b).
Proof.
  intros G P w tg b Hc. destruct (arm_arity w tg) as [| m] eqn:E.
  - cbn [arm_inner]. rewrite Nat.add_0_r. reflexivity.
  - rewrite (lbls_body_inner (S m) 0 b G (S P) (ltac:(lia)) Hc). reflexivity.
Qed.

Lemma scoped_inner : forall m j b G k,
  arm_chain m j b -> scoped G k b -> scoped G (k + m) (arm_inner m b).
Proof.
  induction m as [| m IH]; intros j b G k Hc Hs.
  - cbn [arm_inner]. rewrite Nat.add_0_r. exact Hs.
  - destruct b; try (cbn in Hc; contradiction).
    destruct b1; try (cbn in Hc; contradiction).
    destruct b1; try (cbn in Hc; contradiction).
    cbn in Hc. destruct Hc as (_ & _ & Hc).
    destruct Hs as (_ & Hs & _).
    cbn [arm_inner]. replace (k + S m) with (S k + m) by lia.
    exact (IH _ _ _ _ Hc Hs).
Qed.
