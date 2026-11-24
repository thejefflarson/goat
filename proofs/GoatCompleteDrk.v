(* Completeness of algorithm W, stage 7.7f: the unifier on record-free types
   leaves the row kinds alone (docs/design/phase7-proof-plan.md).

   A record-free run never makes a row variable, so the kinding environment it
   returns has the row kinds it was given.  [RA D] says every row variable of [D]
   has the trivial kind; [rkok] at that kind holds of every row, which is what
   lets the completeness induction drop its hypothesis that the derivation's
   substitution respects the row kinds ([rkres]) at the environment it
   currently reads.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatCompleteRf.
Require Import Stdlib.Lists.List.

Definition RA (D : denv) : Prop := forall r, drk D r = rk_any.

Lemma RA_d_any : RA d_any.
Proof. intros r. reflexivity. Qed.

Lemma RA_upd : forall D a k, RA D -> RA (upd D a k).
Proof. intros D a k H r. exact (H r). Qed.

Lemma RA_of_drk : forall D D', drk D' = drk D -> RA D -> RA D'.
Proof. intros D D' E H r. rewrite E. apply H. Qed.

Lemma rkres_RA : forall D DT sr, RA D -> rkres D DT sr.
Proof. intros D DT sr H r. rewrite (H r). apply rkok_any. Qed.

(* ---- record-free substitutions ---- *)

Definition rfS (s : sub) : Prop := forall x, rf (sT s x).

Lemma rfS_id : rfS sid.
Proof. intros x. cbn [sT sid idt]. exact I. Qed.

Lemma rfS_apT : forall s T, rfS s -> rf T -> rf (apT s T).
Proof. intros s T Hs HT. apply rf_ap; [ exact HT | intros x _; apply Hs ]. Qed.

Lemma rfS_comp : forall s2 s1, rfS s2 -> rfS s1 -> rfS (scomp s2 s1).
Proof. intros s2 s1 H2 H1 x. change (rf (apT s2 (sT s1 x))). apply rfS_apT; [ exact H2 | apply H1 ]. Qed.

Lemma rfS_sbT : forall a T, rf T -> rfS (sbT a T).
Proof.
  intros a T HT x. cbn [sT sbT]. destruct (Atom.eq_dec x a); [ exact HT | exact I ].
Qed.

Lemma push_sort_rfS : forall l D k n s D' n', push_sort D k l n = (s, D', n') -> rfS s.
Proof.
  induction l as [|b l IH]; intros D k n s D' n' H; cbn [push_sort] in H.
  - inversion H; subst. apply rfS_id.
  - destruct (finer_b (D b) k).
    + exact (IH _ _ _ _ _ _ H).
    + destruct (finer_b k (D b)).
      * destruct (push_sort (upd D (ea n) k) k l (S n)) as [[s1 D1] n1] eqn:E.
        inversion H; subst; clear H.
        apply rfS_comp; [ exact (IH _ _ _ _ _ _ E) | apply rfS_sbT; exact I ].
      * destruct (push_sort D k l n) as [[s1 D1] n1] eqn:E.
        inversion H; subst; clear H.
        apply rfS_comp; [ exact (IH _ _ _ _ _ _ E) | apply rfS_sbT; exact I ].
Qed.

Lemma bind_prop_rf : forall D a T n s D' n',
  bind_prop D a T n = Some (s, D', n') -> rf T -> drk D' = drk D /\ rfS s.
Proof.
  intros D a T n s D' n' H HT. unfold bind_prop in H.
  destruct (occT a T); [ discriminate | ].
  destruct (push_sort D (D a) (AtomSetImpl.elements (ftv_typ T)) n) as [[sp D1] n1] eqn:Ep.
  pose proof (proj1 (proj2 (proj2 (rf_facts T HT)))) as Hfrv.
  rewrite (elements_empty_of _ Hfrv) in H. cbn [push_sort_r] in H.
  destruct (occT a (apT sid (apT sp T))); [ discriminate | ].
  destruct (sat_b D1 (D1 a) (apT sid (apT sp T))); [ | discriminate ].
  inversion H; subst; clear H.
  split.
  - exact (push_sort_drk _ _ _ _ _ _ _ Ep).
  - apply rfS_comp; [ apply rfS_sbT | apply rfS_comp; [ apply rfS_id | exact (push_sort_rfS _ _ _ _ _ _ _ Ep) ] ].
    apply rfS_apT; [ apply rfS_id | apply rfS_apT; [ exact (push_sort_rfS _ _ _ _ _ _ _ Ep) | exact HT ] ].
Qed.

(* A record-free unification run changes no row kind and builds a record-free
   substitution. *)
Lemma unify_tD_rf_drk : forall f D T1 T2 n s D' n',
  unify_tD f D T1 T2 n = Some (s, D', n') -> rf T1 -> rf T2 ->
  drk D' = drk D /\ rfS s.
Proof.
  induction f as [|f IH]; intros D T1 T2 n s D' n' H R1 R2; [ discriminate | ].
  cbn [unify_tD] in H.
  destruct T1; simpl in R1; try contradiction;
    destruct T2; simpl in R2; try contradiction.
  all: try discriminate H.
  all: try (inversion H; subst; clear H; split; [ reflexivity | apply rfS_id ]; fail).
  all: try (first [ exact (bind_prop_rf _ _ _ _ _ _ _ H R2) | exact (bind_prop_rf _ _ _ _ _ _ _ H R1) ]; fail).
  - (* arrow, arrow *)
    destruct (unify_tD f D T1_1 T2_1 n) as [[[s1 D1] n1]|] eqn:E1; [ | discriminate ].
    destruct (unify_tD f D1 (apT s1 T1_2) (apT s1 T2_2) n1) as [[[s2 D2] n2]|] eqn:E2; [ | discriminate ].
    inversion H; subst; clear H.
    destruct R1 as [R11 R12]. destruct R2 as [R21 R22].
    destruct (IH _ _ _ _ _ _ _ E1 R11 R21) as [Dr1 S1].
    destruct (IH _ _ _ _ _ _ _ E2 (rfS_apT _ _ S1 R12) (rfS_apT _ _ S1 R22)) as [Dr2 S2].
    split; [ rewrite Dr2, Dr1; reflexivity | exact (rfS_comp _ _ S2 S1) ].
  - (* variable, variable *)
    destruct (Atom.eq_dec a a0) as [_|_].
    + inversion H; subst; clear H. split; [ reflexivity | apply rfS_id ].
    + destruct (finer_b (D a0) (D a)).
      * inversion H; subst; clear H. split; [ reflexivity | apply rfS_sbT; exact I ].
      * destruct (finer_b (D a) (D a0)).
        -- inversion H; subst; clear H. split; [ reflexivity | apply rfS_sbT; exact I ].
        -- inversion H; subst; clear H. split; [ reflexivity | ].
           unfold meet_float. apply rfS_comp; apply rfS_sbT; exact I.
Qed.
