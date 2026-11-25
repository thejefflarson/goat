(* Completeness of algorithm W, stage 7.8d: the record-free induction on the
   unifier's step over the fragment (docs/design/phase7-proof-plan.md).

   A record-free run moves no row variable ([unify_tD_rf_rr]), and a [pf] type
   whose image under a substitution is record-free is record-free and its
   variables are sent to record-free types ([rf_back]); the record-free
   induction ([unify_stepC], GoatCompleteCtxW.v) reads [unify_stepG]
   (GoatCompleteLive.v) through them.

   The fresh row variable and the fresh presence atom, which a step past records
   introduces, are the analogues of [SemG_fresh] at the end.

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
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteMono.
Require Import Goat.GoatCompleteDrk.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteLive.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- a record-free run moves no row variable ---- *)

Definition rrS (s : sub) : Prop := forall q, sR s q = row_Var q.

Lemma rrS_id : rrS sid.
Proof. intros q. reflexivity. Qed.

Lemma rrS_sbT : forall a T, rrS (sbT a T).
Proof. intros a T q. reflexivity. Qed.

Lemma rrS_comp : forall s2 s1, rrS s2 -> rrS s1 -> rrS (scomp s2 s1).
Proof.
  intros s2 s1 H2 H1 q. change (ap_row (sT s2) (sR s2) (sR s1 q) = row_Var q).
  rewrite (H1 q). exact (H2 q).
Qed.

Lemma push_sort_rrS : forall l D k n s D' n', push_sort D k l n = (s, D', n') -> rrS s.
Proof.
  induction l as [|b l IH]; intros D k n s D' n' H; cbn [push_sort] in H.
  - inversion H; subst. apply rrS_id.
  - destruct (finer_b (D b) k).
    + exact (IH _ _ _ _ _ _ H).
    + destruct (finer_b k (D b)).
      * destruct (push_sort (upd D (ea n) k) k l (S n)) as [[s1 D1] n1] eqn:E.
        inversion H; subst; clear H.
        apply rrS_comp; [ exact (IH _ _ _ _ _ _ E) | apply rrS_sbT ].
      * destruct (push_sort D k l n) as [[s1 D1] n1] eqn:E.
        inversion H; subst; clear H.
        apply rrS_comp; [ exact (IH _ _ _ _ _ _ E) | apply rrS_sbT ].
Qed.

Lemma bind_prop_rr : forall D a T n s D' n',
  bind_prop D a T n = Some (s, D', n') -> rf T -> rrS s.
Proof.
  intros D a T n s D' n' H HT. unfold bind_prop in H.
  destruct (bind_prop0 D a T n) as [[[s0 D0] n0]|] eqn:E0.
  - inversion H; subst; clear H. unfold bind_prop0 in E0.
    destruct (occT a T); [ discriminate | ].
    destruct (push_sort D (D a) (AtomSetImpl.elements (ftv_live T)) n) as [[sp D1] n1] eqn:Ep.
    rewrite (elements_empty_of _ (frv_live_rf T HT)) in E0. cbn [push_sort_r] in E0.
    destruct (occT a (apT sid (apT sp T))); [ discriminate | ].
    destruct (sat_b D1 (D1 a) (apT sid (apT sp T))); [ | discriminate ].
    inversion E0; subst; clear E0.
    apply rrS_comp; [ apply rrS_sbT | apply rrS_comp; [ apply rrS_id | exact (push_sort_rrS _ _ _ _ _ _ _ Ep) ] ].
  - destruct (occT a T); [ discriminate | ]. rewrite (forced_rf _ _ HT) in H. discriminate H.
Qed.

Lemma unify_tD_rf_rr : forall f D T1 T2 n s D' n',
  unify_tD f D T1 T2 n = Some (s, D', n') -> rf T1 -> rf T2 -> rrS s.
Proof.
  induction f as [|f IH]; intros D T1 T2 n s D' n' H R1 R2; [ discriminate | ].
  cbn [unify_tD] in H.
  destruct T1; simpl in R1; try contradiction;
    destruct T2; simpl in R2; try contradiction.
  all: try discriminate H.
  all: try (inversion H; subst; clear H; apply rrS_id; fail).
  all: try (first [ exact (bind_prop_rr _ _ _ _ _ _ _ H R2) | exact (bind_prop_rr _ _ _ _ _ _ _ H R1) ]; fail).
  - destruct (unify_tD f D T1_1 T2_1 n) as [[[s1 D1] n1]|] eqn:E1; [ | discriminate ].
    destruct (unify_tD f D1 (apT s1 T1_2) (apT s1 T2_2) n1) as [[[s2 D2] n2]|] eqn:E2; [ | discriminate ].
    inversion H; subst; clear H.
    destruct R1 as [R11 R12]. destruct R2 as [R21 R22].
    destruct (unify_tD_rf_drk _ _ _ _ _ _ _ _ E1 R11 R21) as [_ S1].
    apply rrS_comp; [ exact (IH _ _ _ _ _ _ _ E2 (rfS_apT _ _ S1 R12) (rfS_apT _ _ S1 R22))
                    | exact (IH _ _ _ _ _ _ _ E1 R11 R21) ].
  - destruct (Atom.eq_dec a a0) as [_|_].
    + inversion H; subst; clear H. apply rrS_id.
    + destruct (finer_b (D a0) (D a)).
      * inversion H; subst; clear H. apply rrS_sbT.
      * destruct (finer_b (D a) (D a0)).
        -- inversion H; subst; clear H. apply rrS_sbT.
        -- inversion H; subst; clear H. unfold meet_float. apply rrS_comp; apply rrS_sbT.
Qed.

(* ---- record-freeness pulled back through a substitution ---- *)

Lemma ps_rf : forall S T, rf T -> ps S T.
Proof.
  intros S T. induction T as [ | | | | | A IHA B IHB | R | a | i | B IHB | w B IHB ];
    simpl; intros H; try contradiction; try exact I.
  destruct H as [H1 H2]. split; [ exact (IHA H1) | exact (IHB H2) ].
Qed.

Lemma rf_back : forall S T, pf T -> rf (apT S T) ->
  rf T /\ forall y, y `in` ftv_typ T -> rf (sT S y).
Proof.
  intros S T. induction T as [ | | | | | A IHA B IHB | R | a | i | B IHB | w B IHB ]; intros HP Hr;
    try (split; [ exact I | intros y Hy; exfalso; simpl in Hy; revert Hy; fsetdec ]; fail);
    try (exfalso; unfold apT in Hr; simpl in Hr; contradiction; fail);
    try (simpl in HP; contradiction).
  - rewrite apT_Arrow in Hr. simpl in Hr, HP. destruct HP as [PA PB]. destruct Hr as [RA1 RB1].
    destruct (IHA PA RA1) as [R1 H1]. destruct (IHB PB RB1) as [R2 H2].
    split; [ exact (conj R1 R2) | ].
    intros y Hy. simpl in Hy. apply AtomSetFacts.union_iff in Hy.
    destruct Hy as [Hy|Hy]; [ exact (H1 y Hy) | exact (H2 y Hy) ].
  - rewrite apT_Var in Hr. split; [ exact I | ].
    intros y Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst y. exact Hr.
Qed.

Lemma teq_rf_eq : forall T T', rf T -> teq T T' -> T' = T.
Proof. intros T T' H Ht. exact (teqD_rf_eq d_any T T' H (teq_teqD d_any T T' Ht)). Qed.

(* ---- fresh row variables and presence atoms ---- *)

Definition rsupd (Sg : sub) (a : atom) (R : row) : sub :=
  Sub (sT Sg) (fun r => if Atom.eq_dec r a then R else sR Sg r).

Lemma rsupd_other : forall Sg a R q, q <> a -> sR (rsupd Sg a R) q = sR Sg q.
Proof. intros Sg a R q H. cbn [rsupd sR]. destruct (Atom.eq_dec q a); [ contradiction | reflexivity ]. Qed.

(* A fresh row variable of kind [K], sent to [R]: the identity step to the
   extended environment and substitution. *)
Lemma SemG_fresh_row : forall E F L LR DT D Sg n K R,
  DOk D n -> Drow D -> (rk_sort K = k_Any \/ rk_sort K = k_Eq) -> LOld n L -> LOld n LR ->
  LiveG E F L LR D DT Sg ->
  SemG E F L LR DT Sg n sid (rupd D (ea n) K) (S n) (rsupd Sg (ea n) R).
Proof.
  intros E F L LR DT D Sg n K R Hd Hrow HK Ho Hro HL.
  assert (Hnq : forall q, q `in` LR -> q <> ea n) by (intros q Hq E0; exact (Hro q Hq n (le_n n) E0)).
  assert (Hsub : limgT sid L LR [<=] L /\ limgR sid L LR [<=] LR).
  { split; intros y Hy.
    - apply limgT_in in Hy. destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)].
      + cbn [sT sid idt] in Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst y. exact Hx.
      + cbn [sR sid idr] in Hy. simpl in Hy. fsetdec.
    - apply limgR_in in Hy. destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)].
      + cbn [sT sid idt] in Hy. simpl in Hy. fsetdec.
      + cbn [sR sid idr] in Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst y. exact Hq. }
  pose proof (LiveG_env E F L LR D (rupd D (ea n) K) DT Sg HL
                (fun a _ => eq_refl) (fun q Hq => rupd_other D (ea n) K q (Hnq q Hq))) as HL1.
  pose proof (LiveG_agree E F L LR _ DT Sg (rsupd Sg (ea n) R) HL1
                (fun a _ => eq_refl) (fun q Hq => rsupd_other Sg (ea n) R q (Hnq q Hq))) as HL2.
  refine (conj (DOk_rupd D n K Hd) (conj (Drow_rupd D (ea n) K Hrow HK) (conj _ (conj _ (conj _ (conj _ (conj _ OkS_id))))))).
  - exact (LiveG_mono _ _ _ _ _ _ _ _ _ (proj1 Hsub) (proj2 Hsub) HL2).
  - refine (conj (Nat.le_succ_diag_r n) (conj _ _)).
    + intros x Hx. cbn [sT sid idt].
      exact (conj I (conj (atT_V DT (S n) x (old_le n (S n) x (Nat.le_succ_diag_r n) (Ho x Hx))) I)).
    + intros q Hq. cbn [sR sid idr].
      exact (conj I (conj (atR_V DT (S n) q (old_le n (S n) q (Nat.le_succ_diag_r n) (Hro q Hq))) I)).
  - intros x Hx. cbn [sid sT idt]. change (teq (sT Sg x) (sT Sg x)). apply teq_refl.
  - intros q Hq. cbn [sid sR idr]. change (req (sR Sg q) (sR (rsupd Sg (ea n) R) q)).
    rewrite (rsupd_other Sg (ea n) R q (Hnq q Hq)). apply req_refl.
  - intros E' F' HB.
    exact (BndL_agree E' F' _ _ Sg (rsupd Sg (ea n) R)
             (BndL_mono E' F' _ _ _ _ Sg (proj1 Hsub) (proj2 Hsub) HB)
             (fun a _ => eq_refl)
             (fun q Hq => rsupd_other Sg (ea n) R q (Hnq q (proj2 Hsub q Hq)))).
Qed.

(* A fresh presence atom, an atom of sort [Any] sent to [Unit], joins the live
   atoms and the presence atoms. *)
Lemma LiveG_fresh_pres : forall E F L LR (D D' DT : denv) Sg n,
  LOld n L -> LiveG E F L LR D DT Sg ->
  D' (ea n) = k_Any -> (forall a, a `in` L -> D' a = D a) -> (forall q, drk D' q = drk D q) ->
  LiveG E F (L `union` {{ ea n }}) LR D' DT (supd Sg (ea n) typ_Unit).
Proof.
  intros E F L LR D D' DT Sg n Ho HL Hk Hag Hdr.
  refine (LiveG_fresh E F L LR D D' DT Sg n k_Any typ_Unit Ho HL (sat_any _ _) _ _ _ Hk Hag Hdr).
  - intros b Hb. simpl in Hb. fsetdec.
  - intros q Hq. simpl in Hq. fsetdec.
  - intros [H|H]; discriminate H.
Qed.
