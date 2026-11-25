(* Completeness of algorithm W, stage 7.8l (partial): the unifier's package at the
   fragment with absent entries (docs/design/phase7-proof-plan.md).

   [Pkg] (GoatCompleteRfRows.v) promises, of the images a unifier step gives the old
   atoms, that they are in the fragment with every entry present ([ps]).  [PkgA] is
   the same promise at [psA] (GoatCompletePsA.v): an entry's presence is [Unit] or
   [Bool].  Every [Pkg] is a [PkgA] ([Pkg_PkgA]), so the proved unifier already
   delivers [PkgA] at its [ps] inputs; the lemmas below are the ones the unifier at
   [psA] and its consumers need: composition, the step applied to a type, and the
   front entry of a row whose presence may be absent.

   The unifier at [psA] is not here.  Where an entry is absent, [nfR] drops it when its
   presence is the syntactic [Bool] ([na] excludes that), the occurs checks read a
   variable behind it as an occurrence, and the rewrite of the second row to present the
   front label meets a present entry of the same label when the front is absent; those
   are the cases the plan lists under what remains.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatCompleteRows.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteRewrite.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompletePsA.
Require Import Stdlib.micromega.Lia.

(* A type with no syntactic [Bool] presence is its own normal form at any environment. *)
Lemma na_nf : forall D,
  (forall T, na T = true -> nfT D T = T) /\ (forall R, nar R = true -> nfR D R = R).
Proof.
  intros D. apply typ_row_mutind; cbn [na nar nfT nfR]; try (intros; reflexivity).
  - intros A IHA B IHB H. apply andb_prop in H as [HA HB]. rewrite (IHA HA), (IHB HB). reflexivity.
  - intros R IH H. rewrite (IH H). reflexivity.
  - intros l T IHT R IHR H. apply andb_prop in H as [HT HR]. rewrite (IHT HT), (IHR HR). reflexivity.
  - intros l P IHP T IHT R IHR H.
    apply andb_prop in H as [H HR]. apply andb_prop in H as [H HT]. apply andb_prop in H as [Hn HP].
    apply Bool.negb_true_iff in Hn. rewrite (IHR HR), Hn, (IHP HP), (IHT HT). reflexivity.
Qed.

Lemma na_drop_abs : forall R, nar R = true -> drop_abs R = R.
Proof.
  intros R. induction R as [ | r | l T R IH | l P T R IH ]; intros H; try reflexivity.
  - cbn [nar] in H. apply andb_prop in H as [_ HR]. cbn [drop_abs]. rewrite (IH HR). reflexivity.
  - cbn [nar] in H. apply andb_prop in H as [H HR]. apply andb_prop in H as [H _].
    apply andb_prop in H as [Hn _]. apply Bool.negb_true_iff in Hn.
    cbn [drop_abs]. rewrite (IH HR), Hn. reflexivity.
Qed.

Section Sorted.

Variable DT : denv.

Definition PkgA (Sg : sub) (n : nat) (s : sub) (D' : denv) (n' : nat) (S2 : sub) : Prop :=
  n <= n' /\ DOk D' n' /\ Dsrt D' S2 /\ KR D' DT S2 /\
  (forall x, old n x -> pf (sT s x) /\ atT n' (sT s x) /\ psA S2 (sT s x) /\
     teq (sT Sg x) (apT S2 (sT s x))) /\
  (forall q, old n q -> prf (sR s q) /\ atR n' (sR s q) /\ psAr S2 (sR s q) /\
     req (sR Sg q) (apR S2 (sR s q))) /\
  Cov Sg S2.

Lemma Pkg_PkgA : forall Sg n s D' n' S2, Pkg DT Sg n s D' n' S2 -> PkgA Sg n s D' n' S2.
Proof.
  intros Sg n s D' n' S2 (Hl & Hd & Ht & Hk & Hx & Hq & Cv).
  refine (conj Hl (conj Hd (conj Ht (conj Hk (conj _ (conj _ Cv)))))).
  - intros x Hox. destruct (Hx x Hox) as (A & B & C & E). exact (conj A (conj B (conj (proj1 (ps_psA S2) _ C) E))).
  - intros q Hoq. destruct (Hq q Hoq) as (A & B & C & E). exact (conj A (conj B (conj (proj2 (ps_psA S2) _ C) E))).
Qed.

Lemma PkgA_id : forall Sg D n, DOk D n -> Dsrt D Sg -> KR D DT Sg -> PkgA Sg n sid D n Sg.
Proof.
  intros Sg D n Hd Ht Hk. exact (Pkg_PkgA _ _ _ _ _ _ (Pkg_id DT Sg D n Hd Ht Hk)).
Qed.

Lemma pkg_apA_T : forall Sg n s D' n' S2 T, PkgA Sg n s D' n' S2 -> pf T -> atT n T -> psA Sg T ->
  pf (apT s T) /\ atT n' (apT s T) /\ psA S2 (apT s T).
Proof.
  intros Sg n s D' n' S2 T (Hl & Hd & Ht & Hk & Hx & Hq & _) HT [A1 A2] PT.
  refine (conj _ (conj _ _)).
  - apply (proj1 (pf_ap s)); [ exact HT | intros x Hx'; exact (proj1 (Hx x (A1 x Hx')))
                              | intros q Hq'; exact (proj1 (Hq q (A2 q Hq'))) ].
  - apply atT_ap; [ intros x Hx'; exact (proj1 (proj2 (Hx x (A1 x Hx'))))
                  | intros q Hq'; exact (proj1 (proj2 (Hq q (A2 q Hq')))) ].
  - apply (proj1 (psA_pull Sg S2 s)); [ exact HT | exact PT
      | intros x Hx'; destruct (Hx x (A1 x Hx')) as (_ & _ & P & F); exact (conj F P)
      | intros q Hq'; exact (proj1 (proj2 (proj2 (Hq q (A2 q Hq'))))) ].
Qed.

Lemma pkg_apA_R : forall Sg n s D' n' S2 R, PkgA Sg n s D' n' S2 -> prf R -> atR n R -> psAr Sg R ->
  prf (apR s R) /\ atR n' (apR s R) /\ psAr S2 (apR s R).
Proof.
  intros Sg n s D' n' S2 R (Hl & Hd & Ht & Hk & Hx & Hq & _) HR [A1 A2] PR.
  refine (conj _ (conj _ _)).
  - apply (proj2 (pf_ap s)); [ exact HR | intros x Hx'; exact (proj1 (Hx x (A1 x Hx')))
                              | intros q Hq'; exact (proj1 (Hq q (A2 q Hq'))) ].
  - apply atR_ap; [ intros x Hx'; exact (proj1 (proj2 (Hx x (A1 x Hx'))))
                  | intros q Hq'; exact (proj1 (proj2 (Hq q (A2 q Hq')))) ].
  - apply (proj2 (psA_pull Sg S2 s)); [ exact HR | exact PR
      | intros x Hx'; destruct (Hx x (A1 x Hx')) as (_ & _ & P & F); exact (conj F P)
      | intros q Hq'; exact (proj1 (proj2 (proj2 (Hq q (A2 q Hq'))))) ].
Qed.

Lemma pkg_facA_T : forall Sg n s D' n' S2 T, PkgA Sg n s D' n' S2 -> atT n T ->
  teq (apT Sg T) (apT S2 (apT s T)).
Proof.
  intros Sg n s D' n' S2 T (Hl & Hd & Ht & Hk & Hx & Hq & _) [A1 A2].
  apply ap_factor; [ intros x Hx'; exact (proj2 (proj2 (proj2 (Hx x (A1 x Hx')))))
                   | intros q Hq'; exact (proj2 (proj2 (proj2 (Hq q (A2 q Hq'))))) ].
Qed.

Lemma pkg_facA_R : forall Sg n s D' n' S2 R, PkgA Sg n s D' n' S2 -> atR n R ->
  req (apR Sg R) (apR S2 (apR s R)).
Proof.
  intros Sg n s D' n' S2 R (Hl & Hd & Ht & Hk & Hx & Hq & _) [A1 A2].
  apply ap_factor_row; [ intros x Hx'; exact (proj2 (proj2 (proj2 (Hx x (A1 x Hx')))))
                       | intros q Hq'; exact (proj2 (proj2 (proj2 (Hq q (A2 q Hq'))))) ].
Qed.

Lemma PkgA_comp : forall Sg n s1 D1 n1 S2 s2 D2 n2 S3,
  PkgA Sg n s1 D1 n1 S2 -> PkgA S2 n1 s2 D2 n2 S3 -> PkgA Sg n (scomp s2 s1) D2 n2 S3.
Proof.
  intros Sg n s1 D1 n1 S2 s2 D2 n2 S3 P1 P2.
  destruct P1 as (Hl1 & Hd1 & Ht1 & Hk1 & Hx1 & Hq1 & Cv1).
  assert (P2' := P2). destruct P2 as (Hl2 & Hd2 & Ht2 & Hk2 & Hx2 & Hq2 & Cv2).
  refine (conj (Nat.le_trans _ _ _ Hl1 Hl2) (conj Hd2 (conj Ht2 (conj Hk2 (conj _ (conj _ (Cov_trans _ _ _ Cv1 Cv2))))))).
  - intros x Hx. destruct (Hx1 x Hx) as (Hpf & Hat & Hps & Hf).
    change (pf (apT s2 (sT s1 x)) /\ atT n2 (apT s2 (sT s1 x)) /\ psA S3 (apT s2 (sT s1 x)) /\
            teq (sT Sg x) (apT S3 (apT s2 (sT s1 x)))).
    destruct (pkg_apA_T S2 n1 s2 D2 n2 S3 _ P2' Hpf Hat Hps) as (A & B & C).
    refine (conj A (conj B (conj C _))).
    exact (teq_trans _ _ _ Hf (pkg_facA_T S2 n1 s2 D2 n2 S3 _ P2' Hat)).
  - intros q Hq. destruct (Hq1 q Hq) as (Hpf & Hat & Hps & Hf).
    change (prf (apR s2 (sR s1 q)) /\ atR n2 (apR s2 (sR s1 q)) /\ psAr S3 (apR s2 (sR s1 q)) /\
            req (sR Sg q) (apR S3 (apR s2 (sR s1 q)))).
    destruct (pkg_apA_R S2 n1 s2 D2 n2 S3 _ P2' Hpf Hat Hps) as (A & B & C).
    refine (conj A (conj B (conj C _))).
    exact (req_trans _ _ _ Hf (pkg_facA_R S2 n1 s2 D2 n2 S3 _ P2' Hat)).
Qed.

(* The first entry of a row of the fragment with absent entries: its presence is [Unit] or
   [Bool], the field is in the fragment, and the size is that of a present entry or of
   the rest alone. *)
Lemma row_frontA : forall Sg n R1 l P T R1', row_head R1 = Some (l, P, T, R1') ->
  prf R1 -> atR n R1 -> psAr Sg R1 ->
  (apT Sg P = typ_Unit \/ apT Sg P = typ_Bool) /\ pf P /\ pf T /\ prf R1' /\
  atT n P /\ atT n T /\ atR n R1' /\ psA Sg T /\ psAr Sg R1' /\
  (apT Sg P = typ_Unit -> rsz (apR Sg R1) = S (tsz (apT Sg T) + rsz (apR Sg R1'))) /\
  (apT Sg P = typ_Bool -> rsz (apR Sg R1) = rsz (apR Sg R1')).
Proof.
  intros Sg n R1 l P T R1' Hh HR AR PR. destruct R1 as [ | | l0 T0 R0 | l0 P0 T0 R0 ]; simpl in Hh;
    try discriminate; inversion Hh; subst.
  - destruct HR as [HT HR']. destruct (atR_ext_inv DT _ _ _ _ AR) as [AT AR']. destruct PR as [PT PR'].
    refine (conj (or_introl eq_refl) (conj I (conj HT (conj HR' (conj _ (conj AT (conj AR' (conj PT (conj PR' (conj _ _)))))))))).
    + apply atT_scalar; intros; simpl; fsetdec.
    + intros _. rewrite apR_Ext. reflexivity.
    + intros H. discriminate H.
  - destruct HR as [HP [HT HR']]. destruct (atR_maybe_inv DT _ _ _ _ _ AR) as [AP [AT AR']].
    destruct PR as [PP [PT PR']].
    refine (conj PP (conj HP (conj HT (conj HR' (conj AP (conj AT (conj AR' (conj PT (conj PR' (conj _ _)))))))))).
    + intros E. rewrite apR_Maybe. cbn [rsz]. change (ap_typ (sT Sg) (sR Sg) P) with (apT Sg P). rewrite E.
      reflexivity.
    + intros E. rewrite apR_Maybe. cbn [rsz]. change (ap_typ (sT Sg) (sR Sg) P) with (apT Sg P). rewrite E.
      reflexivity.
Qed.

End Sorted.
