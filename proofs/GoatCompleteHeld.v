(* Completeness of algorithm W, stage 7.8a: the discharge of held equations
   (docs/design/phase7-proof-plan.md).

   A spread holds the equation [p => y = T] (GoatHeld.v), and a generalizing
   [let], a recursive group and the end of a closed run discharge what they hold
   with [dis].  Completeness has to say that [dis] succeeds when the
   derivation's substitution solves the equations, and that it leaves the
   substitution factoring through its result, as the unifier does
   ([Pkg], GoatCompleteRfRows.v).

   [dis] skips an equation whose presence is already [Bool], and otherwise
   unifies the field variable with the value's type.  Each such unification is
   an instance of [unify_tD_complete_full], so the discharge is the unifier's
   completeness iterated down the list, with the equations that remain carried
   through each step ([apH]).  The hypothesis on an equation that [dis] unifies
   is [HEq]: its two types are in the fragment of 7.6 and the substitution makes
   them one type.  A substitution that solves an equation only because it makes
   the presence [Bool] while the two types differ is outside [HEq]: [dis] meets
   that case through [clash_d], and what [clash_d] needs is not proved here.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatSubst.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferW.
Require Import Goat.GoatHeld.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRfRows.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* What [dis] asks of an equation it unifies: both types are in the fragment
   over atoms below the supply with every entry present, and [Sg] makes them
   one type.  An equation whose presence is [Bool] is skipped and asks
   nothing. *)
Definition HEq (Sg : sub) (n : nat) (h : heq) : Prop :=
  pf (h_fld h) /\ pf (h_val h) /\ atT n (h_fld h) /\ atT n (h_val h) /\
  ps Sg (h_fld h) /\ ps Sg (h_val h) /\ teq (apT Sg (h_fld h)) (apT Sg (h_val h)).

Definition HOkC (Sg : sub) (n : nat) (H : list heq) : Prop :=
  Forall (fun h => is_bool (h_pres h) = false -> HEq Sg n h) H.

Lemma is_bool_ap : forall s P, is_bool (apT s P) = false -> is_bool P = false.
Proof.
  intros s P H. destruct P; try reflexivity.
  unfold apT in H. simpl in H. discriminate H.
Qed.

Section Held.

Variable DT : denv.

(* A step carries the equations that remain: each one that [dis] would still
   unify stays in the fragment, and [S2] makes its two types one type because
   [Sg] did. *)
Lemma HOkC_step : forall Sg n s D' n' S2 H,
  Pkg DT Sg n s D' n' S2 -> HOkC Sg n H -> HOkC S2 n' (apH s H).
Proof.
  intros Sg n s D' n' S2 H HP. induction H as [|h H IH]; intros Hk; simpl; [ constructor | ].
  inversion Hk as [|h' H' Hh Hrest]; subst. constructor.
  - intros Hb. cbn [apE h_pres] in Hb. pose proof (Hh (is_bool_ap s _ Hb)) as (F1 & V1 & A1 & AV & P1 & PV & Ht).
    destruct (pkg_ap_T DT Sg n s D' n' S2 _ HP F1 A1 P1) as (F2 & A2 & P2).
    destruct (pkg_ap_T DT Sg n s D' n' S2 _ HP V1 AV PV) as (V2 & AV2 & PV2).
    refine (conj F2 (conj V2 (conj A2 (conj AV2 (conj P2 (conj PV2 _)))))).
    cbn [apE h_fld h_val].
    eapply teq_trans; [ apply teq_sym; exact (pkg_fac_T DT Sg n s D' n' S2 _ HP A1) | ].
    eapply teq_trans; [ exact Ht | exact (pkg_fac_T DT Sg n s D' n' S2 _ HP AV) ].
  - exact (IH Hrest).
Qed.

(* The discharge of a list of equations is complete: from some unifier fuel on
   it succeeds, and the derivation's substitution factors through its result by
   an extension that respects the environment it returns.  [k] is the bound on
   the number of equations, as in [dis_top]. *)
Lemma dis_complete : forall k H Sg D n,
  length H <= k -> DOk D n -> Dsrt D Sg -> KR D DT Sg -> HOkC Sg n H ->
  exists s D' n' S2, Stable (fun f => dis k f D H n = Some (s, D', n')) /\ Pkg DT Sg n s D' n' S2.
Proof.
  induction k as [|k IH]; intros H Sg D n Hl Hd Ht Hk HO.
  - destruct H as [|h H]; [ | simpl in Hl; lia ].
    exists sid, D, n, Sg. split; [ | exact (Pkg_id DT Sg D n Hd Ht Hk) ].
    exists 0. intros f _. reflexivity.
  - destruct H as [|h H].
    + exists sid, D, n, Sg. split; [ | exact (Pkg_id DT Sg D n Hd Ht Hk) ].
      exists 0. intros f _. reflexivity.
    + inversion HO as [|h' H' Hh Hrest]; subst. simpl in Hl.
      destruct (is_bool (h_pres h)) eqn:Hb.
      * destruct (IH H Sg D n ltac:(lia) Hd Ht Hk Hrest) as (s & D' & n' & S2 & St & HP).
        exists s, D', n', S2. split; [ | exact HP ].
        eapply Stable_mono; [ | exact St ]. intros f Hf. cbn [dis]. rewrite Hb. exact Hf.
      * destruct (Hh eq_refl) as (F1 & V1 & A1 & AV & P1 & PV & Ht1).
        destruct (unify_tD_complete_full DT D Sg (h_fld h) (h_val h) n Hd Ht Hk F1 V1 A1 AV P1 PV Ht1)
          as (s1 & D1 & n1 & S2 & St1 & HP1).
        pose proof HP1 as HP1'. destruct HP1 as (Hl1 & Hd1 & Ht1' & Hk1 & _).
        destruct (IH (apH s1 H) S2 D1 n1 ltac:(unfold apH; rewrite length_map; lia) Hd1 Ht1' Hk1
                    (HOkC_step Sg n s1 D1 n1 S2 H HP1' Hrest)) as (s2 & D2 & n2 & S3 & St2 & HP2).
        exists (scomp s2 s1), D2, n2, S3. split.
        -- pose proof (Stable_and _ _ (Stable_mono _ _ (fun f H => proj1 H) St1) St2) as HSt.
           eapply Stable_mono; [ | exact HSt ]. intros f (E1 & E2). cbn [dis]. rewrite Hb, E1, E2. reflexivity.
        -- exact (Pkg_comp DT Sg n s1 D1 n1 S2 s2 D2 n2 S3 HP1' HP2).
Qed.

Lemma dis_top_complete : forall H Sg D n,
  DOk D n -> Dsrt D Sg -> KR D DT Sg -> HOkC Sg n H ->
  exists s D' n' S2, Stable (fun f => dis_top f D H n = Some (s, D', n')) /\ Pkg DT Sg n s D' n' S2.
Proof.
  intros H Sg D n Hd Ht Hk HO.
  exact (dis_complete (S (length H)) H Sg D n (Nat.le_succ_diag_r _) Hd Ht Hk HO).
Qed.

(* The closed entry point: a run of [infer] that holds equations, whose type and
   equations the derivation's substitution reads, is discharged, and the type
   the closed run returns is the run's type under the discharge. *)
Theorem infer_closed_elab_m_held : forall gm e s D T n e' H Sg,
  Stable (fun f => infer gm f d_any nil e 0 = Some (s, D, T, n, e', H)) ->
  DOk D n -> Dsrt D Sg -> KR D DT Sg -> HOkC Sg n H -> atT n T ->
  exists d D' n' S2,
    Stable (fun f => infer_closed_elab_m gm f e = Some (D', apT d T, e')) /\
    Pkg DT Sg n d D' n' S2 /\ teq (apT Sg T) (apT S2 (apT d T)).
Proof.
  intros gm e s D T n e' H Sg Hinf Hd Ht Hk HO HT.
  destruct (dis_top_complete H Sg D n Hd Ht Hk HO) as (d & D' & n' & S2 & St & HP).
  exists d, D', n', S2.
  refine (conj _ (conj HP (pkg_fac_T DT Sg n d D' n' S2 T HP HT))).
  pose proof (Stable_and _ _ Hinf St) as HSt.
  eapply Stable_mono; [ | exact HSt ]. intros f (E1 & E2).
  unfold infer_closed_elab_m. rewrite E1. rewrite E2. reflexivity.
Qed.

End Held.

(* The speculating run is the first thing [infer_closed_elab] tries, so a
   successful speculating run is the closed run's answer; a successful
   non-speculating run is an answer when the speculating one fails, and the
   closed run answers with one of the two otherwise. *)
Lemma infer_closed_elab_of_true : forall e r,
  Stable (fun f => infer_closed_elab_m true f e = Some r) ->
  Stable (fun f => infer_closed_elab f e = Some r).
Proof.
  intros e r St. eapply Stable_mono; [ | exact St ]. intros f Hf.
  unfold infer_closed_elab. rewrite Hf. reflexivity.
Qed.

Lemma infer_closed_elab_of_false : forall e r,
  Stable (fun f => infer_closed_elab_m false f e = Some r) ->
  Stable (fun f => exists r', infer_closed_elab f e = Some r').
Proof.
  intros e r St. eapply Stable_mono; [ | exact St ]. intros f Hf.
  unfold infer_closed_elab. destruct (infer_closed_elab_m true f e) as [r1|] eqn:E1.
  - exists r1. reflexivity.
  - exists r. exact Hf.
Qed.
