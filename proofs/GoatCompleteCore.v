(* Completeness of algorithm W, stage 7.7: the core constructs
   (docs/design/phase7-proof-plan.md).

   L3 for the constructs whose types are base types, variables and arrows:
   variables, constants, [program], a call, [if], the operators, a comparison
   and [float(e)].  A derivation [ctyping P D1 G1 e T1] of one of them, a context
   [G] of the algorithm that [G1] instantiates ([CI]), a set [L] of live atoms (the
   ones [G] and the pending types mention) and a substitution [Sg] that respects
   the sorts on [L] ([Live P L D D1 Sg]) give a run of [infer] that succeeds from
   some fuel on and a step [SemL] to the derivation's side: the extension [S2] of
   [Sg] respects the sorts the run ends with on the images of the live atoms, [Sg]
   factors through the run's substitution at [teqD D1] on [L], and the type the
   run returns is [teqD D1] to the derivation's under [S2].  Nothing is asked of
   [Sg] off the live atoms: each call to the unifier ([unify_stepL]) rebuilds a
   full substitution ([restr]) that agrees with [Sg] on [L] and sends the other
   atoms to [Int], which satisfies every sort, and then reads the result back on
   the live atoms.  The allowed set [P] of images rides along: the unifier's
   extension invents no type ([Img]), and [Int] is in [P], so [P] holds of every
   image of the live atoms the run returns.

   [let] of a value and [letrec] are not here: they generalize, so the algorithm's
   context holds schemes, and the comparison of a scheme with the derivation's
   ([gen_mono_let], GoatCompleteLet.v) needs the derivation's substitutions to
   keep clear of the quantified atoms.  Here every binding is monomorphic, so
   the context relation is [teqD] of the instance of each type.

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
Require Import Goat.GoatInferSound.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatClose.
Require Import Goat.GoatElab.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteSorts.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.


(* ---- extending a substitution at one atom ---- *)

Definition supd (Sg : sub) (a : atom) (U : typ) : sub :=
  Sub (fun b => if Atom.eq_dec b a then U else sT Sg b) (sR Sg).

Lemma supd_same : forall Sg a U, sT (supd Sg a U) a = U.
Proof. intros. cbn [supd sT]. destruct (Atom.eq_dec a a); [ reflexivity | contradiction ]. Qed.

Lemma supd_other : forall Sg a U b, b <> a -> sT (supd Sg a U) b = sT Sg b.
Proof. intros. cbn [supd sT]. destruct (Atom.eq_dec b a); [ contradiction | reflexivity ]. Qed.

Lemma apT_Arrow : forall s A B, apT s (typ_Arrow A B) = typ_Arrow (apT s A) (apT s B).
Proof. reflexivity. Qed.

Lemma apT_Var : forall s a, apT s (typ_Var a) = sT s a.
Proof. reflexivity. Qed.

Lemma apT_supd : forall Sg a U T, rf T -> a `notin` ftv_typ T -> apT (supd Sg a U) T = apT Sg T.
Proof.
  intros Sg a U T. induction T; simpl; intros H Hn; try contradiction; try reflexivity.
  - destruct H as [H1 H2]. rewrite !apT_Arrow.
    rewrite (IHT1 H1 ltac:(fsetdec)), (IHT2 H2 ltac:(fsetdec)). reflexivity.
  - rewrite !apT_Var. rewrite supd_other by fsetdec. reflexivity.
Qed.


(* ---- record-free types over atoms below a supply ---- *)

Definition TOk (n : nat) (T : typ) : Prop :=
  rf T /\ forall a, a `in` ftv_typ T -> old n a.

Lemma TOk_mono : forall n n' T, n <= n' -> TOk n T -> TOk n' T.
Proof. intros n n' T Hl [H1 H2]. split; [ exact H1 | intros a Ha; exact (old_le _ _ _ Hl (H2 a Ha)) ]. Qed.

Lemma TOk_var : forall n a, old n a -> TOk n (typ_Var a).
Proof.
  intros n a Ha. split; [ exact I | intros b Hb; simpl in Hb;
    apply AtomSetFacts.singleton_iff in Hb; subst; exact Ha ].
Qed.

Lemma TOk_arrow : forall n A B, TOk n A -> TOk n B -> TOk n (typ_Arrow A B).
Proof.
  intros n A B [A1 A2] [B1 B2]. split; [ exact (conj A1 B1) | ].
  intros a Ha. simpl in Ha. apply AtomSetFacts.union_iff in Ha.
  destruct Ha as [Ha|Ha]; [ exact (A2 a Ha) | exact (B2 a Ha) ].
Qed.

Lemma TOk_arrow_inv : forall n A B, TOk n (typ_Arrow A B) -> TOk n A /\ TOk n B.
Proof.
  intros n A B [[A1 B1] H]. split; split; try assumption;
    intros a Ha; apply H; simpl; apply AtomSetFacts.union_iff; [ left | right ]; exact Ha.
Qed.

Lemma TOk_scalar : forall n c,
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) -> TOk n c.
Proof.
  intros n c Hc. split.
  - destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; exact I.
  - intros a Ha. destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; simpl in Ha; fsetdec.
Qed.

Lemma TOk_ap : forall n n' s T, SI n n' s -> TOk n T -> TOk n' (apT s T).
Proof.
  intros n n' s T (Hl & Hx & _) [H1 H2]. split.
  - apply rf_ap; [ exact H1 | intros x Hxi; exact (proj1 (Hx x (H2 x Hxi))) ].
  - intros y Hy. destruct (ftv_ap_rf s T y H1 Hy) as (x & Hxi & Hyx).
    exact (proj2 (Hx x (H2 x Hxi)) y Hyx).
Qed.

(* ---- steps ---- *)

Lemma SI_weaken : forall n0 n1 n' s, n0 <= n1 -> SI n1 n' s -> SI n0 n' s.
Proof.
  intros n0 n1 n' s Hl (Hl1 & Hx & Hr). split; [ lia | split ].
  - intros x Hx0. exact (Hx x (old_le _ _ _ Hl Hx0)).
  - intros q Hq. exact (Hr q (old_le _ _ _ Hl Hq)).
Qed.

Lemma SI_id_le : forall n n', n <= n' -> SI n n' sid.
Proof.
  intros n n' Hl. split; [ exact Hl | split; intros x Hx; [ | reflexivity ] ].
  cbn [sT sid idt]. split; [ exact I | ].
  intros y Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst. exact (old_le _ _ _ Hl Hx).
Qed.


(* ---- the contexts ---- *)

(* Every binding of the algorithm's context is a record-free type over atoms
   below the supply. *)
Definition GOk (n : nat) (G : ctx) : Prop :=
  Forall (fun b => exists T, snd b = sch_mono T /\ TOk n T) G.

(* The derivation's context holds, at each name, the type that the algorithm's
   is under [Sg], up to [teqD]. *)
Definition CI (D1 : denv) (Sg : sub) (G1 G : ctx) : Prop :=
  Forall2 (fun b1 b => fst b1 = fst b /\
     exists T1 T, snd b1 = sch_mono T1 /\ snd b = sch_mono T /\ teqD D1 (apT Sg T) T1) G1 G.

Lemma GOk_nil : forall n, GOk n nil.
Proof. intros n. constructor. Qed.

Lemma GOk_cons : forall n x T G, TOk n T -> GOk n G -> GOk n ((x ~ sch_mono T) ++ G).
Proof. intros n x T G HT HG. constructor; [ exists T; split; [ reflexivity | exact HT ] | exact HG ]. Qed.

Lemma GOk_mono : forall n n' G, n <= n' -> GOk n G -> GOk n' G.
Proof.
  intros n n' G Hl H. induction H as [|b G [T [E HT]] _ IH]; constructor.
  - exists T. split; [ exact E | exact (TOk_mono _ _ _ Hl HT) ].
  - exact IH.
Qed.

Lemma apS_mono : forall s T, apS s (sch_mono T) = sch_mono (apT s T).
Proof. reflexivity. Qed.

Lemma GOk_apC : forall n n' s G, SI n n' s -> GOk n G -> GOk n' (apC s G).
Proof.
  intros n n' s G HI H. rewrite apC_map. induction H as [|[y sc] G [T [E HT]] _ IH]; simpl in *.
  - constructor.
  - constructor; [ | exact IH ].
    simpl in E. subst sc. exists (apT s T). split; [ reflexivity | exact (TOk_ap _ _ _ _ HI HT) ].
Qed.

Lemma CI_nil : forall D1 Sg, CI D1 Sg nil nil.
Proof. intros. constructor. Qed.

Lemma CI_cons : forall D1 Sg G1 G x T1 T,
  CI D1 Sg G1 G -> teqD D1 (apT Sg T) T1 ->
  CI D1 Sg ((x ~ sch_mono T1) ++ G1) ((x ~ sch_mono T) ++ G).
Proof.
  intros D1 Sg G1 G x T1 T H Ht. constructor; [ | exact H ].
  simpl. split; [ reflexivity | exists T1, T; repeat split; exact Ht ].
Qed.

Lemma CI_dom : forall D1 Sg G1 G, CI D1 Sg G1 G -> dom G1 [=] dom G.
Proof.
  intros D1 Sg G1 G H. induction H as [|[x s1] [y s] G1 G [Hk _] _ IH]; simpl in *; [ reflexivity | ].
  subst y. rewrite IH. reflexivity.
Qed.


Lemma CI_lookup : forall D1 Sg G1 G x sc1,
  CI D1 Sg G1 G -> uniq G1 -> binds x sc1 G1 ->
  exists T1 T, sc1 = sch_mono T1 /\ lookup x G = Some (sch_mono T) /\ teqD D1 (apT Sg T) T1.
Proof.
  intros D1 Sg G1 G x sc1 H. induction H as [|[y s1] [z sc] G1 G [Hk [T1 [T [E1 [E2 Ht]]]]] _ IH]; intros Hu Hb.
  - inversion Hb.
  - simpl in *. subst z. apply binds_cons_1 in Hb. destruct Hb as [[Hxy Hs]|Hb].
    + subst x sc1. exists T1, T. split; [ exact E1 | ]. split; [ | exact Ht ].
      cbn [lookup]. destruct (Atom.eq_dec y y); [ rewrite E2; reflexivity | contradiction ].
    + inversion Hu; subst.
      destruct (IH ltac:(assumption) Hb) as (T1' & T' & Ea & Eb & Hc). exists T1', T'.
      split; [ exact Ea | ]. split; [ | exact Hc ].
      cbn [lookup]. destruct (Atom.eq_dec x y) as [->|_]; [ | exact Eb ].
      exfalso. apply binds_In in Hb. contradiction.
Qed.




(* ---- live atoms ---- *)

(* The atoms a run still reads, those the context and the pending types mention,
   are the only ones whose sorts the derivation's substitution has to respect:
   the algorithm may generalize any other, and what the substitution does to a
   generalized atom is the derivation's own business.  [limg s L] is the atoms of
   the images of the atoms of [L]. *)
Definition limg (s : sub) (L : atoms) : atoms :=
  aset (flat_map (fun x => AtomSetImpl.elements (ftv_typ (sT s x))) (AtomSetImpl.elements L)).

Lemma limg_in : forall s L y,
  y `in` limg s L <-> exists x, x `in` L /\ y `in` ftv_typ (sT s x).
Proof.
  intros s L y. unfold limg. rewrite aset_in, in_flat_map. split.
  - intros (x & Hx & Hy). exists x. split; [ apply in_elts; exact Hx | apply in_elts; exact Hy ].
  - intros (x & Hx & Hy). exists x. split; [ apply in_elts; exact Hx | apply in_elts; exact Hy ].
Qed.

Definition LOld (n : nat) (L : atoms) : Prop := forall a, a `in` L -> old n a.

Lemma limg_mono : forall s L1 L2, L1 [<=] L2 -> limg s L1 [<=] limg s L2.
Proof.
  intros s L1 L2 H y Hy. apply limg_in in Hy. destruct Hy as (x & Hx & Hy).
  apply limg_in. exists x. split; [ apply H; exact Hx | exact Hy ].
Qed.

Lemma limg_sid : forall L, limg sid L [<=] L.
Proof.
  intros L y Hy. apply limg_in in Hy. destruct Hy as (x & Hx & Hy).
  cbn [sT sid idt] in Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst. exact Hx.
Qed.

Lemma limg_old : forall n n' s L, LOld n L -> SI n n' s -> LOld n' (limg s L).
Proof.
  intros n n' s L Ho (_ & HI & _) y Hy. apply limg_in in Hy. destruct Hy as (x & Hx & Hy).
  exact (proj2 (HI x (Ho x Hx)) y Hy).
Qed.

Lemma limg_scomp : forall n n1 s1 s2 L, LOld n L -> SI n n1 s1 ->
  limg (scomp s2 s1) L [<=] limg s2 (limg s1 L).
Proof.
  intros n n1 s1 s2 L Ho (_ & HI & _) y Hy. apply limg_in in Hy. destruct Hy as (x & Hx & Hy).
  change (y `in` ftv_typ (apT s2 (sT s1 x))) in Hy.
  destruct (ftv_ap_rf s2 _ y (proj1 (HI x (Ho x Hx))) Hy) as (z & Hz & Hyz).
  apply limg_in. exists z. split; [ apply limg_in; exists x; split; assumption | exact Hyz ].
Qed.

Lemma limg_chain : forall n n1 s1 s2 L Lm Lm', LOld n L -> SI n n1 s1 ->
  limg s1 L [<=] Lm -> limg s2 Lm [<=] Lm' -> limg (scomp s2 s1) L [<=] Lm'.
Proof.
  intros n n1 s1 s2 L Lm Lm' Ho HI H1 H2 y Hy.
  apply H2. apply (limg_mono s2 _ _ H1). exact (limg_scomp n n1 s1 s2 L Ho HI y Hy).
Qed.

Lemma limg_ap : forall s T L, rf T -> ftv_typ T [<=] L -> ftv_typ (apT s T) [<=] limg s L.
Proof.
  intros s T L Hrf Hs y Hy. destruct (ftv_ap_rf s T y Hrf Hy) as (x & Hx & Hyx).
  apply limg_in. exists x. split; [ apply Hs; exact Hx | exact Hyx ].
Qed.

(* What a run hands on: the old live atoms' images and the result type's atoms. *)
Definition lnext (s : sub) (L : atoms) (T : typ) : atoms := limg s L `union` ftv_typ T.

Lemma limg_lnext : forall s L T, limg s L [<=] lnext s L T.
Proof. intros s L T y Hy. unfold lnext. fsetdec. Qed.

Lemma ftv_lnext : forall s L T, ftv_typ T [<=] lnext s L T.
Proof. intros s L T y Hy. unfold lnext. fsetdec. Qed.

(* [Live P L D Dd S]: on the live atoms, [S] sends each atom to a type of the
   sort [D] gives it, read in [Dd], and to a type [P] allows.  [P] is the allowed
   set of images (evenness, in the use that needs it). *)
Definition Live (P : typ -> Prop) (L : atoms) (D Dd : denv) (S : sub) : Prop :=
  forall a, a `in` L -> sat Dd (D a) (sT S a) /\ P (sT S a).

Lemma Live_mono : forall P L1 L2 D Dd S, L1 [<=] L2 -> Live P L2 D Dd S -> Live P L1 D Dd S.
Proof. intros P L1 L2 D Dd S H HL a Ha. exact (HL a (H a Ha)). Qed.

Lemma Live_union : forall P L1 L2 D Dd S, Live P L1 D Dd S -> Live P L2 D Dd S ->
  Live P (L1 `union` L2) D Dd S.
Proof.
  intros P L1 L2 D Dd S H1 H2 a Ha. apply AtomSetFacts.union_iff in Ha.
  destruct Ha as [Ha|Ha]; [ exact (H1 a Ha) | exact (H2 a Ha) ].
Qed.

Lemma Live_empty : forall P D Dd S, Live P {} D Dd S.
Proof. intros P D Dd S a Ha. exfalso. revert Ha. fsetdec. Qed.

Lemma Live_scalar : forall P c (D Dd : denv) S,
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) ->
  Live P (ftv_typ c) D Dd S.
Proof.
  intros P c D Dd S Hc a Ha. exfalso.
  destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; simpl in Ha; revert Ha; fsetdec.
Qed.

Lemma Live_var : forall P a (D Dd : denv) S, sat Dd (D a) (sT S a) -> P (sT S a) ->
  Live P (ftv_typ (typ_Var a)) D Dd S.
Proof.
  intros P a D Dd S Hs HP b Hb. simpl in Hb. apply AtomSetFacts.singleton_iff in Hb. subst b.
  exact (conj Hs HP).
Qed.

(* The substitution may change at an atom the live set does not hold. *)
Lemma Live_fresh : forall P L (D D' DT : denv) Sg n k U, LOld n L -> Live P L D DT Sg -> sat DT k U -> P U ->
  D' (ea n) = k -> (forall a, a `in` L -> D' a = D a) ->
  Live P (L `union` {{ ea n }}) D' DT (supd Sg (ea n) U).
Proof.
  intros P L D D' DT Sg n k U Ho HL Hs HPU Hk Hag a Ha. apply AtomSetFacts.union_iff in Ha.
  destruct Ha as [Ha|Ha].
  - assert (Hne : a <> ea n) by (intro E; exact (Ho a Ha n (le_n n) E)).
    rewrite supd_other by exact Hne. rewrite (Hag a Ha). exact (HL a Ha).
  - apply AtomSetFacts.singleton_iff in Ha. subst a. rewrite supd_same, Hk. exact (conj Hs HPU).
Qed.

Lemma LOld_fresh : forall n L, LOld n L -> LOld (S n) (L `union` {{ ea n }}).
Proof.
  intros n L Ho a Ha. apply AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha].
  - exact (old_le _ _ _ (Nat.le_succ_diag_r n) (Ho a Ha)).
  - apply AtomSetFacts.singleton_iff in Ha. subst a. apply old_ea. lia.
Qed.

Lemma LOld_union : forall n L1 L2, LOld n L1 -> LOld n L2 -> LOld n (L1 `union` L2).
Proof.
  intros n L1 L2 H1 H2 a Ha. apply AtomSetFacts.union_iff in Ha.
  destruct Ha as [Ha|Ha]; [ exact (H1 a Ha) | exact (H2 a Ha) ].
Qed.

Lemma LOld_ftv : forall n T, TOk n T -> LOld n (ftv_typ T).
Proof. intros n T [_ H] a Ha. exact (H a Ha). Qed.

Lemma LOld_mono : forall n n' L, n <= n' -> LOld n L -> LOld n' L.
Proof. intros n n' L Hl H a Ha. exact (old_le _ _ _ Hl (H a Ha)). Qed.

Lemma LOld_sub : forall n L1 L2, L1 [<=] L2 -> LOld n L2 -> LOld n L1.
Proof. intros n L1 L2 H Ho a Ha. exact (Ho a (H a Ha)). Qed.

Lemma apT_agree : forall S S' T, rf T ->
  (forall a, a `in` ftv_typ T -> sT S a = sT S' a) -> apT S T = apT S' T.
Proof.
  intros S S' T. induction T; simpl; intros H Hn; try contradiction; try reflexivity.
  - destruct H as [H1 H2]. rewrite !apT_Arrow.
    rewrite (IHT1 H1 (fun a Ha => Hn a ltac:(fsetdec))), (IHT2 H2 (fun a Ha => Hn a ltac:(fsetdec))).
    reflexivity.
  - rewrite !apT_Var. apply Hn. fsetdec.
Qed.

(* ---- a step, on the live atoms ---- *)

(* [Sg] factors through the step [s] by [S2], on the live atoms [L]; [S2]
   respects the sorts the run ends with, and sends the images of the live atoms
   to types [P] allows. *)
Definition SemL (P : typ -> Prop) (L : atoms) (DT : denv) (Sg : sub) (n : nat) (s : sub)
  (D' : denv) (n' : nat) (S2 : sub) : Prop :=
  rkres D' DT (sR S2) /\ Live P (limg s L) D' DT S2 /\ DOk D' n' /\ SI n n' s /\
  (forall x, x `in` L -> teqD DT (sT Sg x) (apT S2 (sT s x))) /\
  (forall q, old n q -> sR S2 q = sR Sg q).

Lemma SemL_rk : forall P L DT Sg n s D' n' S2, SemL P L DT Sg n s D' n' S2 -> rkres D' DT (sR S2).
Proof. intros P L DT Sg n s D' n' S2 H. exact (proj1 H). Qed.

Lemma SemL_live : forall P L DT Sg n s D' n' S2, SemL P L DT Sg n s D' n' S2 ->
  Live P (limg s L) D' DT S2.
Proof. intros P L DT Sg n s D' n' S2 H. exact (proj1 (proj2 H)). Qed.

Lemma SemL_DOk : forall P L DT Sg n s D' n' S2, SemL P L DT Sg n s D' n' S2 -> DOk D' n'.
Proof. intros P L DT Sg n s D' n' S2 H. exact (proj1 (proj2 (proj2 H))). Qed.

Lemma SemL_SI : forall P L DT Sg n s D' n' S2, SemL P L DT Sg n s D' n' S2 -> SI n n' s.
Proof. intros P L DT Sg n s D' n' S2 H. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.

Lemma SemL_F : forall P L DT Sg n s D' n' S2, SemL P L DT Sg n s D' n' S2 ->
  forall x, x `in` L -> teqD DT (sT Sg x) (apT S2 (sT s x)).
Proof. intros P L DT Sg n s D' n' S2 H. exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))). Qed.

Arguments SemL_rk {P L DT Sg n s D' n' S2} H.
Arguments SemL_live {P L DT Sg n s D' n' S2} H.
Arguments SemL_DOk {P L DT Sg n s D' n' S2} H.
Arguments SemL_SI {P L DT Sg n s D' n' S2} H.
Arguments SemL_F {P L DT Sg n s D' n' S2} H x _.

(* A record-free type over live atoms factors through the step. *)
Lemma SemL_factor : forall P L DT Sg n s D' n' S2 T, SemL P L DT Sg n s D' n' S2 ->
  rf T -> ftv_typ T [<=] L -> teqD DT (apT Sg T) (apT S2 (apT s T)).
Proof.
  intros P L DT Sg n s D' n' S2 T H Hrf Hs. apply ap_factor_rf; [ exact Hrf | ].
  intros z Hz. exact (SemL_F H z (Hs z Hz)).
Qed.

Lemma SemL_live_ap : forall P L DT Sg n s D' n' S2 T, SemL P L DT Sg n s D' n' S2 ->
  rf T -> ftv_typ T [<=] L -> Live P (ftv_typ (apT s T)) D' DT S2.
Proof.
  intros P L DT Sg n s D' n' S2 T H Hrf Hs. eapply Live_mono; [ | exact (SemL_live H) ].
  exact (limg_ap s T L Hrf Hs).
Qed.

Lemma SemL_mono : forall P L1 L2 DT Sg n s D' n' S2, L1 [<=] L2 ->
  SemL P L2 DT Sg n s D' n' S2 -> SemL P L1 DT Sg n s D' n' S2.
Proof.
  intros P L1 L2 DT Sg n s D' n' S2 Hsub (R & V & Hd & HI & F & Q).
  refine (conj R (conj (Live_mono _ _ _ _ _ _ (limg_mono s _ _ Hsub) V) (conj Hd (conj HI (conj _ Q))))).
  intros x Hx. exact (F x (Hsub x Hx)).
Qed.

(* A step from a substitution that agrees with [Sg] on the live atoms, which lie
   below a smaller supply, is a step from [Sg]. *)
Lemma SemL_weaken : forall P L DT Sg Sg' n0 n1 s D' n' S2,
  n0 <= n1 -> LOld n0 L -> SemL P L DT Sg' n1 s D' n' S2 ->
  (forall x, x `in` L -> sT Sg' x = sT Sg x) -> (forall q, old n0 q -> sR Sg' q = sR Sg q) ->
  SemL P L DT Sg n0 s D' n' S2.
Proof.
  intros P L DT Sg Sg' n0 n1 s D' n' S2 Hl Ho (R & V & Hd & HI & F & Q) Ex Er.
  refine (conj R (conj V (conj Hd (conj (SI_weaken _ _ _ _ Hl HI) (conj _ _))))).
  - intros x Hx. rewrite <- (Ex x Hx). exact (F x Hx).
  - intros q Hq. rewrite <- (Er q Hq). exact (Q q (old_le _ _ _ Hl Hq)).
Qed.

Lemma SemL_id : forall P L DT Sg D n, rkres D DT (sR Sg) -> Live P L D DT Sg -> DOk D n ->
  SemL P L DT Sg n sid D n Sg.
Proof.
  intros P L DT Sg D n Hr HL Hd. refine (conj Hr (conj _ (conj Hd (conj (SI_id n) (conj _ _))))).
  - intros a Ha. exact (HL a (limg_sid L a Ha)).
  - intros x _. apply teqD_refl.
  - intros q _. reflexivity.
Qed.

(* A fresh variable of sort [k], sent to [U]. *)
Lemma SemL_fresh : forall P L DT D Sg n k U, rkres D DT (sR Sg) -> Live P L D DT Sg -> DOk D n ->
  LOld n L -> SemL P L DT Sg n sid (upd D (ea n) k) (S n) (supd Sg (ea n) U).
Proof.
  intros P L DT D Sg n k U Hr HL Hd Ho.
  refine (conj _ (conj _ (conj (DOk_upd D n k Hd) (conj (SI_id_le n (S n) (Nat.le_succ_diag_r n)) (conj _ _))))).
  - intros r. cbn [sR supd drk upd]. exact (Hr r).
  - intros a Ha. pose proof (limg_sid L a Ha) as Ha'.
    assert (Hne : a <> ea n) by (intro E; exact (Ho a Ha' n (le_n n) E)).
    rewrite upd_other by exact Hne. rewrite supd_other by exact Hne. exact (HL a Ha').
  - intros x Hx. cbn [sid sT idt]. change (teqD DT (sT Sg x) (sT (supd Sg (ea n) U) x)).
    rewrite supd_other by (intro E; exact (Ho x Hx n (le_n n) E)). apply teqD_refl.
  - intros q _. reflexivity.
Qed.

(* The step that ran past the fresh atom is a step from the old substitution. *)
Lemma SemL_unfresh : forall P Ln DT Sg n U s D' n' S2, LOld n Ln ->
  SemL P (Ln `union` {{ ea n }}) DT (supd Sg (ea n) U) (S n) s D' n' S2 ->
  SemL P Ln DT Sg n s D' n' S2.
Proof.
  intros P Ln DT Sg n U s D' n' S2 Ho H.
  refine (SemL_weaken P Ln DT Sg (supd Sg (ea n) U) n (S n) s D' n' S2 (Nat.le_succ_diag_r n) Ho
            (SemL_mono P Ln _ DT _ _ s D' n' S2 _ H) _ _).
  - intros x Hx. fsetdec.
  - intros x Hx. apply supd_other. intro E. exact (Ho x Hx n (le_n n) E).
  - intros q _. reflexivity.
Qed.

Lemma SemL_comp : forall P L Lm DT Sg n s D1 n1 S1 s' D2 n2 S2, LOld n L ->
  SemL P L DT Sg n s D1 n1 S1 -> limg s L [<=] Lm ->
  SemL P Lm DT S1 n1 s' D2 n2 S2 -> SemL P L DT Sg n (scomp s' s) D2 n2 S2.
Proof.
  intros P L Lm DT Sg n s D1 n1 S1 s' D2 n2 S2 Ho (R1 & V1 & Hd1 & I1 & F1 & Q1) Hsub
    (R2 & V2 & Hd2 & I2 & F2 & Q2).
  refine (conj R2 (conj _ (conj Hd2 (conj (SI_comp _ _ _ _ _ I1 I2) (conj _ _))))).
  - intros y Hy. apply V2. exact (limg_mono s' _ _ Hsub y (limg_scomp n n1 s s' L Ho I1 y Hy)).
  - intros x Hx. eapply teqD_trans; [ exact (F1 x Hx) | ].
    pose proof (proj1 (proj2 I1) x (Ho x Hx)) as [Hrf _].
    change (teqD DT (apT S1 (sT s x)) (apT S2 (apT s' (sT s x)))).
    apply ap_factor_rf; [ exact Hrf | intros z Hz; apply F2; apply Hsub; apply limg_in; exists x; split; assumption ].
  - intros q Hq. rewrite (Q2 q (old_le _ _ _ (proj1 I1) Hq)). exact (Q1 q Hq).
Qed.

(* ---- the contexts, on the live atoms ---- *)

(* The types of the context's bindings lie over live atoms. *)
Definition GLive (L : atoms) (G : ctx) : Prop :=
  Forall (fun b => exists T, snd b = sch_mono T /\ ftv_typ T [<=] L) G.

Lemma GLive_nil : forall L, GLive L nil.
Proof. intros L. constructor. Qed.

Lemma GLive_cons : forall L x T G, ftv_typ T [<=] L -> GLive L G -> GLive L ((x ~ sch_mono T) ++ G).
Proof. intros L x T G HT HG. constructor; [ exists T; split; [ reflexivity | exact HT ] | exact HG ]. Qed.

Lemma GLive_mono : forall L1 L2 G, L1 [<=] L2 -> GLive L1 G -> GLive L2 G.
Proof.
  intros L1 L2 G Hl H. induction H as [|b G [T [E HT]] _ IH]; constructor.
  - exists T. split; [ exact E | intros a Ha; apply Hl; apply HT; exact Ha ].
  - exact IH.
Qed.

Lemma GLive_lookup : forall L G x T, GLive L G -> lookup x G = Some (sch_mono T) -> ftv_typ T [<=] L.
Proof.
  intros L G x T H. induction H as [|[y sc] G [T0 [E HT]] _ IH]; intros Hl; [ discriminate Hl | ].
  cbn [lookup] in Hl. destruct (Atom.eq_dec x y) as [_|_].
  - cbn [snd] in E. subst sc. injection Hl as Hl. subst T0. exact HT.
  - exact (IH Hl).
Qed.

Lemma GLive_apC : forall n n' s L G, SI n n' s -> GOk n G -> GLive L G ->
  GLive (limg s L) (apC s G).
Proof.
  intros n n' s L G HI HG HL. rewrite apC_map. revert HG.
  induction HL as [|[y sc] G [T [E HT]] _ IH]; intros HG; simpl.
  - constructor.
  - inversion HG as [|b G' [T' [E' [HT' HTa]]] HG' Eb]; subst. simpl in *.
    rewrite E in E'. apply (f_equal s_body) in E'. cbn [sch_mono s_body] in E'. subst T'.
    constructor; [ | exact (IH HG') ].
    exists (apT s T). split; [ simpl; rewrite E; reflexivity | ].
    intros a Ha. destruct (ftv_ap_rf s T a HT' Ha) as (x & Hx & Hax).
    apply limg_in. exists x. split; [ apply HT; exact Hx | exact Hax ].
Qed.


(* The substitution may change off the live atoms. *)
Lemma CI_agree : forall D1 Sg Sg' G1 G L n, CI D1 Sg G1 G -> GOk n G -> GLive L G ->
  (forall a, a `in` L -> sT Sg' a = sT Sg a) -> CI D1 Sg' G1 G.
Proof.
  intros D1 Sg Sg' G1 G L n H. induction H as [|[x s1] [y s] G1 G [Hk [T1 [T [E1 [E2 Ht]]]]] _ IH]; intros HO HG Hag.
  - constructor.
  - inversion HG as [|b G' [T' [E' HTa]] HG' Eb]; subst.
    inversion HO as [|b2 G2 [T2 [E2' [HT2 HT2o]]] HO' Eb2]; subst. simpl in *. subst y.
    constructor; [ | exact (IH HO' HG' Hag) ].
    simpl. split; [ reflexivity | ]. exists T1, T. repeat split; try assumption.
    rewrite E' in E2. apply (f_equal s_body) in E2. cbn [sch_mono s_body] in E2. subst T'.
    rewrite E' in E2'. apply (f_equal s_body) in E2'. cbn [sch_mono s_body] in E2'. subst T2.
    rewrite (apT_agree Sg' Sg T HT2 (fun a Ha => Hag a (HTa a Ha))). exact Ht.
Qed.

Lemma CI_stepL : forall P L DT Sg n s D' n' S2 G1 G,
  SemL P L DT Sg n s D' n' S2 -> CI DT Sg G1 G -> GOk n G -> GLive L G ->
  CI DT S2 G1 (apC s G) /\ GOk n' (apC s G) /\ GLive (limg s L) (apC s G).
Proof.
  intros P L DT Sg n s D' n' S2 G1 G Hs HC HG HL.
  refine (conj _ (conj (GOk_apC _ _ _ _ (SemL_SI Hs) HG) (GLive_apC _ _ _ _ _ (SemL_SI Hs) HG HL))).
  rewrite apC_map. revert HG HL.
  induction HC as [|[x s1] [y sc] G1 G [Hk [T1 [T [E1 [E2 Ht]]]]] _ IH]; intros HG HL.
  - constructor.
  - inversion HG as [|b G' [T' [E' [HT' HTa]]] HG' Eb]; subst.
    inversion HL as [|b2 G2 [T2 [E2' HT2]] HL' Eb2]; subst. simpl in *. subst y.
    constructor; [ | exact (IH HG' HL') ].
    simpl. split; [ reflexivity | ].
    rewrite E2 in E'. apply (f_equal s_body) in E'. cbn [sch_mono s_body] in E'. subst T'.
    rewrite E2 in E2'. apply (f_equal s_body) in E2'. cbn [sch_mono s_body] in E2'. subst T2.
    exists T1, (apT s T). split; [ exact E1 | split; [ rewrite E2; reflexivity | ] ].
    eapply teqD_trans; [ | exact Ht ]. apply teqD_sym. exact (SemL_factor P L DT Sg n s D' n' S2 T Hs HT' HT2).
Qed.

Lemma next_facts : forall P Dd Gd Sg n L s D1 n1 S1 T G,
  LOld n L -> SemL P L Dd Sg n s D1 n1 S1 -> TOk n1 T -> Live P (ftv_typ T) D1 Dd S1 ->
  GOk n G -> GLive L G -> CI Dd Sg Gd G ->
  LOld n1 (lnext s L T) /\ Live P (lnext s L T) D1 Dd S1 /\ GOk n1 (apC s G) /\
  GLive (lnext s L T) (apC s G) /\ CI Dd S1 Gd (apC s G).
Proof.
  intros P Dd Gd Sg n L s D1 n1 S1 T G Ho Hs HT Lv HG HL HC.
  destruct (CI_stepL P L Dd Sg n s D1 n1 S1 Gd G Hs HC HG HL) as (HC1 & HG1 & HL1).
  refine (conj (LOld_union _ _ _ (limg_old _ _ _ _ Ho (SemL_SI Hs)) (LOld_ftv _ _ HT)) (conj _ (conj HG1 (conj _ HC1)))).
  - exact (Live_union _ _ _ _ _ _ (SemL_live Hs) Lv).
  - exact (GLive_mono _ _ _ (limg_lnext s L T) HL1).
Qed.

(* The full substitution the unifier's completeness needs: [Sg] on the live
   atoms, and [Int], which satisfies every sort, elsewhere. *)
Definition restr (L : atoms) (Sg : sub) : sub :=
  Sub (fun a => if AtomSetImpl.mem a L then sT Sg a else typ_Int) (sR Sg).

Lemma restr_in : forall L Sg a, a `in` L -> sT (restr L Sg) a = sT Sg a.
Proof. intros L Sg a Ha. cbn [restr sT]. rewrite (AtomSetImpl.mem_1 Ha). reflexivity. Qed.

Lemma unify_stepL : forall P DT D Sg L T1 T2 n,
  P typ_Int -> DOk D n -> LOld n L -> Live P L D DT Sg -> rkres D DT (sR Sg) ->
  rf T1 -> rf T2 -> ftv_typ T1 [<=] L -> ftv_typ T2 [<=] L ->
  teqD DT (apT Sg T1) (apT Sg T2) ->
  exists s D' n' S2,
    Stable (fun f => unify_coD f D T1 T2 n = Some (s, D', nil, n')) /\ SemL P L DT Sg n s D' n' S2.
Proof.
  intros P DT D Sg L T1 T2 n HPI Hd Ho HL Hr R1 R2 S1 S2 Heq.
  assert (HK : KR D DT (restr L Sg)).
  { split.
    - intros a. cbn [restr sT]. destruct (AtomSetImpl.mem a L) eqn:E.
      + exact (proj1 (HL a (AtomSetImpl.mem_2 E))).
      + simpl. exact I.
    - exact Hr. }
  assert (HPall : forall z, P (sT (restr L Sg) z)).
  { intros z. cbn [restr sT]. destruct (AtomSetImpl.mem z L) eqn:E.
    - exact (proj2 (HL z (AtomSetImpl.mem_2 E))).
    - exact HPI. }
  assert (Heq' : teqD DT (apT (restr L Sg) T1) (apT (restr L Sg) T2)).
  { rewrite (apT_agree (restr L Sg) Sg T1 R1 (fun a Ha => restr_in L Sg a (S1 a Ha))),
            (apT_agree (restr L Sg) Sg T2 R2 (fun a Ha => restr_in L Sg a (S2 a Ha))). exact Heq. }
  destruct (unify_tD_rf_complete_img DT D (restr L Sg) T1 T2 n Hd HK R1 R2
              (fun x Hx => Ho x (S1 x Hx)) (fun x Hx => Ho x (S2 x Hx)) Heq')
    as (s & D' & n' & S3 & [f0 Hf0] & (K & Hd' & HI & F & Q) & Im).
  exists s, D', n', S3. split.
  - exact (unify_coD_stable f0 D T1 T2 n s D' n' (Hf0 f0 (le_n f0))).
  - refine (conj (proj2 K) (conj _ (conj Hd' (conj HI (conj _ Q))))).
    + intros a _. exact (conj (proj1 K a) (Img_bound P _ S3 Im HPall a)).
    + intros x Hx. rewrite <- (restr_in L Sg x Hx). exact (F x (Ho x Hx)).
Qed.


(* ---- the derivations of the core constructs ---- *)

(* [typing] restricted to the constructs here, with a binder's premise at every
   name fresh for the context and the term (the algorithm opens a binder at the
   one name it chose), the context's bindings monomorphic, and the operators of
   one numeric sort.  The record division of [sig_quot_rec] is not here: the
   core's types hold no record, so the algorithm unifies the operands of [/] with
   [Float].  [P] is the allowed set: the types a rule invents (a parameter's, a
   numeral's, a call's result, an operator's) are in it. *)
Inductive ctyping (P : typ -> Prop) : denv -> ctx -> exp -> typ -> Prop :=
  | C_Var : forall Dd Gd x T,
      uniq Gd -> binds x (sch_mono T) Gd -> ctyping P Dd Gd (e_fvar_f x) T
  | C_Num : forall Dd Gd i T, uniq Gd -> sat Dd k_Literal T -> P T -> ctyping P Dd Gd (e_num i) T
  | C_Dec : forall Dd Gd d, uniq Gd -> ctyping P Dd Gd (e_dec d) typ_Float
  | C_True : forall Dd Gd, uniq Gd -> ctyping P Dd Gd e_true typ_Bool
  | C_False : forall Dd Gd, uniq Gd -> ctyping P Dd Gd e_false typ_Bool
  | C_Unit : forall Dd Gd, uniq Gd -> ctyping P Dd Gd e_unit typ_Unit
  | C_Str : forall Dd Gd q, uniq Gd -> ctyping P Dd Gd (e_str q) typ_String
  | C_Abs : forall Dd Gd e T1 T2, P T1 ->
      (forall x, x `notin` dom Gd `union` fv_exp e ->
         ctyping P Dd ((x ~ sch_mono T1) ++ Gd) (open_exp_wrt_exp e (e_fvar_f x)) T2) ->
      ctyping P Dd Gd (e_abs e) (typ_Arrow T1 T2)
  | C_App : forall Dd Gd e1 e2 T1 T2, P T2 ->
      ctyping P Dd Gd e1 (typ_Arrow T1 T2) -> ctyping P Dd Gd e2 T1 ->
      ctyping P Dd Gd (e_app e1 e2) T2
  | C_If : forall Dd Gd e1 e2 e3 T,
      ctyping P Dd Gd e1 typ_Bool -> ctyping P Dd Gd e2 T -> ctyping P Dd Gd e3 T ->
      ctyping P Dd Gd (e_ite e1 e2 e3) T
  | C_ToFloat : forall Dd Gd e A,
      ctyping P Dd Gd e A -> sat Dd k_Literal A -> P A -> ctyping P Dd Gd (e_tofloat e) typ_Float
  | C_Arith : forall Dd Gd e1 o e2 A,
      kind o <> k_cmp -> kind o <> k_quot -> sat Dd k_Numeric A -> P A ->
      ctyping P Dd Gd e1 A -> ctyping P Dd Gd e2 A -> ctyping P Dd Gd (e_bin e1 o e2) A
  | C_Quot : forall Dd Gd e1 e2,
      ctyping P Dd Gd e1 typ_Float -> ctyping P Dd Gd e2 typ_Float ->
      ctyping P Dd Gd (e_bin e1 bop_div e2) typ_Float
  | C_Cmp : forall Dd Gd e1 o e2 A,
      kind o = k_cmp -> sat Dd k_Eq A -> P A ->
      ctyping P Dd Gd e1 A -> ctyping P Dd Gd e2 A -> ctyping P Dd Gd (e_bin e1 o e2) typ_Bool
  | C_LetMono : forall Dd Gd e1 e2 T1 T2,
      is_gen_value e1 = false -> ctyping P Dd Gd e1 T1 ->
      (forall x, x `notin` dom Gd `union` fv_exp e2 ->
         ctyping P Dd ((x ~ sch_mono T1) ++ Gd) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
      ctyping P Dd Gd (e_let e1 e2) T2
  | C_Conv : forall Dd Gd e T T',
      ctyping P Dd Gd e T -> teqD Dd T T' -> ctyping P Dd Gd e T'.

Theorem ctyping_typing : forall P D G e T, ctyping P D G e T -> typing D G e T.
Proof.
  intros P D G e T H. induction H.
  - eapply T_Var; [ exact H | exact H0 | apply inst_mono_self ].
  - apply T_Num; assumption.
  - apply T_Dec; assumption.
  - apply T_True; assumption.
  - apply T_False; assumption.
  - apply T_Unit; assumption.
  - apply T_Str; assumption.
  - apply T_Abs with (L := dom Gd `union` fv_exp e). exact H1.
  - eapply T_App; eassumption.
  - apply T_If; assumption.
  - eapply T_ToFloat; eassumption.
  - eapply T_Bin; [ exact IHctyping1 | exact IHctyping2 | ].
    destruct (kind o) eqn:Ek; try contradiction;
      [ apply sig_ring | apply sig_whole ]; assumption.
  - apply (T_Bin Dd Gd e1 bop_div e2 typ_Float typ_Float typ_Float); [ assumption | assumption | apply sig_quot ].
  - eapply T_Bin; [ exact IHctyping1 | exact IHctyping2 | ].
    apply sig_cmp; assumption.
  - apply T_LetMono with (L := dom Gd `union` fv_exp e2) (T1 := T1); [ exact IHctyping | exact H2 ].
  - eapply T_ConvD; eassumption.
Qed.

(* ---- what each case of the induction uses ---- *)

Lemma GOk_lookup : forall n G x T, GOk n G -> lookup x G = Some (sch_mono T) -> TOk n T.
Proof.
  intros n G x T H. induction H as [|[y sc] G [T0 [E HT]] _ IH]; intros Hl; [ discriminate Hl | ].
  cbn [lookup] in Hl. destruct (Atom.eq_dec x y) as [_|_].
  - cbn [snd] in E. subst sc. injection Hl as Hl. subst T0. exact HT.
  - exact (IH Hl).
Qed.

Lemma elements_none : forall V : atoms, (forall q, q `notin` V) -> AtomSetImpl.elements V = nil.
Proof. exact elements_empty_of. Qed.

Lemma instantiate_mono : forall D T n, instantiate D (sch_mono T) n = (T, D, n).
Proof.
  intros D T n. unfold instantiate.
  assert (E : AtomSetImpl.elements (s_tq (sch_mono T)) = nil)
    by (apply elements_none; intros q; cbn [sch_mono s_tq]; fsetdec).
  assert (E' : AtomSetImpl.elements (s_rq (sch_mono T)) = nil)
    by (apply elements_none; intros q; cbn [sch_mono s_rq]; fsetdec).
  assert (Ei : apT (inst_sub (sch_mono T) n) (s_body (sch_mono T)) = T).
  { unfold apT. cbn [s_body]. apply ap_typ_pointwise_id.
    - intros a. unfold inst_sub. cbn [sT]. rewrite E. reflexivity.
    - intros r. unfold inst_sub. cbn [sR]. rewrite E'. reflexivity. }
  assert (Ed : inst_den D (sch_mono T) n = D).
  { unfold inst_den. rewrite E, E'. destruct D. reflexivity. }
  rewrite Ei, Ed, E, E'. simpl. repeat rewrite Nat.add_0_r. reflexivity.
Qed.


Lemma generic_sort_arith : forall o, kind o <> k_cmp -> generic_sort o = k_Numeric.
Proof. intros o H. unfold generic_sort. destruct (kind o); [ reflexivity | reflexivity | reflexivity | contradiction ]. Qed.

Lemma is_cmp_op_true : forall o, kind o = k_cmp -> is_cmp_op o = true.
Proof. intros o H. unfold is_cmp_op. rewrite H. reflexivity. Qed.

Lemma is_cmp_op_false : forall o, kind o <> k_cmp -> is_cmp_op o = false.
Proof. intros o H. unfold is_cmp_op. destruct (kind o); try reflexivity. contradiction. Qed.

Lemma is_generic_op_true : forall o, kind o <> k_quot -> is_generic_op o = true.
Proof. intros o H. unfold is_generic_op. destruct (kind o); try reflexivity. contradiction. Qed.

Lemma quot_ty_rf : forall T1 T2, rf T1 -> rf T2 -> quot_ty T1 T2 = typ_Float.
Proof.
  intros T1 T2 H1 H2. unfold quot_ty.
  assert (Hn : forall T, rf T -> float_head T = None)
    by (intros T H; destruct T; first [ reflexivity | (cbn in H; contradiction) ]).
  rewrite (Hn _ H1), (Hn _ H2). reflexivity.
Qed.



(* What a run ends with. *)
Definition Done (P : typ -> Prop) (L : atoms) (D1 : denv) (G : ctx) (e : exp) (D : denv) (n : nat)
  (Sg : sub) (T1 : typ) : Prop :=
  exists s D' n' S2 T e',
    Stable (fun f => infer f D G e n = Some (s, D', T, n', e')) /\
    SemL P L D1 Sg n s D' n' S2 /\ TOk n' T /\ Live P (ftv_typ T) D' D1 S2 /\
    teqD D1 (apT S2 T) T1 /\ is_gen_value e' = is_gen_value e.

Lemma Done_const : forall P L D1 G e D n Sg T1 c,
  (forall f, infer (S f) D G e n = Some (sid, D, c, n, e)) ->
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) ->
  DOk D n -> rkres D D1 (sR Sg) -> Live P L D D1 Sg -> teqD D1 c T1 -> Done P L D1 G e D n Sg T1.
Proof.
  intros P L D1 G e D n Sg T1 c Hi Hc Hd Hr HL Hteq.
  exists sid, D, n, Sg, c, e.
  refine (conj _ (conj (SemL_id P L D1 Sg D n Hr HL Hd) (conj (TOk_scalar n c Hc)
    (conj (Live_scalar P c D D1 Sg Hc) (conj _ eq_refl))))).
  - exists 1. intros f Hf. destruct f as [|f]; [ lia | exact (Hi f) ].
  - destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; exact Hteq.
Qed.

Lemma bin_res_arith : forall o A, kind o <> k_cmp -> bin_res o A = A.
Proof. intros o A H. unfold bin_res. destruct (kind o); try reflexivity. contradiction. Qed.

Ltac stable_run H :=
  eapply Stable_mono; [ | exact H ];
  intros [|f] Hf; [ contradiction | ].

Lemma ftv_arrow_sub : forall A B L, ftv_typ A [<=] L -> ftv_typ B [<=] L -> ftv_typ (typ_Arrow A B) [<=] L.
Proof. intros A B L H1 H2 y Hy. simpl in Hy. apply AtomSetFacts.union_iff in Hy. destruct Hy as [Hy|Hy]; [ apply H1 | apply H2 ]; exact Hy. Qed.

Lemma sub_ul : forall A B C : atoms, A [<=] B -> A [<=] B `union` C.
Proof. intros A B C H y Hy. apply AtomSetFacts.union_iff. left. exact (H y Hy). Qed.

Lemma in_fresh : forall (n : nat) (L : atoms), ea n `in` L `union` {{ ea n }}.
Proof. intros n L. apply AtomSetFacts.union_iff. right. apply AtomSetFacts.singleton_iff. reflexivity. Qed.

Lemma ftv_var_fresh : forall (n : nat) (L : atoms), ftv_typ (typ_Var (ea n)) [<=] L `union` {{ ea n }}.
Proof. intros n L y Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst y. apply in_fresh. Qed.

Lemma sub_scalar : forall (c : typ) (L : atoms),
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) -> ftv_typ c [<=] L.
Proof.
  intros c L Hc y Hy. exfalso. destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; simpl in Hy; revert Hy; fsetdec.
Qed.

(* ---- the induction ---- *)

Theorem infer_complete_core : forall P, P typ_Int -> forall D1 G1 e T1, ctyping P D1 G1 e T1 ->
  forall D G n Sg L, DOk D n -> LOld n L -> Live P L D D1 Sg -> rkres D D1 (sR Sg) ->
    GOk n G -> GLive L G -> CI D1 Sg G1 G -> Done P L D1 G e D n Sg T1.
Proof.
  intros P HPI Dd Gd e T1 H.
  induction H as
    [ Dd Gd x T Hu Hb
    | Dd Gd i T Hu Hs HPT
    | Dd Gd d Hu | Dd Gd Hu | Dd Gd Hu | Dd Gd Hu | Dd Gd q Hu
    | Dd Gd b T1 T2 HPT1 Hb IH
    | Dd Gd e1 e2 T1 T2 HPT2 H1 IH1 H2 IH2
    | Dd Gd e1 e2 e3 T H1 IH1 H2 IH2 H3 IH3
    | Dd Gd e A H1 IH1 Hs HPA
    | Dd Gd e1 o e2 A Hk1 Hk2 Hs HPA H1 IH1 H2 IH2
    | Dd Gd e1 e2 H1 IH1 H2 IH2
    | Dd Gd e1 o e2 A Hk Hs HPA H1 IH1 H2 IH2
    | Dd Gd e1 e2 T1 T2 Hv H1 IH1 H2 IH2
    | Dd Gd e T T' H1 IH1 Hteq ];
    intros D G n Sg L Hd HLo HLv HRk HG HGL HC.
  - (* variable *)
    destruct (CI_lookup Dd Sg Gd G x (sch_mono T) HC Hu Hb) as (T1' & T' & Ea & Eb & Hc).
    assert (ET : T = T1') by (apply (f_equal s_body) in Ea; exact Ea). subst T1'.
    pose proof (GLive_lookup L G x T' HGL Eb) as Hsub.
    exists sid, D, n, Sg, T', (e_fvar_f x).
    refine (conj _ (conj (SemL_id P L Dd Sg D n HRk HLv Hd) (conj _ (conj _ (conj Hc eq_refl))))).
    + exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
      cbn [infer]. rewrite Eb, instantiate_mono. reflexivity.
    + exact (GOk_lookup n G x T' HG Eb).
    + exact (Live_mono P _ _ D Dd Sg Hsub HLv).
  - (* numeral *)
    exists sid, (upd D (ea n) k_Literal), (S n), (supd Sg (ea n) T), (typ_Var (ea n)), (e_num i).
    refine (conj _ (conj (SemL_fresh P L Dd D Sg n k_Literal T HRk HLv Hd HLo) (conj _ (conj _ (conj _ _))))).
    + exists 1. intros f Hf. destruct f as [|f]; [ lia | reflexivity ].
    + apply TOk_var. apply old_ea. lia.
    + apply Live_var; rewrite ?upd_same, ?supd_same; assumption.
    + rewrite apT_Var, supd_same. apply teqD_refl.
    + reflexivity.
  - (* float literal *)
    apply (Done_const P L Dd G (e_dec d) D n Sg typ_Float typ_Float); try assumption;
      [ intros f; reflexivity | right; left; reflexivity | apply teqD_refl ].
  - apply (Done_const P L Dd G e_true D n Sg typ_Bool typ_Bool); try assumption;
      [ intros f; reflexivity | right; right; left; reflexivity | apply teqD_refl ].
  - apply (Done_const P L Dd G e_false D n Sg typ_Bool typ_Bool); try assumption;
      [ intros f; reflexivity | right; right; left; reflexivity | apply teqD_refl ].
  - apply (Done_const P L Dd G e_unit D n Sg typ_Unit typ_Unit); try assumption;
      [ intros f; reflexivity | right; right; right; left; reflexivity | apply teqD_refl ].
  - apply (Done_const P L Dd G (e_str q) D n Sg typ_String typ_String); try assumption;
      [ intros f; reflexivity | right; right; right; right; reflexivity | apply teqD_refl ].
  - (* program *)
    set (x := fresh_var G b).
    assert (Hx : x `notin` dom Gd `union` fv_exp b).
    { rewrite (CI_dom _ _ _ _ HC). pose proof (fresh_var_notin_dom G b). pose proof (fresh_var_notin_fv G b).
      fsetdec. }
    set (Sg' := supd Sg (ea n) T1).
    set (L' := L `union` {{ ea n }}).
    assert (Hsat : sat Dd (D (ea n)) T1) by (rewrite (DOk_ea D n n Hd (le_n n)); apply sat_any).
    assert (HTb : TOk (S n) (typ_Var (ea n))) by (apply TOk_var; apply old_ea; lia).
    assert (HsL : L [<=] L') by (intros y Hy; apply AtomSetFacts.union_iff; left; exact Hy).
    assert (HsV : ftv_typ (typ_Var (ea n)) [<=] L') by exact (ftv_var_fresh n L).
    assert (Hag : forall a, a `in` L -> sT Sg' a = sT Sg a).
    { intros a Ha. unfold Sg'. apply supd_other. intro E. exact (HLo a Ha n (le_n n) E). }
    assert (HLv' : Live P L' D Dd Sg').
    { exact (Live_fresh P L D D Dd Sg n (D (ea n)) T1 HLo HLv Hsat HPT1 eq_refl (fun _ _ => eq_refl)). }
    destruct (IH x Hx D ((x ~ sch_mono (typ_Var (ea n))) ++ G) (S n) Sg' L'
                (DOk_mono D n (S n) Hd (Nat.le_succ_diag_r n)) (LOld_fresh n L HLo) HLv' HRk
                (GOk_cons (S n) x _ G HTb (GOk_mono n (S n) G (Nat.le_succ_diag_r n) HG))
                (GLive_cons L' x _ G HsV (GLive_mono L L' G HsL HGL))
                (CI_cons Dd Sg' Gd G x T1 _ (CI_agree Dd Sg Sg' Gd G L n HC HG HGL Hag)
                   ltac:(unfold Sg'; rewrite apT_Var, supd_same; apply teqD_refl)))
      as (s & D' & n' & S2 & T & e' & Hst & Hsem & HT & LvT & Heq & HgHeq).
    exists s, D', n', S2, (typ_Arrow (apT s (typ_Var (ea n))) T), (e_abs (cl 0 x e')).
    pose proof (SemL_weaken P L Dd Sg Sg' n (S n) s D' n' S2 (Nat.le_succ_diag_r n) HLo
      (SemL_mono P L L' Dd Sg' (S n) s D' n' S2 HsL Hsem) Hag (fun _ _ => eq_refl)) as Hsem0.
    refine (conj _ (conj Hsem0 (conj _ (conj _ (conj _ _))))).
    + pose proof (Stable_below _ Hst) as HSt. stable_run HSt.
      cbn [infer]. change (fresh_var G b) with x. rewrite Hf. reflexivity.
    + apply TOk_arrow; [ exact (TOk_ap _ _ _ _ (SemL_SI Hsem) HTb) | exact HT ].
    + cbn [ftv_typ]. apply Live_union; [ | exact LvT ].
      refine (SemL_live_ap P L' Dd Sg' (S n) s D' n' S2 (typ_Var (ea n)) Hsem I _).
      exact HsV.
    + rewrite apT_Arrow. apply teqD_Arrow; [ | exact Heq ].
      pose proof (SemL_F Hsem (ea n) (in_fresh n L)) as F.
      unfold Sg' in F. rewrite supd_same in F. apply teqD_sym. exact F.
    + reflexivity.
  - (* call *)
    destruct (IH1 D G n Sg L Hd HLo HLv HRk HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & LvTa & Heq1 & HgHeq1).
    destruct (next_facts P Dd Gd Sg n L s1 D1a n1 Sa Ta G HLo Sem1 HTa LvTa HG HGL HC)
      as (HLo1 & HLv1 & HG1 & HGL1 & HC1).
    set (L2 := lnext s1 L Ta) in *.
    destruct (IH2 D1a (apC s1 G) n1 Sa L2 (SemL_DOk Sem1) HLo1 HLv1 (SemL_rk Sem1) HG1 HGL1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & LvTb & Heq2 & HgHeq2).
    destruct (next_facts P Dd Gd Sa n1 L2 s2 D2 n2 Sb Tb (apC s1 G) HLo1 Sem2 HTb LvTb HG1 HGL1 HC1)
      as (HLo2 & HLv2 & _ & _ & _).
    set (Ln := lnext s2 L2 Tb) in *.
    pose proof (SemL_DOk Sem2) as Hd2.
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem2) HTa) as HTa2.
    assert (Hle : n2 <= S n2) by lia.
    assert (HTv : TOk (S n2) (typ_Var (ea n2))) by (apply TOk_var; apply old_ea; lia).
    assert (HTarr : TOk (S n2) (typ_Arrow Tb (typ_Var (ea n2))))
      by (apply TOk_arrow; [ exact (TOk_mono _ _ _ Hle HTb) | exact HTv ]).
    assert (HsubTa : ftv_typ Ta [<=] L2) by exact (ftv_lnext s1 L Ta).
    assert (HsubTb : ftv_typ Tb [<=] Ln) by exact (ftv_lnext s2 L2 Tb).
    assert (HsubTa2 : ftv_typ (apT s2 Ta) [<=] Ln)
      by (intros y Hy; exact (limg_lnext s2 L2 Tb y (limg_ap s2 Ta L2 (proj1 HTa) HsubTa y Hy))).
    set (Lu := Ln `union` {{ ea n2 }}).
    assert (HLv3 : Live P Lu D2 Dd (supd Sb (ea n2) T2)).
    { exact (Live_fresh P Ln D2 D2 Dd Sb n2 k_Any T2 HLo2 HLv2 (sat_any _ _) HPT2
               (DOk_ea D2 n2 n2 Hd2 (le_n n2)) (fun _ _ => eq_refl)). }
    assert (Heq : teqD Dd (apT (supd Sb (ea n2) T2) (apT s2 Ta))
                          (apT (supd Sb (ea n2) T2) (typ_Arrow Tb (typ_Var (ea n2))))).
    { rewrite (apT_supd Sb (ea n2) T2 _ (proj1 HTa2) (fun Hin => proj2 HTa2 _ Hin n2 (le_n n2) eq_refl)).
      rewrite apT_Arrow, (apT_supd Sb (ea n2) T2 Tb (proj1 HTb) (fun Hin => proj2 HTb _ Hin n2 (le_n n2) eq_refl)),
        apT_Var, supd_same.
      eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor P L2 Dd Sa n1 s2 D2 n2 Sb Ta Sem2 (proj1 HTa) HsubTa) | ].
      eapply teqD_trans; [ exact Heq1 | ]. apply teqD_Arrow; [ apply teqD_sym; exact Heq2 | apply teqD_refl ]. }
    destruct (unify_stepL P Dd D2 (supd Sb (ea n2) T2) Lu (apT s2 Ta) (typ_Arrow Tb (typ_Var (ea n2))) (S n2)
                HPI (DOk_mono D2 n2 (S n2) Hd2 Hle) (LOld_fresh n2 Ln HLo2) HLv3 (SemL_rk Sem2)
                (proj1 HTa2) (conj (proj1 HTb) I)
                (sub_ul _ _ _ HsubTa2)
                (ftv_arrow_sub _ _ _ (sub_ul _ _ _ HsubTb) (ftv_var_fresh n2 Ln)) Heq)
      as (s3 & D3 & n3 & S3 & St3 & Sem3).
    pose proof (SemL_unfresh P Ln Dd Sb n2 T2 s3 D3 n3 S3 HLo2 Sem3) as Sem3'.
    pose proof (SemL_comp P L L2 Dd Sg n s1 D1a n1 Sa s2 D2 n2 Sb HLo Sem1 (limg_lnext s1 L Ta) Sem2) as Sem12.
    pose proof (limg_chain n n1 s1 s2 L L2 Ln HLo (SemL_SI Sem1) (limg_lnext s1 L Ta) (limg_lnext s2 L2 Tb)) as Hc2.
    exists (scomp s3 (scomp s2 s1)), D3, n3, S3, (apT s3 (typ_Var (ea n2))), (e_app e1' e2').
    refine (conj _ (conj (SemL_comp P L Ln Dd Sg n (scomp s2 s1) D2 n2 Sb s3 D3 n3 S3 HLo Sem12 Hc2 Sem3') (conj _ (conj _ (conj _ _))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 St3))) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2 & E3). cbn [infer]. rewrite E1, E2, E3. reflexivity.
    + exact (TOk_ap _ _ _ _ (SemL_SI Sem3) HTv).
    + refine (SemL_live_ap P Lu Dd _ (S n2) s3 D3 n3 S3 (typ_Var (ea n2)) Sem3 I _).
      exact (ftv_var_fresh n2 Ln).
    + pose proof (SemL_F Sem3 (ea n2) (in_fresh n2 Ln)) as F.
      rewrite supd_same in F. apply teqD_sym. exact F.
    + cbn [is_gen_value]; try reflexivity; try assumption.
  - (* if *)
    destruct (IH1 D G n Sg L Hd HLo HLv HRk HG HGL HC)
      as (s1 & D1a & n1 & Sa & Tc & c' & St1 & Sem1 & HTc & LvTc & Heq1 & HgHeq1).
    destruct (next_facts P Dd Gd Sg n L s1 D1a n1 Sa Tc G HLo Sem1 HTc LvTc HG HGL HC)
      as (HLo1 & HLv1 & HG1 & HGL1 & HC1).
    set (L1 := lnext s1 L Tc) in *.
    destruct (unify_stepL P Dd D1a Sa L1 Tc typ_Bool n1 HPI (SemL_DOk Sem1) HLo1 HLv1 (SemL_rk Sem1)
                (proj1 HTc) I (ftv_lnext s1 L Tc) (sub_scalar typ_Bool L1 (or_intror (or_intror (or_introl eq_refl)))) Heq1)
      as (s2 & D1b & n2 & Sb & St2 & Sem2).
    destruct (CI_stepL P L1 Dd Sa n1 s2 D1b n2 Sb Gd (apC s1 G) Sem2 HC1 HG1 HGL1) as (HC2 & HG2 & HGL2).
    set (Lb := limg s2 L1).
    assert (HLob : LOld n2 Lb) by exact (limg_old _ _ _ _ HLo1 (SemL_SI Sem2)).
    destruct (IH2 D1b (apC s2 (apC s1 G)) n2 Sb Lb (SemL_DOk Sem2) HLob (SemL_live Sem2) (SemL_rk Sem2) HG2 HGL2 HC2)
      as (s3 & D3 & n3 & Sc & Ta & a' & St3 & Sem3 & HTa & LvTa & Heq2 & HgHeq2).
    destruct (next_facts P Dd Gd Sb n2 Lb s3 D3 n3 Sc Ta (apC s2 (apC s1 G)) HLob Sem3 HTa LvTa HG2 HGL2 HC2)
      as (HLo3 & HLv3 & HG3 & HGL3 & HC3).
    set (L3 := lnext s3 Lb Ta) in *.
    destruct (IH3 D3 (apC s3 (apC s2 (apC s1 G))) n3 Sc L3 (SemL_DOk Sem3) HLo3 HLv3 (SemL_rk Sem3) HG3 HGL3 HC3)
      as (s4 & D4 & n4 & Sd & Tb & b' & St4 & Sem4 & HTb & LvTb & Heq3 & HgHeq3).
    destruct (next_facts P Dd Gd Sc n3 L3 s4 D4 n4 Sd Tb (apC s3 (apC s2 (apC s1 G))) HLo3 Sem4 HTb LvTb HG3 HGL3 HC3)
      as (HLo4 & HLv4 & _ & _ & _).
    set (L4 := lnext s4 L3 Tb) in *.
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem4) HTa) as HTa4.
    assert (HsubTa : ftv_typ Ta [<=] L3) by exact (ftv_lnext s3 Lb Ta).
    assert (HsubTa4 : ftv_typ (apT s4 Ta) [<=] L4)
      by (intros y Hy; exact (limg_lnext s4 L3 Tb y (limg_ap s4 Ta L3 (proj1 HTa) HsubTa y Hy))).
    assert (Heq : teqD Dd (apT Sd (apT s4 Ta)) (apT Sd Tb)).
    { eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor P L3 Dd Sc n3 s4 D4 n4 Sd Ta Sem4 (proj1 HTa) HsubTa) | ].
      eapply teqD_trans; [ exact Heq2 | apply teqD_sym; exact Heq3 ]. }
    destruct (unify_stepL P Dd D4 Sd L4 (apT s4 Ta) Tb n4 HPI (SemL_DOk Sem4) HLo4 HLv4 (SemL_rk Sem4)
                (proj1 HTa4) (proj1 HTb) HsubTa4 (ftv_lnext s4 L3 Tb) Heq)
      as (s5 & D5 & n5 & Se & St5 & Sem5).
    pose proof (SemL_comp P L L1 Dd Sg n s1 D1a n1 Sa s2 D1b n2 Sb HLo Sem1 (limg_lnext s1 L Tc)
      Sem2) as Sem12.
    pose proof (limg_chain n n1 s1 s2 L L1 Lb HLo (SemL_SI Sem1) (limg_lnext s1 L Tc) (fun _ H => H)) as Hc2.
    pose proof (SemL_comp P L Lb Dd Sg n (scomp s2 s1) D1b n2 Sb s3 D3 n3 Sc HLo Sem12 Hc2 Sem3) as Sem123.
    pose proof (SI_comp _ _ _ _ _ (SemL_SI Sem1) (SemL_SI Sem2)) as SI12.
    pose proof (limg_chain n n2 (scomp s2 s1) s3 L Lb L3 HLo SI12 Hc2 (limg_lnext s3 Lb Ta)) as Hc3.
    pose proof (SemL_comp P L L3 Dd Sg n (scomp s3 (scomp s2 s1)) D3 n3 Sc s4 D4 n4 Sd HLo Sem123 Hc3 Sem4) as Sem1234.
    pose proof (SI_comp _ _ _ _ _ SI12 (SemL_SI Sem3)) as SI123.
    pose proof (limg_chain n n3 (scomp s3 (scomp s2 s1)) s4 L L3 L4 HLo SI123 Hc3 (limg_lnext s4 L3 Tb)) as Hc4.
    exists (scomp s5 (scomp s4 (scomp s3 (scomp s2 s1)))), D5, n5, Se, (apT s5 Tb), (e_ite c' a' b').
    refine (conj _ (conj (SemL_comp P L L4 Dd Sg n _ D4 n4 Sd s5 D5 n5 Se HLo Sem1234 Hc4 Sem5) (conj _ (conj _ (conj _ _))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3
        (Stable_and _ _ St4 St5))))) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2 & E3 & E4 & E5). cbn [infer]. rewrite E1, E2, E3, E4, E5. reflexivity.
    + exact (TOk_ap _ _ _ _ (SemL_SI Sem5) HTb).
    + exact (SemL_live_ap P L4 Dd Sd n4 s5 D5 n5 Se Tb Sem5 (proj1 HTb) (ftv_lnext s4 L3 Tb)).
    + eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor P L4 Dd Sd n4 s5 D5 n5 Se Tb Sem5 (proj1 HTb) (ftv_lnext s4 L3 Tb)) | ].
      exact Heq3.
    + cbn [is_gen_value]; try reflexivity; try assumption.
  - (* float(e) *)
    destruct (IH1 D G n Sg L Hd HLo HLv HRk HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e' & St1 & Sem1 & HTa & LvTa & Heq1 & HgHeq1).
    destruct (next_facts P Dd Gd Sg n L s1 D1a n1 Sa Ta G HLo Sem1 HTa LvTa HG HGL HC)
      as (HLo1 & HLv1 & _ & _ & _).
    set (L1 := lnext s1 L Ta) in *.
    assert (Hle : n1 <= S n1) by lia.
    assert (HTv : TOk (S n1) (typ_Var (ea n1))) by (apply TOk_var; apply old_ea; lia).
    assert (HsubTa : ftv_typ Ta [<=] L1) by exact (ftv_lnext s1 L Ta).
    assert (HLv2 : Live P (L1 `union` {{ ea n1 }}) (upd D1a (ea n1) k_Literal) Dd (supd Sa (ea n1) A)).
    { refine (Live_fresh P L1 D1a (upd D1a (ea n1) k_Literal) Dd Sa n1 k_Literal A HLo1 HLv1 Hs HPA
                (upd_same _ _ _) (fun a Ha => upd_other D1a (ea n1) k_Literal a (fun E => HLo1 a Ha n1 (le_n n1) E))). }
    assert (Heq : teqD Dd (apT (supd Sa (ea n1) A) Ta) (apT (supd Sa (ea n1) A) (typ_Var (ea n1)))).
    { rewrite (apT_supd Sa (ea n1) A Ta (proj1 HTa) (fun Hin => proj2 HTa _ Hin n1 (le_n n1) eq_refl)),
        apT_Var, supd_same. exact Heq1. }
    destruct (unify_stepL P Dd (upd D1a (ea n1) k_Literal) (supd Sa (ea n1) A) (L1 `union` {{ ea n1 }})
                Ta (typ_Var (ea n1)) (S n1) HPI (DOk_upd D1a n1 k_Literal (SemL_DOk Sem1))
                (LOld_fresh n1 L1 HLo1) HLv2 (fun r => SemL_rk Sem1 r) (proj1 HTa) I
                (sub_ul _ _ _ HsubTa) (ftv_var_fresh n1 L1) Heq) as (s2 & D2 & n2 & S3 & St2 & Sem2).
    pose proof (SemL_unfresh P L1 Dd Sa n1 A s2 D2 n2 S3 HLo1 Sem2) as Sem2'.
    exists (scomp s2 s1), D2, n2, S3, typ_Float, (e_tofloat e').
    refine (conj _ (conj (SemL_comp P L L1 Dd Sg n s1 D1a n1 Sa s2 D2 n2 S3 HLo Sem1 (limg_lnext s1 L Ta) Sem2') (conj _ (conj _ (conj _ _))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 St2)) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2). cbn [infer]. rewrite E1, E2. reflexivity.
    + apply TOk_scalar. right. left. reflexivity.
    + apply Live_scalar. right. left. reflexivity.
    + apply teqD_refl.
    + cbn [is_gen_value]; try reflexivity; try assumption.
  - (* arithmetic *)
    destruct (IH1 D G n Sg L Hd HLo HLv HRk HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & LvTa & Heq1 & HgHeq1).
    destruct (next_facts P Dd Gd Sg n L s1 D1a n1 Sa Ta G HLo Sem1 HTa LvTa HG HGL HC)
      as (HLo1 & HLv1 & HG1 & HGL1 & HC1).
    set (L1 := lnext s1 L Ta) in *.
    destruct (IH2 D1a (apC s1 G) n1 Sa L1 (SemL_DOk Sem1) HLo1 HLv1 (SemL_rk Sem1) HG1 HGL1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & LvTb & Heq2 & HgHeq2).
    destruct (next_facts P Dd Gd Sa n1 L1 s2 D2 n2 Sb Tb (apC s1 G) HLo1 Sem2 HTb LvTb HG1 HGL1 HC1)
      as (HLo2 & HLv2 & _ & _ & _).
    set (Ln := lnext s2 L1 Tb) in *.
    assert (HTv : TOk (S n2) (typ_Var (ea n2))) by (apply TOk_var; apply old_ea; lia).
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem2) HTa) as HTa2.
    assert (HsubTa : ftv_typ Ta [<=] L1) by exact (ftv_lnext s1 L Ta).
    assert (HsubTb : ftv_typ Tb [<=] Ln) by exact (ftv_lnext s2 L1 Tb).
    assert (HsubTa2 : ftv_typ (apT s2 Ta) [<=] Ln)
      by (intros y Hy; exact (limg_lnext s2 L1 Tb y (limg_ap s2 Ta L1 (proj1 HTa) HsubTa y Hy))).
    assert (Hg : sat Dd (generic_sort o) A) by (rewrite (generic_sort_arith o Hk1); exact Hs).
    assert (HLv3 : Live P (Ln `union` {{ ea n2 }}) (upd D2 (ea n2) (generic_sort o)) Dd (supd Sb (ea n2) A)).
    { refine (Live_fresh P Ln D2 (upd D2 (ea n2) (generic_sort o)) Dd Sb n2 (generic_sort o) A HLo2 HLv2 Hg HPA
                (upd_same _ _ _) (fun a Ha => upd_other D2 (ea n2) (generic_sort o) a (fun E => HLo2 a Ha n2 (le_n n2) E))). }
    assert (Heq : teqD Dd (apT (supd Sb (ea n2) A) (apT s2 Ta)) (apT (supd Sb (ea n2) A) (typ_Var (ea n2)))).
    { rewrite (apT_supd Sb (ea n2) A _ (proj1 HTa2) (fun Hin => proj2 HTa2 _ Hin n2 (le_n n2) eq_refl)),
        apT_Var, supd_same.
      eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor P L1 Dd Sa n1 s2 D2 n2 Sb Ta Sem2 (proj1 HTa) HsubTa) | ].
      exact Heq1. }
    destruct (unify_stepL P Dd (upd D2 (ea n2) (generic_sort o)) (supd Sb (ea n2) A) (Ln `union` {{ ea n2 }})
                (apT s2 Ta) (typ_Var (ea n2)) (S n2) HPI (DOk_upd D2 n2 _ (SemL_DOk Sem2))
                (LOld_fresh n2 Ln HLo2) HLv3 (fun r => SemL_rk Sem2 r) (proj1 HTa2) I
                (sub_ul _ _ _ HsubTa2) (ftv_var_fresh n2 Ln) Heq) as (s3 & D3 & n3 & S3 & St3 & Sem3).
    pose proof (SemL_unfresh P Ln Dd Sb n2 A s3 D3 n3 S3 HLo2 Sem3) as Sem3'.
    set (Lu := Ln `union` {{ ea n2 }}) in *.
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem3) HTv) as HTc3.
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem3') HTb) as HTb3.
    assert (Fc : teqD Dd A (apT S3 (apT s3 (typ_Var (ea n2))))).
    { pose proof (SemL_F Sem3 (ea n2) (in_fresh n2 Ln)) as F. rewrite supd_same in F. exact F. }
    assert (Heq' : teqD Dd (apT S3 (apT s3 Tb)) (apT S3 (apT s3 (typ_Var (ea n2))))).
    { eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor P Ln Dd Sb n2 s3 D3 n3 S3 Tb Sem3' (proj1 HTb) HsubTb) | ].
      eapply teqD_trans; [ exact Heq2 | exact Fc ]. }
    assert (HLo3 : LOld n3 (limg s3 Lu)) by exact (limg_old _ _ _ _ (LOld_fresh n2 Ln HLo2) (SemL_SI Sem3)).
    destruct (unify_stepL P Dd D3 S3 (limg s3 Lu) (apT s3 Tb) (apT s3 (typ_Var (ea n2))) n3 HPI (SemL_DOk Sem3)
                HLo3 (SemL_live Sem3) (SemL_rk Sem3) (proj1 HTb3) (proj1 HTc3)
                (limg_ap s3 Tb Lu (proj1 HTb) (sub_ul _ _ _ HsubTb))
                (limg_ap s3 (typ_Var (ea n2)) Lu I (ftv_var_fresh n2 Ln)) Heq')
      as (s4 & D4 & n4 & S4 & St4 & Sem4).
    pose proof (SemL_comp P L L1 Dd Sg n s1 D1a n1 Sa s2 D2 n2 Sb HLo Sem1 (limg_lnext s1 L Ta) Sem2) as Sem12.
    pose proof (limg_chain n n1 s1 s2 L L1 Ln HLo (SemL_SI Sem1) (limg_lnext s1 L Ta) (limg_lnext s2 L1 Tb)) as Hc2.
    pose proof (SemL_comp P L Ln Dd Sg n (scomp s2 s1) D2 n2 Sb s3 D3 n3 S3 HLo Sem12 Hc2 Sem3') as Sem123.
    pose proof (SI_comp _ _ _ _ _ (SemL_SI Sem1) (SemL_SI Sem2)) as SI12.
    pose proof (limg_chain n n2 (scomp s2 s1) s3 L Ln (limg s3 Lu) HLo SI12 Hc2
      (limg_mono s3 _ _ (sub_ul _ _ _ (fun _ H => H)))) as Hc3.
    exists (scomp s4 (scomp s3 (scomp s2 s1))), D4, n4, S4, (apT s4 (apT s3 (typ_Var (ea n2)))), (e_bin e1' o e2').
    refine (conj _ (conj (SemL_comp P L (limg s3 Lu) Dd Sg n _ D3 n3 S3 s4 D4 n4 S4 HLo Sem123 Hc3 Sem4) (conj _ (conj _ (conj _ _))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3 St4)))) as HSt.
      stable_run HSt. destruct Hf as (E1 & E2 & E3 & E4). cbn [infer]. rewrite E1, E2.
      rewrite (is_cmp_op_false o Hk1), (is_generic_op_true o Hk2). cbv beta iota zeta.
      rewrite E3, E4. rewrite (bin_res_arith o _ Hk1). reflexivity.
    + exact (TOk_ap _ _ _ _ (SemL_SI Sem4) HTc3).
    + exact (SemL_live_ap P (limg s3 Lu) Dd S3 n3 s4 D4 n4 S4 _ Sem4 (proj1 HTc3) (limg_ap s3 (typ_Var (ea n2)) Lu I (ftv_var_fresh n2 Ln))).
    + eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor P (limg s3 Lu) Dd S3 n3 s4 D4 n4 S4 _ Sem4 (proj1 HTc3) (limg_ap s3 (typ_Var (ea n2)) Lu I (ftv_var_fresh n2 Ln))) | ].
      apply teqD_sym. exact Fc.
    + cbn [is_gen_value]; try reflexivity; try assumption.
  - (* division *)
    destruct (IH1 D G n Sg L Hd HLo HLv HRk HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & LvTa & Heq1 & HgHeq1).
    destruct (next_facts P Dd Gd Sg n L s1 D1a n1 Sa Ta G HLo Sem1 HTa LvTa HG HGL HC)
      as (HLo1 & HLv1 & HG1 & HGL1 & HC1).
    set (L1 := lnext s1 L Ta) in *.
    destruct (IH2 D1a (apC s1 G) n1 Sa L1 (SemL_DOk Sem1) HLo1 HLv1 (SemL_rk Sem1) HG1 HGL1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & LvTb & Heq2 & HgHeq2).
    destruct (next_facts P Dd Gd Sa n1 L1 s2 D2 n2 Sb Tb (apC s1 G) HLo1 Sem2 HTb LvTb HG1 HGL1 HC1)
      as (HLo2 & HLv2 & _ & _ & _).
    set (Ln := lnext s2 L1 Tb) in *.
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem2) HTa) as HTa2.
    assert (HsubTa : ftv_typ Ta [<=] L1) by exact (ftv_lnext s1 L Ta).
    assert (HsubTb : ftv_typ Tb [<=] Ln) by exact (ftv_lnext s2 L1 Tb).
    assert (HsubTa2 : ftv_typ (apT s2 Ta) [<=] Ln)
      by (intros y Hy; exact (limg_lnext s2 L1 Tb y (limg_ap s2 Ta L1 (proj1 HTa) HsubTa y Hy))).
    assert (HsubF : forall L', ftv_typ typ_Float [<=] L') by (intros L'; exact (sub_scalar typ_Float L' (or_intror (or_introl eq_refl)))).
    assert (Heq : teqD Dd (apT Sb (apT s2 Ta)) (apT Sb typ_Float)).
    { eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor P L1 Dd Sa n1 s2 D2 n2 Sb Ta Sem2 (proj1 HTa) HsubTa) | ].
      exact Heq1. }
    destruct (unify_stepL P Dd D2 Sb Ln (apT s2 Ta) typ_Float n2 HPI (SemL_DOk Sem2) HLo2 HLv2 (SemL_rk Sem2)
                (proj1 HTa2) I HsubTa2 (HsubF Ln) Heq) as (s3 & D3 & n3 & S3 & St3 & Sem3).
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem3) HTb) as HTb3.
    assert (Heq' : teqD Dd (apT S3 (apT s3 Tb)) (apT S3 typ_Float)).
    { eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor P Ln Dd Sb n2 s3 D3 n3 S3 Tb Sem3 (proj1 HTb) HsubTb) | ].
      exact Heq2. }
    assert (HLo3 : LOld n3 (limg s3 Ln)) by exact (limg_old _ _ _ _ HLo2 (SemL_SI Sem3)).
    destruct (unify_stepL P Dd D3 S3 (limg s3 Ln) (apT s3 Tb) typ_Float n3 HPI (SemL_DOk Sem3) HLo3
                (SemL_live Sem3) (SemL_rk Sem3) (proj1 HTb3) I (limg_ap s3 Tb Ln (proj1 HTb) HsubTb)
                (HsubF _) Heq') as (s4 & D4 & n4 & S4 & St4 & Sem4).
    pose proof (SemL_comp P L L1 Dd Sg n s1 D1a n1 Sa s2 D2 n2 Sb HLo Sem1 (limg_lnext s1 L Ta) Sem2) as Sem12.
    pose proof (limg_chain n n1 s1 s2 L L1 Ln HLo (SemL_SI Sem1) (limg_lnext s1 L Ta) (limg_lnext s2 L1 Tb)) as Hc2.
    pose proof (SemL_comp P L Ln Dd Sg n (scomp s2 s1) D2 n2 Sb s3 D3 n3 S3 HLo Sem12 Hc2 Sem3) as Sem123.
    pose proof (SI_comp _ _ _ _ _ (SemL_SI Sem1) (SemL_SI Sem2)) as SI12.
    pose proof (limg_chain n n2 (scomp s2 s1) s3 L Ln (limg s3 Ln) HLo SI12 Hc2 (fun _ H => H)) as Hc3.
    exists (scomp s4 (scomp s3 (scomp s2 s1))), D4, n4, S4, typ_Float, (e_bin e1' bop_div e2').
    refine (conj _ (conj (SemL_comp P L (limg s3 Ln) Dd Sg n _ D3 n3 S3 s4 D4 n4 S4 HLo Sem123 Hc3 Sem4) (conj _ (conj _ (conj _ _))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3 St4)))) as HSt.
      stable_run HSt. destruct Hf as (E1 & E2 & E3 & E4). cbn [infer]. rewrite E1, E2.
      rewrite (is_cmp_op_false bop_div ltac:(discriminate)).
      change (is_generic_op bop_div) with false. cbv beta iota zeta.
      rewrite (quot_ty_rf _ _ (proj1 HTa2) (proj1 HTb)), E3, E4. reflexivity.
    + apply TOk_scalar. right. left. reflexivity.
    + apply Live_scalar. right. left. reflexivity.
    + apply teqD_refl.
    + cbn [is_gen_value]; try reflexivity; try assumption.
  - (* comparison *)
    destruct (IH1 D G n Sg L Hd HLo HLv HRk HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & LvTa & Heq1 & HgHeq1).
    destruct (next_facts P Dd Gd Sg n L s1 D1a n1 Sa Ta G HLo Sem1 HTa LvTa HG HGL HC)
      as (HLo1 & HLv1 & HG1 & HGL1 & HC1).
    set (L1 := lnext s1 L Ta) in *.
    destruct (IH2 D1a (apC s1 G) n1 Sa L1 (SemL_DOk Sem1) HLo1 HLv1 (SemL_rk Sem1) HG1 HGL1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & LvTb & Heq2 & HgHeq2).
    destruct (next_facts P Dd Gd Sa n1 L1 s2 D2 n2 Sb Tb (apC s1 G) HLo1 Sem2 HTb LvTb HG1 HGL1 HC1)
      as (HLo2 & HLv2 & _ & _ & _).
    set (Ln := lnext s2 L1 Tb) in *.
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem2) HTa) as HTa2.
    assert (HsubTa : ftv_typ Ta [<=] L1) by exact (ftv_lnext s1 L Ta).
    assert (HsubTb : ftv_typ Tb [<=] Ln) by exact (ftv_lnext s2 L1 Tb).
    assert (HsubTa2 : ftv_typ (apT s2 Ta) [<=] Ln)
      by (intros y Hy; exact (limg_lnext s2 L1 Tb y (limg_ap s2 Ta L1 (proj1 HTa) HsubTa y Hy))).
    assert (Heq : teqD Dd (apT Sb (apT s2 Ta)) (apT Sb Tb)).
    { eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor P L1 Dd Sa n1 s2 D2 n2 Sb Ta Sem2 (proj1 HTa) HsubTa) | ].
      eapply teqD_trans; [ exact Heq1 | apply teqD_sym; exact Heq2 ]. }
    destruct (unify_stepL P Dd D2 Sb Ln (apT s2 Ta) Tb n2 HPI (SemL_DOk Sem2) HLo2 HLv2 (SemL_rk Sem2)
                (proj1 HTa2) (proj1 HTb) HsubTa2 HsubTb Heq) as (s3 & D3 & n3 & S3 & St3 & Sem3).
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem3) HTb) as HTb3.
    assert (HTv : TOk (S n3) (typ_Var (ea n3))) by (apply TOk_var; apply old_ea; lia).
    assert (HLo3 : LOld n3 (limg s3 Ln)) by exact (limg_old _ _ _ _ HLo2 (SemL_SI Sem3)).
    assert (HsubTb3 : ftv_typ (apT s3 Tb) [<=] limg s3 Ln) by exact (limg_ap s3 Tb Ln (proj1 HTb) HsubTb).
    assert (HLv4 : Live P (limg s3 Ln `union` {{ ea n3 }}) (upd D3 (ea n3) k_Eq) Dd (supd S3 (ea n3) A)).
    { refine (Live_fresh P (limg s3 Ln) D3 (upd D3 (ea n3) k_Eq) Dd S3 n3 k_Eq A HLo3 (SemL_live Sem3) Hs HPA
                (upd_same _ _ _) (fun a Ha => upd_other D3 (ea n3) k_Eq a (fun E => HLo3 a Ha n3 (le_n n3) E))). }
    assert (Heq' : teqD Dd (apT (supd S3 (ea n3) A) (apT s3 Tb)) (apT (supd S3 (ea n3) A) (typ_Var (ea n3)))).
    { rewrite (apT_supd S3 (ea n3) A _ (proj1 HTb3) (fun Hin => proj2 HTb3 _ Hin n3 (le_n n3) eq_refl)),
        apT_Var, supd_same.
      eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor P Ln Dd Sb n2 s3 D3 n3 S3 Tb Sem3 (proj1 HTb) HsubTb) | ].
      exact Heq2. }
    destruct (unify_stepL P Dd (upd D3 (ea n3) k_Eq) (supd S3 (ea n3) A) (limg s3 Ln `union` {{ ea n3 }})
                (apT s3 Tb) (typ_Var (ea n3)) (S n3) HPI (DOk_upd D3 n3 k_Eq (SemL_DOk Sem3))
                (LOld_fresh n3 _ HLo3) HLv4 (fun r => SemL_rk Sem3 r) (proj1 HTb3) I
                (sub_ul _ _ _ HsubTb3) (ftv_var_fresh n3 _) Heq') as (s4 & D4 & n4 & S4 & St4 & Sem4).
    pose proof (SemL_unfresh P (limg s3 Ln) Dd S3 n3 A s4 D4 n4 S4 HLo3 Sem4) as Sem4'.
    pose proof (SemL_comp P L L1 Dd Sg n s1 D1a n1 Sa s2 D2 n2 Sb HLo Sem1 (limg_lnext s1 L Ta) Sem2) as Sem12.
    pose proof (limg_chain n n1 s1 s2 L L1 Ln HLo (SemL_SI Sem1) (limg_lnext s1 L Ta) (limg_lnext s2 L1 Tb)) as Hc2.
    pose proof (SemL_comp P L Ln Dd Sg n (scomp s2 s1) D2 n2 Sb s3 D3 n3 S3 HLo Sem12 Hc2 Sem3) as Sem123.
    pose proof (SI_comp _ _ _ _ _ (SemL_SI Sem1) (SemL_SI Sem2)) as SI12.
    pose proof (limg_chain n n2 (scomp s2 s1) s3 L Ln (limg s3 Ln) HLo SI12 Hc2 (fun _ H => H)) as Hc3.
    exists (scomp s4 (scomp s3 (scomp s2 s1))), D4, n4, S4, typ_Bool, (e_bin e1' o e2').
    refine (conj _ (conj (SemL_comp P L (limg s3 Ln) Dd Sg n _ D3 n3 S3 s4 D4 n4 S4 HLo Sem123 Hc3 Sem4') (conj _ (conj _ (conj _ _))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3 St4)))) as HSt.
      stable_run HSt. destruct Hf as (E1 & E2 & E3 & E4). cbn [infer]. rewrite E1, E2.
      rewrite (is_cmp_op_true o Hk). cbv beta iota zeta. rewrite E3, E4. reflexivity.
    + apply TOk_scalar. right. right. left. reflexivity.
    + apply Live_scalar. right. right. left. reflexivity.
    + apply teqD_refl.
    + cbn [is_gen_value]; try reflexivity; try assumption.
  - (* let of a binding that is not a value *)
    destruct (IH1 D G n Sg L Hd HLo HLv HRk HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & LvTa & Heq1 & Hgv).
    destruct (next_facts P Dd Gd Sg n L s1 D1a n1 Sa Ta G HLo Sem1 HTa LvTa HG HGL HC)
      as (HLo1 & HLv1 & HG1 & HGL1 & HC1).
    set (L1 := lnext s1 L Ta) in *.
    rewrite Hv in Hgv.
    assert (Hx : fresh_var (apC s1 G) e2 `notin` dom Gd `union` fv_exp e2).
    { rewrite (CI_dom _ _ _ _ HC). pose proof (dom_apC s1 G).
      pose proof (fresh_var_notin_dom (apC s1 G) e2). pose proof (fresh_var_notin_fv (apC s1 G) e2). fsetdec. }
    destruct (IH2 _ Hx D1a ((fresh_var (apC s1 G) e2 ~ sch_mono Ta) ++ apC s1 G) n1 Sa L1
                (SemL_DOk Sem1) HLo1 HLv1 (SemL_rk Sem1) (GOk_cons n1 _ Ta _ HTa HG1)
                (GLive_cons L1 _ Ta _ (ftv_lnext s1 L Ta) HGL1)
                (CI_cons Dd Sa Gd (apC s1 G) _ T1 Ta HC1 Heq1))
      as (s2 & D2 & n2 & Sb & T & e2' & St2 & Sem2 & HT & LvT & Heq2 & Hg2).
    exists (scomp s2 s1), D2, n2, Sb, T, (e_let e1' (cl 0 (fresh_var (apC s1 G) e2) e2')).
    refine (conj _ (conj (SemL_comp P L L1 Dd Sg n s1 D1a n1 Sa s2 D2 n2 Sb HLo Sem1 (limg_lnext s1 L Ta) Sem2)
      (conj HT (conj LvT (conj Heq2 _))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 St2)) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2). cbn [infer]. rewrite E1, Hgv. cbv beta iota zeta. rewrite E2. reflexivity.
    + reflexivity.
  - (* conversion *)
    destruct (IH1 D G n Sg L Hd HLo HLv HRk HG HGL HC)
      as (s & D' & n' & S2 & T0 & e' & Hst & Hsem & HT & LvT & Heq & HgHeq).
    exists s, D', n', S2, T0, e'. refine (conj Hst (conj Hsem (conj HT (conj LvT (conj _ HgHeq))))).
    eapply teqD_trans; [ exact Heq | exact Hteq ].
Qed.


(* The closed program: a derivation of a core program at the program judgment
   gives a run of the closed entry point from some fuel on, whose result is a
   principal type of the derivation's, and whose elaborated term erases to the
   program. *)
Theorem infer_complete_core_closed : forall e T, ctyping (fun _ => True) d_any nil e T ->
  exists D T' e' S2,
    Stable (fun f => infer_closed_elab f e = Some (D, T', e')) /\ erase e' = e /\
    Live (fun _ => True) (ftv_typ T') D d_any S2 /\ rkres D d_any (sR S2) /\
    teqD d_any (apT S2 T') T /\ rf T'.
Proof.
  intros e T H.
  destruct (infer_complete_core (fun _ => True) I d_any nil e T H d_any nil 0 sid {}
              (d_any_DOk 0) (fun a Ha => ltac:(exfalso; revert Ha; fsetdec)) (Live_empty _ _ _ _)
              (proj2 (KR_id d_any)) (GOk_nil 0) (GLive_nil {}) (CI_nil d_any sid))
    as (s & D' & n' & S2 & T' & e' & St & Sem & HT & LvT & Heq & HgHeq).
  exists D', T', e', S2.
  assert (St' : Stable (fun f => infer_closed_elab f e = Some (D', T', e'))).
  { eapply Stable_mono; [ | exact St ]. intros f Hf. unfold infer_closed_elab. rewrite Hf. reflexivity. }
  refine (conj St' (conj _ (conj LvT (conj (SemL_rk Sem) (conj Heq (proj1 HT)))))).
  destruct St' as [f0 Hf0]. exact (proj2 (infer_closed_sound f0 e D' T' e' (Hf0 f0 (le_n f0)))).
Qed.

(* The identity function has the derivation at [Int -> Int]; the algorithm
   answers with a type of which that one is an instance. *)
Example core_identity : exists D T' e' S2,
  Stable (fun f => infer_closed_elab f (e_abs (e_fvar_b 0)) = Some (D, T', e')) /\
  erase e' = e_abs (e_fvar_b 0) /\ Live (fun _ => True) (ftv_typ T') D d_any S2 /\ rkres D d_any (sR S2) /\
  teqD d_any (apT S2 T') (typ_Arrow typ_Int typ_Int) /\ rf T'.
Proof.
  apply infer_complete_core_closed. apply C_Abs; [ exact I | ]. intros x Hx. simpl.
  apply C_Var; [ solve_uniq | apply binds_one_3; reflexivity ].
Qed.

(* A comparison, which unifies its operands and only then requires the joined
   type to be [Eq]. *)
Example core_comparison : exists D T' e' S2,
  Stable (fun f => infer_closed_elab f (e_abs (e_bin (e_fvar_b 0) bop_eq (e_fvar_b 0))) = Some (D, T', e')) /\
  erase e' = e_abs (e_bin (e_fvar_b 0) bop_eq (e_fvar_b 0)) /\
  Live (fun _ => True) (ftv_typ T') D d_any S2 /\ rkres D d_any (sR S2) /\
  teqD d_any (apT S2 T') (typ_Arrow typ_Int typ_Bool) /\ rf T'.
Proof.
  apply infer_complete_core_closed. apply C_Abs; [ exact I | ]. intros x Hx. simpl.
  apply C_Cmp with (A := typ_Int); [ reflexivity | simpl; auto | exact I | | ];
    (apply C_Var; [ solve_uniq | apply binds_one_3; reflexivity ]).
Qed.
