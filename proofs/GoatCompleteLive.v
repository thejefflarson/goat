(* Completeness of algorithm W, stage 7.8c: what a step carries past record-free
   types (docs/design/phase7-proof-plan.md).

   GoatCompleteCtx.v states a step ([SemL]) over the type atoms of a live set [L]
   and reads the unifier through its record-free completeness.  A run that
   generalizes holds row variables and presence variables too, and its types are
   in the fragment of 7.6 ([pf], [ps], [atT]).  This file states the live clauses
   and the step for that fragment and proves the unifier's step ([unify_stepG])
   from [unify_tD_complete_full]:

   - [LiveG E F L LR D Dd S] is [Live] on the type atoms [L] and the row variables
     [LR]: [S] sends each live type atom to a type of its sort and each live row
     variable to a row of its kind (read in [Dd]), the atoms the images mention
     satisfy [E] (type atoms) and [F] (row variables), and a [Numeric] or [Quot]
     atom is not sent to a record ([NN]).  [E] and [F] replace the allowed set of
     images [P] of [Live]: the unifier's extension invents no type, but it does
     rename ([Cov]), so a property of the atoms an image mentions survives a step
     where "the image is record-free" does not.
   - [restrG L LR Sg] is the full substitution the unifier needs: [Sg] on the live
     atoms, [Float] on the other type atoms and the empty row on the other row
     variables, which satisfy every sort and every kind.
   - [PLive LP S] says [S] sends the presence atoms [LP] to [Unit]; [psA] reads
     [ps] off it, and [PLive_step] carries it through a step, because a step's
     image of a presence atom is [Unit] or a variable the extension sends to [Unit].

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
Require Import Goat.GoatCoerce.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteRewrite.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteHeld.
Require Import Goat.GoatInferW.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the live clauses ---- *)

(* The live type atoms are sent to types of their sort. *)
Definition SatL (L : atoms) (D Dd : denv) (S : sub) : Prop :=
  forall a, a `in` L -> sat Dd (D a) (sT S a).

(* The live row variables are sent to rows of their kind. *)
Definition RLive (LR : atoms) (D Dd : denv) (S : sub) : Prop :=
  forall q, q `in` LR -> rkok Dd (drk D q) (sR S q).

(* The images of the live atoms mention only atoms [E] and [F] allow. *)
Definition BndL (E F : atom -> Prop) (L LR : atoms) (S : sub) : Prop :=
  (forall a, a `in` L -> (forall b, b `in` ftv_typ (sT S a) -> E b) /\
                         (forall q, q `in` frv_typ (sT S a) -> F q)) /\
  (forall q, q `in` LR -> (forall b, b `in` ftv_row (sR S q) -> E b) /\
                          (forall r, r `in` frv_row (sR S q) -> F r)).

(* A live atom of sort [Numeric] or [Quot] is not sent to a record. *)
Definition NNL (L : atoms) (D : denv) (S : sub) : Prop :=
  forall a, a `in` L -> NQ (D a) -> forall R, sT S a <> typ_Record R.

Definition LiveG (E F : atom -> Prop) (L LR : atoms) (D Dd : denv) (S : sub) : Prop :=
  SatL L D Dd S /\ RLive LR D Dd S /\ BndL E F L LR S /\ NNL L D S.

Lemma LiveG_mono : forall E F L1 L2 LR1 LR2 D Dd S, L1 [<=] L2 -> LR1 [<=] LR2 ->
  LiveG E F L2 LR2 D Dd S -> LiveG E F L1 LR1 D Dd S.
Proof.
  intros E F L1 L2 LR1 LR2 D Dd S Hl Hr (Hs & Hq & (Ht & Hb) & Hn).
  refine (conj _ (conj _ (conj (conj _ _) _))).
  - intros a Ha. exact (Hs a (Hl a Ha)).
  - intros q Hq'. exact (Hq q (Hr q Hq')).
  - intros a Ha. exact (Ht a (Hl a Ha)).
  - intros q Hq'. exact (Hb q (Hr q Hq')).
  - intros a Ha. exact (Hn a (Hl a Ha)).
Qed.

Lemma LiveG_empty : forall E F D Dd S, LiveG E F {} {} D Dd S.
Proof.
  intros E F D Dd S. refine (conj _ (conj _ (conj (conj _ _) _))); intros a Ha; exfalso; revert Ha; fsetdec.
Qed.

Lemma LiveG_union : forall E F L1 L2 LR1 LR2 D Dd S,
  LiveG E F L1 LR1 D Dd S -> LiveG E F L2 LR2 D Dd S ->
  LiveG E F (L1 `union` L2) (LR1 `union` LR2) D Dd S.
Proof.
  intros E F L1 L2 LR1 LR2 D Dd S (S1 & Q1 & (T1 & B1) & N1) (S2 & Q2 & (T2 & B2) & N2).
  refine (conj _ (conj _ (conj (conj _ _) _))).
  - intros a Ha. apply AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha]; [ exact (S1 a Ha) | exact (S2 a Ha) ].
  - intros q Hq. apply AtomSetFacts.union_iff in Hq. destruct Hq as [Hq|Hq]; [ exact (Q1 q Hq) | exact (Q2 q Hq) ].
  - intros a Ha. apply AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha]; [ exact (T1 a Ha) | exact (T2 a Ha) ].
  - intros q Hq. apply AtomSetFacts.union_iff in Hq. destruct Hq as [Hq|Hq]; [ exact (B1 q Hq) | exact (B2 q Hq) ].
  - intros a Ha. apply AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha]; [ exact (N1 a Ha) | exact (N2 a Ha) ].
Qed.

(* Two substitutions that agree on the live atoms and rows have the same live clauses. *)
Lemma LiveG_agree : forall E F L LR D Dd S S',
  LiveG E F L LR D Dd S ->
  (forall a, a `in` L -> sT S' a = sT S a) -> (forall q, q `in` LR -> sR S' q = sR S q) ->
  LiveG E F L LR D Dd S'.
Proof.
  intros E F L LR D Dd S S' (Hs & Hq & (Ht & Hb) & Hn) Ea Er.
  refine (conj _ (conj _ (conj (conj _ _) _))).
  - intros a Ha. rewrite (Ea a Ha). exact (Hs a Ha).
  - intros q Hq'. rewrite (Er q Hq'). exact (Hq q Hq').
  - intros a Ha. rewrite (Ea a Ha). exact (Ht a Ha).
  - intros q Hq'. rewrite (Er q Hq'). exact (Hb q Hq').
  - intros a Ha. rewrite (Ea a Ha). exact (Hn a Ha).
Qed.

(* ---- the images of the live sets ---- *)

Definition limgT (s : sub) (L LR : atoms) : atoms :=
  limg s L `union`
  aset (flat_map (fun q => AtomSetImpl.elements (ftv_row (sR s q))) (AtomSetImpl.elements LR)).

Definition limgR (s : sub) (L LR : atoms) : atoms :=
  aset (flat_map (fun x => AtomSetImpl.elements (frv_typ (sT s x))) (AtomSetImpl.elements L)) `union`
  aset (flat_map (fun q => AtomSetImpl.elements (frv_row (sR s q))) (AtomSetImpl.elements LR)).

Lemma limgT_in : forall s L LR y, y `in` limgT s L LR <->
  (exists x, x `in` L /\ y `in` ftv_typ (sT s x)) \/ (exists q, q `in` LR /\ y `in` ftv_row (sR s q)).
Proof.
  intros s L LR y. unfold limgT. rewrite AtomSetFacts.union_iff, limg_in, aset_in, in_flat_map. split.
  - intros [H|(q & Hq & Hy)]; [ left; exact H | right; exists q; split; [ apply in_elts; exact Hq | apply in_elts; exact Hy ] ].
  - intros [H|(q & Hq & Hy)]; [ left; exact H | right; exists q; split; [ apply in_elts; exact Hq | apply in_elts; exact Hy ] ].
Qed.

Lemma limgR_in : forall s L LR y, y `in` limgR s L LR <->
  (exists x, x `in` L /\ y `in` frv_typ (sT s x)) \/ (exists q, q `in` LR /\ y `in` frv_row (sR s q)).
Proof.
  intros s L LR y. unfold limgR. rewrite AtomSetFacts.union_iff, !aset_in, !in_flat_map. split.
  - intros [(x & Hx & Hy)|(q & Hq & Hy)]; [ left; exists x; split; [ apply in_elts; exact Hx | apply in_elts; exact Hy ]
                                          | right; exists q; split; [ apply in_elts; exact Hq | apply in_elts; exact Hy ] ].
  - intros [(x & Hx & Hy)|(q & Hq & Hy)]; [ left; exists x; split; [ apply in_elts; exact Hx | apply in_elts; exact Hy ]
                                          | right; exists q; split; [ apply in_elts; exact Hq | apply in_elts; exact Hy ] ].
Qed.

Lemma limgT_mono : forall s L1 L2 LR1 LR2, L1 [<=] L2 -> LR1 [<=] LR2 ->
  limgT s L1 LR1 [<=] limgT s L2 LR2.
Proof.
  intros s L1 L2 LR1 LR2 Hl Hr y Hy. apply limgT_in in Hy. apply limgT_in.
  destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)]; [ left; exists x; split; [ apply Hl; exact Hx | exact Hy ]
                                                 | right; exists q; split; [ apply Hr; exact Hq | exact Hy ] ].
Qed.

Lemma limgR_mono : forall s L1 L2 LR1 LR2, L1 [<=] L2 -> LR1 [<=] LR2 ->
  limgR s L1 LR1 [<=] limgR s L2 LR2.
Proof.
  intros s L1 L2 LR1 LR2 Hl Hr y Hy. apply limgR_in in Hy. apply limgR_in.
  destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)]; [ left; exists x; split; [ apply Hl; exact Hx | exact Hy ]
                                                 | right; exists q; split; [ apply Hr; exact Hq | exact Hy ] ].
Qed.

(* What a step does to the live atoms and rows: their images are in the fragment
   over the atoms below the new supply, with every presence entry present under
   the extension.  This is the part of [Pkg] the next step reads; it is stated on
   the live set because the factoring through a step is. *)
Definition SIg (n n' : nat) (s S2 : sub) (L LR : atoms) : Prop :=
  n <= n' /\
  (forall x, x `in` L -> pf (sT s x) /\ atT n' (sT s x) /\ ps S2 (sT s x)) /\
  (forall q, q `in` LR -> prf (sR s q) /\ atR n' (sR s q) /\ psr S2 (sR s q)).

Lemma limgT_old : forall n n' s S2 L LR, SIg n n' s S2 L LR -> LOld n' (limgT s L LR).
Proof.
  intros n n' s S2 L LR (_ & Hx & Hq) y Hy. apply limgT_in in Hy.
  destruct Hy as [(x & Hx' & Hy)|(q & Hq' & Hy)].
  - exact (proj1 (proj1 (proj2 (Hx x Hx'))) y Hy).
  - exact (proj1 (proj1 (proj2 (Hq q Hq'))) y Hy).
Qed.

Lemma limgR_old : forall n n' s S2 L LR, SIg n n' s S2 L LR -> LOld n' (limgR s L LR).
Proof.
  intros n n' s S2 L LR (_ & Hx & Hq) y Hy. apply limgR_in in Hy.
  destruct Hy as [(x & Hx' & Hy)|(q & Hq' & Hy)].
  - exact (proj2 (proj1 (proj2 (Hx x Hx'))) y Hy).
  - exact (proj2 (proj1 (proj2 (Hq q Hq'))) y Hy).
Qed.

Lemma limgT_ev : forall s L LR, OkS s -> LEv L -> LEv LR -> LEv (limgT s L LR).
Proof.
  intros s L LR Hs HL HR y Hy. apply limgT_in in Hy. destruct Hs as (_ & Ht & Hr & _).
  destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)].
  - exact (proj1 (Ht x (HL x Hx)) y Hy).
  - exact (proj1 (Hr q (HR q Hq)) y Hy).
Qed.

Lemma limgR_ev : forall s L LR, OkS s -> LEv L -> LEv LR -> LEv (limgR s L LR).
Proof.
  intros s L LR Hs HL HR y Hy. apply limgR_in in Hy. destruct Hs as (_ & Ht & Hr & _).
  destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)].
  - exact (proj2 (Ht x (HL x Hx)) y Hy).
  - exact (proj2 (Hr q (HR q Hq)) y Hy).
Qed.

Lemma BndL_of_Bnd : forall E F L LR S, Bnd E F S -> BndL E F L LR S.
Proof.
  intros E F L LR S (H1 & H2 & H3 & H4). refine (conj _ _).
  - intros a _. exact (conj (H1 a) (H2 a)).
  - intros q _. exact (conj (H3 q) (H4 q)).
Qed.

Lemma BndL_mono : forall E F L1 L2 LR1 LR2 S, L1 [<=] L2 -> LR1 [<=] LR2 ->
  BndL E F L2 LR2 S -> BndL E F L1 LR1 S.
Proof.
  intros E F L1 L2 LR1 LR2 S Hl Hr (Ht & Hq). split.
  - intros a Ha. exact (Ht a (Hl a Ha)).
  - intros q Hq'. exact (Hq q (Hr q Hq')).
Qed.

(* ---- a step, on the live atoms and rows ---- *)

(* The step [s] from [Sg] to [S2]: [S2] respects the sorts and kinds the run ends
   with on the images of the live atoms, factors [Sg] through [s] on the live atoms
   and rows, and keeps every bound on the atoms the images of [Sg] mention. *)
Definition SemG (E F : atom -> Prop) (L LR : atoms) (DT : denv) (Sg : sub) (n : nat) (s : sub)
  (D' : denv) (n' : nat) (S2 : sub) : Prop :=
  DOk D' n' /\ Drow D' /\ LiveG E F (limgT s L LR) (limgR s L LR) D' DT S2 /\ SIg n n' s S2 L LR /\
  (forall x, x `in` L -> teq (sT Sg x) (apT S2 (sT s x))) /\
  (forall q, q `in` LR -> req (sR Sg q) (apR S2 (sR s q))) /\
  (forall E' F', BndL E' F' L LR Sg -> BndL E' F' (limgT s L LR) (limgR s L LR) S2) /\ OkS s.

Lemma SemG_DOk : forall E F L LR DT Sg n s D' n' S2, SemG E F L LR DT Sg n s D' n' S2 -> DOk D' n'.
Proof. intros E F L LR DT Sg n s D' n' S2 H. exact (proj1 H). Qed.

Lemma SemG_live : forall E F L LR DT Sg n s D' n' S2, SemG E F L LR DT Sg n s D' n' S2 ->
  LiveG E F (limgT s L LR) (limgR s L LR) D' DT S2.
Proof. intros E F L LR DT Sg n s D' n' S2 H. exact (proj1 (proj2 (proj2 H))). Qed.

Lemma SemG_SIg : forall E F L LR DT Sg n s D' n' S2, SemG E F L LR DT Sg n s D' n' S2 -> SIg n n' s S2 L LR.
Proof. intros E F L LR DT Sg n s D' n' S2 H. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.

Lemma SemG_OkS : forall E F L LR DT Sg n s D' n' S2, SemG E F L LR DT Sg n s D' n' S2 -> OkS s.
Proof. intros E F L LR DT Sg n s D' n' S2 H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))). Qed.

(* ---- the unifier's step ---- *)

(* The full substitution the unifier's completeness needs: [Sg] on the live type
   atoms and row variables, [Float] and the empty row elsewhere. *)
Definition restrG (L LR : atoms) (Sg : sub) : sub :=
  Sub (fun a => if AtomSetImpl.mem a L then sT Sg a else typ_Float)
      (fun q => if AtomSetImpl.mem q LR then sR Sg q else row_Empty).

Lemma restrG_in : forall L LR Sg a, a `in` L -> sT (restrG L LR Sg) a = sT Sg a.
Proof. intros L LR Sg a Ha. cbn [restrG sT]. rewrite (AtomSetImpl.mem_1 Ha). reflexivity. Qed.

Lemma restrG_rin : forall L LR Sg q, q `in` LR -> sR (restrG L LR Sg) q = sR Sg q.
Proof. intros L LR Sg q Hq. cbn [restrG sR]. rewrite (AtomSetImpl.mem_1 Hq). reflexivity. Qed.

Lemma rkok_empty : forall (Dd : denv) K, rkok Dd K row_Empty.
Proof. intros Dd K. split; [ exact (match rk_sort K with _ => I end) | intros l _; reflexivity ]. Qed.

Lemma KR_restrG : forall E F L LR (D DT : denv) Sg, LiveG E F L LR D DT Sg -> KR D DT (restrG L LR Sg).
Proof.
  intros E F L LR D DT Sg (Hs & Hq & _).
  split.
  - intros a. cbn [restrG sT]. destruct (AtomSetImpl.mem a L) eqn:E0.
    + exact (Hs a (AtomSetImpl.mem_2 E0)).
    + simpl. exact I.
  - intros r. cbn [restrG sR]. destruct (AtomSetImpl.mem r LR) eqn:E0.
    + exact (Hq r (AtomSetImpl.mem_2 E0)).
    + exact (rkok_empty DT _).
Qed.

Lemma Dsrt_restrG : forall E F L LR (D DT : denv) Sg, Drow D -> LiveG E F L LR D DT Sg ->
  Dsrt D (restrG L LR Sg).
Proof.
  intros E F L LR D DT Sg Hr (_ & _ & _ & Hn). split; [ exact Hr | ].
  intros y Hy R. cbn [restrG sT]. destruct (AtomSetImpl.mem y L) eqn:E0.
  - exact (Hn y (AtomSetImpl.mem_2 E0) Hy R).
  - discriminate.
Qed.

Lemma Bnd_restrG : forall E F L LR Sg, BndL E F L LR Sg -> Bnd E F (restrG L LR Sg).
Proof.
  intros E F L LR Sg (Ht & Hr). refine (conj _ (conj _ (conj _ _))).
  - intros z a Ha. cbn [restrG sT] in Ha. destruct (AtomSetImpl.mem z L) eqn:E0.
    + exact (proj1 (Ht z (AtomSetImpl.mem_2 E0)) a Ha).
    + simpl in Ha. fsetdec.
  - intros z q Hq. cbn [restrG sT] in Hq. destruct (AtomSetImpl.mem z L) eqn:E0.
    + exact (proj2 (Ht z (AtomSetImpl.mem_2 E0)) q Hq).
    + simpl in Hq. fsetdec.
  - intros r a Ha. cbn [restrG sR] in Ha. destruct (AtomSetImpl.mem r LR) eqn:E0.
    + exact (proj1 (Hr r (AtomSetImpl.mem_2 E0)) a Ha).
    + simpl in Ha. fsetdec.
  - intros r q Hq. cbn [restrG sR] in Hq. destruct (AtomSetImpl.mem r LR) eqn:E0.
    + exact (proj2 (Hr r (AtomSetImpl.mem_2 E0)) q Hq).
    + simpl in Hq. fsetdec.
Qed.

(* Whether an entry is present depends on the images of the variables the type mentions. *)
Lemma ps_agree : forall S S',
  (forall T, pf T -> (forall x, x `in` ftv_typ T -> sT S x = sT S' x) -> ps S T -> ps S' T) /\
  (forall R, prf R -> (forall x, x `in` ftv_row R -> sT S x = sT S' x) -> psr S R -> psr S' R).
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
    + destruct (pres_shape S P HP PP) as [-> | [v [-> Hv]]]; [ reflexivity | ].
      change (sT S' v = typ_Unit). rewrite <- (Hx v ltac:(simpl; fsetdec)). exact Hv.
    + apply IHT; [ exact HT | intros x Hx'; apply Hx; fsetdec | exact PT ].
    + apply IHR; [ exact HR | intros x Hx'; apply Hx; fsetdec | exact PR ].
Qed.

Lemma atT_sub : forall n L LR T, LOld n L -> LOld n LR -> ftv_typ T [<=] L -> frv_typ T [<=] LR -> atT n T.
Proof.
  intros n L LR T Ho Hr Hs Hq. split; [ intros x Hx; exact (Ho x (Hs x Hx)) | intros q Hq'; exact (Hr q (Hq q Hq')) ].
Qed.

Lemma EvT_sub : forall L LR T, LEv L -> LEv LR -> ftv_typ T [<=] L -> frv_typ T [<=] LR -> EvT T.
Proof.
  intros L LR T HL HR Hs Hq. split; [ intros x Hx; exact (HL x (Hs x Hx)) | intros q Hq'; exact (HR q (Hq q Hq')) ].
Qed.

(* The unifier W calls is complete on two types of the fragment over live atoms and
   rows whose images under [Sg] are one type: it succeeds from some fuel on, and
   the run's step from [Sg] is a [SemG]. *)
Theorem unify_stepG : forall E F (DT D : denv) Sg L LR T1 T2 n,
  DOk D n -> Drow D -> LOld n L -> LOld n LR -> LEv L -> LEv LR -> LiveG E F L LR D DT Sg ->
  pf T1 -> pf T2 ->
  ftv_typ T1 [<=] L -> frv_typ T1 [<=] LR -> ftv_typ T2 [<=] L -> frv_typ T2 [<=] LR ->
  ps Sg T1 -> ps Sg T2 -> teq (apT Sg T1) (apT Sg T2) ->
  exists s D' n' S2,
    Stable (fun f => unify_coD f D T1 T2 n = Some (s, D', nil, n')) /\
    SemG E F L LR DT Sg n s D' n' S2 /\
    Stable (fun f => unify_tD f D T1 T2 n = Some (s, D', n')) /\
    Pkg DT (restrG L LR Sg) n s D' n' S2.
Proof.
  intros E F DT D Sg L LR T1 T2 n Hd Hrow Ho Hro HLE HRE HL P1 P2 S1 Q1 S2 Q2 PS1 PS2 Heq.
  set (S := restrG L LR Sg).
  pose proof (KR_restrG E F L LR D DT Sg HL) as HK.
  pose proof (Dsrt_restrG E F L LR D DT Sg Hrow HL) as HDs.
  assert (Hagt : forall T, ftv_typ T [<=] L -> forall a, a `in` ftv_typ T -> sT S a = sT Sg a)
    by (intros T Hs a Ha; exact (restrG_in L LR Sg a (Hs a Ha))).
  assert (Hagr : forall T, frv_typ T [<=] LR -> forall q, q `in` frv_typ T -> sR S q = sR Sg q)
    by (intros T Hs q Hq; exact (restrG_rin L LR Sg q (Hs q Hq))).
  assert (Hap : forall T, ftv_typ T [<=] L -> frv_typ T [<=] LR -> apT S T = apT Sg T)
    by (intros T Hs Hq; unfold apT; apply ap_typ_ext; [ exact (Hagt T Hs) | exact (Hagr T Hq) ]).
  assert (Hps : forall T, pf T -> ftv_typ T [<=] L -> ps Sg T -> ps S T)
    by (intros T HT Hs PS; exact (proj1 (ps_agree Sg S) T HT (fun a Ha => eq_sym (Hagt T Hs a Ha)) PS)).
  rewrite <- (Hap T1 S1 Q1), <- (Hap T2 S2 Q2) in Heq.
  destruct (unify_tD_complete_full DT D S T1 T2 n Hd HDs HK P1 P2
              (atT_sub n L LR T1 Ho Hro S1 Q1) (atT_sub n L LR T2 Ho Hro S2 Q2)
              (Hps T1 P1 S1 PS1) (Hps T2 P2 S2 PS2) Heq)
    as (s & D' & n' & S3 & [f0 Hf0] & Pk).
  pose proof Pk as (Hl & Hd' & Ht' & Hk' & Fx & Fr & Cv).
  pose proof (unify_coD_stable f0 D T1 T2 n s D' n' (proj1 (Hf0 f0 (le_n f0)))) as [f1 Hf1].
  destruct (unify_coD_sound f1 D T1 T2 n s D' nil n' (Hf1 f1 (le_n f1)) Hd
              (EvT_sub L LR T1 HLE HRE S1 Q1) (EvT_sub L LR T2 HLE HRE S2 Q2)) as (Hok & _ & _).
  assert (Hbnd : forall E' F', BndL E' F' L LR Sg -> Bnd E' F' S3)
    by (intros E' F' HB; exact (Cv E' F' (Bnd_restrG E' F' L LR Sg HB))).
  assert (Hbl : forall E' F', BndL E' F' L LR Sg -> BndL E' F' (limgT s L LR) (limgR s L LR) S3)
    by (intros E' F' HB; exact (BndL_of_Bnd E' F' _ _ S3 (Hbnd E' F' HB))).
  exists s, D', n', S3. split; [ exists f1; exact Hf1 | ].
  split; [ | split; [ exists f0; intros f Hf; exact (proj1 (Hf0 f Hf)) | exact Pk ] ].
  assert (HSI : SIg n n' s S3 L LR).
  { refine (conj Hl (conj _ _)).
    - intros x Hx. destruct (Fx x (Ho x Hx)) as (A & B & C & _). exact (conj A (conj B C)).
    - intros q Hq. destruct (Fr q (Hro q Hq)) as (A & B & C & _). exact (conj A (conj B C)). }
  refine (conj Hd' (conj (proj1 Ht') (conj _ (conj HSI (conj _ (conj _ (conj Hbl Hok))))))).
  - destruct HL as (_ & _ & HB & _). pose proof (Hbnd E F HB) as (Bt & Bt2 & Br & Br2).
    refine (conj _ (conj _ (conj (conj _ _) _))).
    + intros a _. exact (proj1 Hk' a).
    + intros q _. exact (proj2 Hk' q).
    + intros a _. exact (conj (fun b Hb => Bt a b Hb) (fun q Hq => Bt2 a q Hq)).
    + intros q _. exact (conj (fun b Hb => Br q b Hb) (fun r Hr => Br2 q r Hr)).
    + intros a _. exact (proj2 Ht' a).
  - intros x Hx. rewrite <- (restrG_in L LR Sg x Hx). exact (proj2 (proj2 (proj2 (Fx x (Ho x Hx))))).
  - intros q Hq. rewrite <- (restrG_rin L LR Sg q Hq). exact (proj2 (proj2 (proj2 (Fr q (Hro q Hq))))).
Qed.

(* ---- presence atoms ---- *)

(* [S] sends the presence atoms [LP] to [Unit]. *)
Definition PLive (LP : atoms) (S : sub) : Prop := forall a, a `in` LP -> sT S a = typ_Unit.

(* The presence of each entry is [Unit] or an atom of [LP]. *)
Fixpoint psA (LP : atoms) (T : typ) {struct T} : Prop :=
  match T with
  | typ_Arrow A B => psA LP A /\ psA LP B
  | typ_Record R => psAr LP R
  | typ_Grp _ A => psA LP A
  | _ => True
  end
with psAr (LP : atoms) (R : row) {struct R} : Prop :=
  match R with
  | row_Ext _ T R' => psA LP T /\ psAr LP R'
  | row_Maybe _ P T R' => (P = typ_Unit \/ exists a, P = typ_Var a /\ a `in` LP) /\ psA LP T /\ psAr LP R'
  | _ => True
  end.

Lemma psA_ps : forall LP S,
  PLive LP S ->
  (forall T, psA LP T -> ps S T) /\ (forall R, psAr LP R -> psr S R).
Proof.
  intros LP S HP. apply typ_row_mutind; simpl; try (intros; exact I).
  - intros A IHA B IHB [HA HB]. split; [ exact (IHA HA) | exact (IHB HB) ].
  - intros R IH HR. exact (IH HR).
  - intros w A IH HA. exact (IH HA).
  - intros l T IHT R IHR [HT HR]. split; [ exact (IHT HT) | exact (IHR HR) ].
  - intros l P IHP T IHT R IHR [HPr [HT HR]]. refine (conj _ (conj (IHT HT) (IHR HR))).
    destruct HPr as [->|(a & -> & Ha)]; [ reflexivity | exact (HP a Ha) ].
Qed.

Lemma PLive_mono : forall LP1 LP2 S, LP1 [<=] LP2 -> PLive LP2 S -> PLive LP1 S.
Proof. intros LP1 LP2 S H HP a Ha. exact (HP a (H a Ha)). Qed.

Lemma PLive_union : forall LP1 LP2 S, PLive LP1 S -> PLive LP2 S -> PLive (LP1 `union` LP2) S.
Proof.
  intros LP1 LP2 S H1 H2 a Ha. apply AtomSetFacts.union_iff in Ha.
  destruct Ha as [Ha|Ha]; [ exact (H1 a Ha) | exact (H2 a Ha) ].
Qed.

Lemma PLive_empty : forall S, PLive {} S.
Proof. intros S a Ha. exfalso. revert Ha. fsetdec. Qed.

(* A presence atom of [LP], sent to [Unit] by [Sg], has an image under the step that
   the extension sends to [Unit], so the atoms of the images are presence atoms of
   [S2]. *)
Lemma PLive_step : forall LP Sg s S2,
  PLive LP Sg -> (forall a, a `in` LP -> pf (sT s a)) ->
  (forall a, a `in` LP -> teq (sT Sg a) (apT S2 (sT s a))) ->
  PLive (limg s LP) S2.
Proof.
  intros LP Sg s S2 HP Hpf Hf y Hy. apply limg_in in Hy. destruct Hy as (a & Ha & Hy).
  pose proof (Hf a Ha) as F. rewrite (HP a Ha) in F.
  pose proof (teq_Unit_inv _ F) as E.
  destruct (pres_shape S2 (sT s a) (Hpf a Ha) E) as [E1|(v & E1 & Hv)].
  - rewrite E1 in Hy. simpl in Hy. fsetdec.
  - rewrite E1 in Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst y. exact Hv.
Qed.

(* ---- the steps compose ---- *)

Lemma limg_scompG : forall s s' L LR,
  limgT (scomp s' s) L LR [<=] limgT s' (limgT s L LR) (limgR s L LR) /\
  limgR (scomp s' s) L LR [<=] limgR s' (limgT s L LR) (limgR s L LR).
Proof.
  intros s s' L LR. split.
  - intros y Hy. apply limgT_in in Hy. apply limgT_in.
    destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)].
    + change (y `in` ftv_typ (apT s' (sT s x))) in Hy.
      destruct (ftv_ap_typ _ _ _ _ Hy) as [(b & Hb & Hyb)|(p & Hp & Hyp)].
      * left. exists b. split; [ apply limgT_in; left; exists x; split; assumption | exact Hyb ].
      * right. exists p. split; [ apply limgR_in; left; exists x; split; assumption | exact Hyp ].
    + change (y `in` ftv_row (apR s' (sR s q))) in Hy.
      destruct (proj2 ftv_ap_mut _ _ _ _ Hy) as [(b & Hb & Hyb)|(p & Hp & Hyp)].
      * left. exists b. split; [ apply limgT_in; right; exists q; split; assumption | exact Hyb ].
      * right. exists p. split; [ apply limgR_in; right; exists q; split; assumption | exact Hyp ].
  - intros y Hy. apply limgR_in in Hy. apply limgR_in.
    destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)].
    + change (y `in` frv_typ (apT s' (sT s x))) in Hy.
      destruct (frv_ap_typ _ _ _ _ Hy) as [(b & Hb & Hyb)|(p & Hp & Hyp)].
      * left. exists b. split; [ apply limgT_in; left; exists x; split; assumption | exact Hyb ].
      * right. exists p. split; [ apply limgR_in; left; exists x; split; assumption | exact Hyp ].
    + change (y `in` frv_row (apR s' (sR s q))) in Hy.
      destruct (proj2 frv_ap_mut _ _ _ _ Hy) as [(b & Hb & Hyb)|(p & Hp & Hyp)].
      * left. exists b. split; [ apply limgT_in; right; exists q; split; assumption | exact Hyb ].
      * right. exists p. split; [ apply limgR_in; right; exists q; split; assumption | exact Hyp ].
Qed.

Lemma SemG_id : forall E F L LR DT Sg D n, DOk D n -> Drow D -> LOld n L -> LOld n LR ->
  LiveG E F L LR D DT Sg -> SemG E F L LR DT Sg n sid D n Sg.
Proof.
  intros E F L LR DT Sg D n Hd Hrow Ho Hro HL.
  assert (Hsub : limgT sid L LR [<=] L /\ limgR sid L LR [<=] LR).
  { split; intros y Hy.
    - apply limgT_in in Hy. destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)].
      + cbn [sT sid idt] in Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst y. exact Hx.
      + cbn [sR sid idr] in Hy. simpl in Hy. fsetdec.
    - apply limgR_in in Hy. destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)].
      + cbn [sT sid idt] in Hy. simpl in Hy. fsetdec.
      + cbn [sR sid idr] in Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst y. exact Hq. }
  refine (conj Hd (conj Hrow (conj (LiveG_mono _ _ _ _ _ _ _ _ _ (proj1 Hsub) (proj2 Hsub) HL)
            (conj _ (conj _ (conj _ (conj _ OkS_id))))))).
  - refine (conj (le_n n) (conj _ _)).
    + intros x Hx. cbn [sT sid idt]. exact (conj I (conj (atT_V DT n x (Ho x Hx)) I)).
    + intros q Hq. cbn [sR sid idr]. exact (conj I (conj (atR_V DT n q (Hro q Hq)) I)).
  - intros x _. cbn [sid sT idt]. change (teq (sT Sg x) (sT Sg x)). apply teq_refl.
  - intros q _. cbn [sid sR idr]. change (req (sR Sg q) (sR Sg q)). apply req_refl.
  - intros E' F' HB. exact (BndL_mono E' F' _ _ _ _ Sg (proj1 Hsub) (proj2 Hsub) HB).
Qed.

(* A type of the fragment over live atoms keeps its place under a step whose images
   of the live atoms are in the fragment, and factors through it. *)
Lemma SemG_ap_T : forall S1 S2 s' n1 n2 Lm LRm T,
  SIg n1 n2 s' S2 Lm LRm ->
  ftv_typ T [<=] Lm -> frv_typ T [<=] LRm -> pf T -> ps S1 T ->
  (forall y, y `in` Lm -> teq (sT S1 y) (apT S2 (sT s' y))) ->
  pf (apT s' T) /\ atT n2 (apT s' T) /\ ps S2 (apT s' T).
Proof.
  intros S1 S2 s' n1 n2 Lm LRm T (_ & Hx & Hq) Ht Hr HT PT Fx.
  refine (conj _ (conj _ _)).
  - apply (proj1 (pf_ap s')); [ exact HT | intros y Hy; exact (proj1 (Hx y (Ht y Hy)))
                              | intros q Hq'; exact (proj1 (Hq q (Hr q Hq'))) ].
  - apply atT_ap; [ intros y Hy; exact (proj1 (proj2 (Hx y (Ht y Hy))))
                  | intros q Hq'; exact (proj1 (proj2 (Hq q (Hr q Hq')))) ].
  - apply (proj1 (ps_pull S1 S2 s')); [ exact HT | exact PT
      | intros y Hy; exact (conj (Fx y (Ht y Hy)) (proj2 (proj2 (Hx y (Ht y Hy)))))
      | intros q Hq'; exact (proj2 (proj2 (Hq q (Hr q Hq')))) ].
Qed.

Lemma SemG_ap_R : forall S1 S2 s' n1 n2 Lm LRm R,
  SIg n1 n2 s' S2 Lm LRm ->
  ftv_row R [<=] Lm -> frv_row R [<=] LRm -> prf R -> psr S1 R ->
  (forall y, y `in` Lm -> teq (sT S1 y) (apT S2 (sT s' y))) ->
  prf (apR s' R) /\ atR n2 (apR s' R) /\ psr S2 (apR s' R).
Proof.
  intros S1 S2 s' n1 n2 Lm LRm R (_ & Hx & Hq) Ht Hr HR PR Fx.
  refine (conj _ (conj _ _)).
  - apply (proj2 (pf_ap s')); [ exact HR | intros y Hy; exact (proj1 (Hx y (Ht y Hy)))
                              | intros q Hq'; exact (proj1 (Hq q (Hr q Hq'))) ].
  - apply atR_ap; [ intros y Hy; exact (proj1 (proj2 (Hx y (Ht y Hy))))
                  | intros q Hq'; exact (proj1 (proj2 (Hq q (Hr q Hq')))) ].
  - apply (proj2 (ps_pull S1 S2 s')); [ exact HR | exact PR
      | intros y Hy; exact (conj (Fx y (Ht y Hy)) (proj2 (proj2 (Hx y (Ht y Hy)))))
      | intros q Hq'; exact (proj2 (proj2 (Hq q (Hr q Hq')))) ].
Qed.

(* A step followed by a step from the substitution it ends with.  The second
   step's live set [Lm] holds the images of the first and may hold more (the
   result types' atoms); [Hm] says [Sg]'s bounds reach the first step's end on
   [Lm], as the derivation's own bounds do for the types it adds. *)
Lemma SemG_comp : forall E F L LR Lm LRm DT Sg n s D1 n1 S1 s' D2 n2 S2,
  SemG E F L LR DT Sg n s D1 n1 S1 -> limgT s L LR [<=] Lm -> limgR s L LR [<=] LRm ->
  SemG E F Lm LRm DT S1 n1 s' D2 n2 S2 ->
  (forall E' F', BndL E' F' L LR Sg -> BndL E' F' Lm LRm S1) ->
  SemG E F L LR DT Sg n (scomp s' s) D2 n2 S2.
Proof.
  intros E F L LR Lm LRm DT Sg n s D1 n1 S1 s' D2 n2 S2
    (Hd1 & Hw1 & Hv1 & HI1 & Fx1 & Fr1 & Cv1 & Ok1) HsT HsR
    (Hd2 & Hw2 & Hv2 & HI2 & Fx2 & Fr2 & Cv2 & Ok2) Hm.
  destruct (limg_scompG s s' L LR) as [GT GR].
  destruct HI1 as (Hl1 & Hx1 & Hq1). pose proof HI2 as HI2'. destruct HI2 as (Hl2 & Hx2 & Hq2).
  assert (Tx : forall x, x `in` L -> ftv_typ (sT s x) [<=] Lm).
  { intros x Hx y Hy. apply HsT. apply limgT_in. left. exists x. split; assumption. }
  assert (Rx : forall x, x `in` L -> frv_typ (sT s x) [<=] LRm).
  { intros x Hx y Hy. apply HsR. apply limgR_in. left. exists x. split; assumption. }
  assert (Tq : forall q, q `in` LR -> ftv_row (sR s q) [<=] Lm).
  { intros q Hq y Hy. apply HsT. apply limgT_in. right. exists q. split; assumption. }
  assert (Rq : forall q, q `in` LR -> frv_row (sR s q) [<=] LRm).
  { intros q Hq y Hy. apply HsR. apply limgR_in. right. exists q. split; assumption. }
  refine (conj Hd2 (conj Hw2 (conj _ (conj _ (conj _ (conj _ (conj _ (OkS_comp _ _ Ok2 Ok1)))))))).
  - exact (LiveG_mono _ _ _ _ _ _ _ _ _
             (fun y Hy => limgT_mono s' _ _ _ _ HsT HsR y (GT y Hy))
             (fun y Hy => limgR_mono s' _ _ _ _ HsT HsR y (GR y Hy)) Hv2).
  - refine (conj (Nat.le_trans _ _ _ Hl1 Hl2) (conj _ _)).
    + intros x Hx. destruct (Hx1 x Hx) as (P & A & PS).
      exact (SemG_ap_T S1 S2 s' n1 n2 Lm LRm (sT s x) HI2' (Tx x Hx) (Rx x Hx) P PS Fx2).
    + intros q Hq. destruct (Hq1 q Hq) as (P & A & PS).
      exact (SemG_ap_R S1 S2 s' n1 n2 Lm LRm (sR s q) HI2' (Tq q Hq) (Rq q Hq) P PS Fx2).
  - intros x Hx. change (teq (sT Sg x) (apT S2 (apT s' (sT s x)))).
    eapply teq_trans; [ exact (Fx1 x Hx) | ].
    apply ap_factor; [ intros y Hy; exact (Fx2 y (Tx x Hx y Hy)) | intros q Hq; exact (Fr2 q (Rx x Hx q Hq)) ].
  - intros q Hq. change (req (sR Sg q) (apR S2 (apR s' (sR s q)))).
    eapply req_trans; [ exact (Fr1 q Hq) | ].
    apply ap_factor_row; [ intros y Hy; exact (Fx2 y (Tq q Hq y Hy)) | intros r Hr; exact (Fr2 r (Rq q Hq r Hr)) ].
  - intros E' F' HB.
    exact (BndL_mono E' F' _ _ _ _ S2 GT GR
             (BndL_mono E' F' _ _ _ _ S2 (limgT_mono s' _ _ _ _ HsT HsR) (limgR_mono s' _ _ _ _ HsT HsR)
                (Cv2 E' F' (Hm E' F' HB)))).
Qed.

(* ---- fresh atoms ---- *)

Lemma LiveG_env : forall E F L LR (D D' Dd : denv) S,
  LiveG E F L LR D Dd S -> (forall a, a `in` L -> D' a = D a) -> (forall q, q `in` LR -> drk D' q = drk D q) ->
  LiveG E F L LR D' Dd S.
Proof.
  intros E F L LR D D' Dd S (Hs & Hq & Hb & Hn) Ea Er.
  refine (conj _ (conj _ (conj Hb _))).
  - intros a Ha. rewrite (Ea a Ha). exact (Hs a Ha).
  - intros q Hq'. rewrite (Er q Hq'). exact (Hq q Hq').
  - intros a Ha. rewrite (Ea a Ha). exact (Hn a Ha).
Qed.

Lemma BndL_agree : forall E F L LR S S',
  BndL E F L LR S -> (forall a, a `in` L -> sT S' a = sT S a) -> (forall q, q `in` LR -> sR S' q = sR S q) ->
  BndL E F L LR S'.
Proof.
  intros E F L LR S S' (Ht & Hr) Ea Er. split.
  - intros a Ha. rewrite (Ea a Ha). exact (Ht a Ha).
  - intros q Hq. rewrite (Er q Hq). exact (Hr q Hq).
Qed.

(* A fresh type atom of sort [k] sent to [U] joins the live atoms when [U] satisfies
   the sort, mentions only atoms the bounds allow, and is no record at a sort
   [NN] keeps off records. *)
Lemma LiveG_fresh : forall E F L LR (D D' DT : denv) Sg n k U,
  LOld n L -> LiveG E F L LR D DT Sg -> sat DT k U ->
  (forall b, b `in` ftv_typ U -> E b) -> (forall q, q `in` frv_typ U -> F q) ->
  (NQ k -> forall R, U <> typ_Record R) ->
  D' (ea n) = k -> (forall a, a `in` L -> D' a = D a) -> (forall q, drk D' q = drk D q) ->
  LiveG E F (L `union` {{ ea n }}) LR D' DT (supd Sg (ea n) U).
Proof.
  intros E F L LR D D' DT Sg n k U Ho HL Hs HE HF HN Hk Hag Hdr.
  assert (Hne : forall a, a `in` L -> a <> ea n) by (intros a Ha E0; exact (Ho a Ha n (le_n n) E0)).
  pose proof (LiveG_agree E F L LR D DT Sg (supd Sg (ea n) U) HL
                (fun a Ha => supd_other Sg (ea n) U a (Hne a Ha)) (fun q _ => eq_refl)) as HL1.
  pose proof (LiveG_env E F L LR D D' DT _ HL1 Hag (fun q _ => Hdr q)) as HL2.
  destruct HL2 as (S2 & Q2 & (T2 & B2) & N2).
  refine (conj _ (conj _ (conj (conj _ B2) _))).
  - intros a Ha. apply AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha]; [ exact (S2 a Ha) | ].
    apply AtomSetFacts.singleton_iff in Ha. subst a. rewrite supd_same, Hk. exact Hs.
  - intros q Hq. exact (Q2 q Hq).
  - intros a Ha. apply AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha]; [ exact (T2 a Ha) | ].
    apply AtomSetFacts.singleton_iff in Ha. subst a. rewrite supd_same. exact (conj HE HF).
  - intros a Ha. apply AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha]; [ exact (N2 a Ha) | ].
    apply AtomSetFacts.singleton_iff in Ha. subst a. rewrite supd_same, Hk. exact HN.
Qed.

(* A fresh type atom: the identity step to the extended environment and substitution. *)
Lemma SemG_fresh : forall E F L LR DT D Sg n k U,
  DOk D n -> Drow D -> LOld n L -> LOld n LR -> LiveG E F L LR D DT Sg ->
  SemG E F L LR DT Sg n sid (upd D (ea n) k) (S n) (supd Sg (ea n) U).
Proof.
  intros E F L LR DT D Sg n k U Hd Hrow Ho Hro HL.
  assert (Hne : forall a, a `in` L -> a <> ea n) by (intros a Ha E0; exact (Ho a Ha n (le_n n) E0)).
  assert (Hsub : limgT sid L LR [<=] L /\ limgR sid L LR [<=] LR).
  { split; intros y Hy.
    - apply limgT_in in Hy. destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)].
      + cbn [sT sid idt] in Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst y. exact Hx.
      + cbn [sR sid idr] in Hy. simpl in Hy. fsetdec.
    - apply limgR_in in Hy. destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)].
      + cbn [sT sid idt] in Hy. simpl in Hy. fsetdec.
      + cbn [sR sid idr] in Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst y. exact Hq. }
  pose proof (LiveG_env E F L LR D (upd D (ea n) k) DT Sg HL
                (fun a Ha => upd_other D (ea n) k a (Hne a Ha)) (fun q _ => eq_refl)) as HL1.
  pose proof (LiveG_agree E F L LR _ DT Sg (supd Sg (ea n) U) HL1
                (fun a Ha => supd_other Sg (ea n) U a (Hne a Ha)) (fun q _ => eq_refl)) as HL2.
  refine (conj (DOk_upd D n k Hd) (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ OkS_id))))))).
  - intros r. cbn [upd drk]. exact (Hrow r).
  - exact (LiveG_mono _ _ _ _ _ _ _ _ _ (proj1 Hsub) (proj2 Hsub) HL2).
  - refine (conj (Nat.le_succ_diag_r n) (conj _ _)).
    + intros x Hx. cbn [sT sid idt].
      exact (conj I (conj (atT_V DT (S n) x (old_le n (S n) x (Nat.le_succ_diag_r n) (Ho x Hx))) I)).
    + intros q Hq. cbn [sR sid idr].
      exact (conj I (conj (atR_V DT (S n) q (old_le n (S n) q (Nat.le_succ_diag_r n) (Hro q Hq))) I)).
  - intros x Hx. cbn [sid sT idt]. change (teq (sT Sg x) (sT (supd Sg (ea n) U) x)).
    rewrite (supd_other Sg (ea n) U x (Hne x Hx)). apply teq_refl.
  - intros q Hq. cbn [sid sR idr]. change (req (sR Sg q) (sR (supd Sg (ea n) U) q)).
    cbn [supd sR]. apply req_refl.
  - intros E' F' HB.
    exact (BndL_agree E' F' _ _ Sg (supd Sg (ea n) U)
             (BndL_mono E' F' _ _ _ _ Sg (proj1 Hsub) (proj2 Hsub) HB)
             (fun a Ha => supd_other Sg (ea n) U a (Hne a (proj1 Hsub a Ha))) (fun q _ => eq_refl)).
Qed.

(* A fresh presence atom: a type atom of sort [Any] sent to [Unit]. *)
Lemma PLive_fresh : forall LP (Sg : sub) n,
  PLive LP Sg -> (forall a, a `in` LP -> a <> ea n) ->
  PLive (LP `union` {{ ea n }}) (supd Sg (ea n) typ_Unit).
Proof.
  intros LP Sg n HP Hne a Ha. apply AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha].
  - rewrite (supd_other Sg (ea n) typ_Unit a (Hne a Ha)). exact (HP a Ha).
  - apply AtomSetFacts.singleton_iff in Ha. subst a. apply supd_same.
Qed.

(* ---- what a run ends with ---- *)

(* The induction's conclusion over the fragment: the run succeeds from some fuel
   on, its step is a [SemG], its type is in the fragment with every entry present
   under the extension, and the equations it holds are ones [dis] discharges
   ([HOkC], GoatCompleteHeld.v).  [DoneG] is [Done] of GoatCompleteCore.v with the
   record-free clauses replaced and the held equations returned. *)
Definition DoneG (E F : atom -> Prop) (L LR : atoms) (D1 : denv) (G : ctx) (e : exp) (D : denv) (n : nat)
  (Sg : sub) (T1 : typ) : Prop :=
  exists s D' n' S2 T e' H,
    Stable (fun f => infer true f D G e n = Some (s, D', T, n', e', H)) /\
    SemG E F L LR D1 Sg n s D' n' S2 /\
    pf T /\ atT n' T /\ ps S2 T /\ EvT T /\ LiveG E F (ftv_typ T) (frv_typ T) D' D1 S2 /\
    HOkC S2 n' H /\ teq (apT S2 T) T1 /\ is_gen_value e' = is_gen_value e /\ let_open e' = let_open e.

Lemma DoneG_const : forall E F L LR D1 G e D n Sg T1 c,
  (forall f, infer true (S f) D G e n = Some (sid, D, c, n, e, nil)) ->
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) ->
  DOk D n -> Drow D -> LOld n L -> LOld n LR -> LiveG E F L LR D D1 Sg -> teq c T1 ->
  DoneG E F L LR D1 G e D n Sg T1.
Proof.
  intros E F L LR D1 G e D n Sg T1 c Hi Hc Hd Hrow Ho Hro HL Hteq.
  assert (Hnone : ftv_typ c [<=] {} /\ frv_typ c [<=] {}).
  { destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; simpl; split; fsetdec. }
  exists sid, D, n, Sg, c, e, nil.
  refine (conj _ (conj (SemG_id E F L LR D1 Sg D n Hd Hrow Ho Hro HL) _)).
  - exists 1. intros f Hf. destruct f as [|f]; [ lia | exact (Hi f) ].
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (Forall_nil _) (conj _ (conj eq_refl eq_refl)))))))).
    + destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; exact I.
    + split; intros y Hy; exfalso; [ pose proof (proj1 Hnone y Hy) as H0 | pose proof (proj2 Hnone y Hy) as H0 ]; revert H0; fsetdec.
    + destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; exact I.
    + split; intros y Hy; exfalso; [ pose proof (proj1 Hnone y Hy) as H0 | pose proof (proj2 Hnone y Hy) as H0 ]; revert H0; fsetdec.
    + exact (LiveG_mono _ _ _ _ _ _ _ _ _ (proj1 Hnone) (proj2 Hnone) (LiveG_empty E F D D1 Sg)).
    + change (teq (apT Sg c) T1).
      destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; exact Hteq.
Qed.
