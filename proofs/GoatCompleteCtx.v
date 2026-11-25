(* Completeness of algorithm W, stage 7.7: what the induction over the core
   carries (docs/design/phase7-proof-plan.md).

   The induction ([infer_complete_core], GoatCompleteCoreW.v) carries a set [L] of
   live atoms (the ones the context and the pending types mention) and a
   substitution [Sg] that respects the sorts on [L] ([Live P L D D1 Sg]); [P] is
   the allowed set of images.  Nothing is asked of [Sg] off the live atoms.

   A binding of the algorithm's context is a monotype or a scheme the algorithm
   generalized ([gen_ren]).  A scheme quantifies odd atoms, which a derivation's
   substitution never mentions, so the comparison reads the substitution with
   those atoms fixed ([sfix]).  The comparison itself, [CIT], and the step of the
   run are in GoatCompleteCtxT.v and GoatCompleteCtxW.v.

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
Require Import Goat.GoatInferGen.
Require Import Goat.GoatCompleteInst.
Require Import Goat.GoatCompleteMono.
Require Import Goat.GoatCompleteDrk.
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


(* A record-free type is [teqD] to itself only: the environment reads rows, and
   there are none. *)
Definition var_of (T : typ) : option atom :=
  match T with typ_Var a => Some a | _ => None end.

Lemma teq_var_of : forall T1 T2, teq T1 T2 -> var_of T1 = var_of T2.
Proof. induction 1; simpl in *; congruence. Qed.

Lemma teqD_Var_inv : forall D a T, teqD D (typ_Var a) T -> T = typ_Var a.
Proof.
  intros D a T H. unfold teqD in H. cbn [nfT] in H. apply teq_var_of in H.
  destruct T; cbn [nfT var_of] in H; try discriminate H.
  injection H as H. subst. reflexivity.
Qed.

Lemma teqD_rf_eq : forall D T T', rf T -> teqD D T T' -> T' = T.
Proof.
  intros D T. induction T; intros T' Hrf H; simpl in Hrf; try contradiction.
  - exact (teqD_Int_inv _ _ H).
  - exact (teqD_Float_inv _ _ H).
  - exact (teqD_Bool_inv _ _ H).
  - exact (teqD_Unit_inv _ _ H).
  - exact (teqD_String_inv _ _ H).
  - destruct Hrf as [R1 R2]. destruct (teqD_Arrow_inv _ _ _ _ H) as (A' & B' & -> & H1 & H2).
    rewrite (IHT1 A' R1 H1), (IHT2 B' R2 H2). reflexivity.
  - exact (teqD_Var_inv _ _ _ H).
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

(* A binding of the algorithm's context is a scheme, well formed ([WfSch]: odd
   quantified atoms, even free atoms), over a record-free body, with no
   quantified row variable, whose free atoms lie below the supply. *)
Definition SOk (n : nat) (sc : scheme) : Prop :=
  WfSch sc /\ s_rq sc [=] {} /\ rf (s_body sc) /\ (forall a, a `in` ftv_sch sc -> old n a).

Definition GOk (n : nat) (G : ctx) : Prop := Forall (fun b => SOk n (snd b)) G.

Lemma ftv_sch_mono : forall T, ftv_sch (sch_mono T) [=] ftv_typ T.
Proof. intros T. unfold ftv_sch. cbn [sch_mono s_body s_tq]. fsetdec. Qed.

Lemma SOk_mono : forall n T, TOk n T -> EvT T -> SOk n (sch_mono T).
Proof.
  intros n T [H1 H2] HE. refine (conj (WfSch_mono T HE) (conj _ (conj H1 _))).
  - cbn [sch_mono s_rq]. fsetdec.
  - intros a Ha. apply H2. apply (proj1 (ftv_sch_mono _ _)). exact Ha.
Qed.

Lemma SOk_mono_inv : forall n T, SOk n (sch_mono T) -> TOk n T.
Proof.
  intros n T (_ & _ & H1 & H2). split; [ exact H1 | ].
  intros a Ha. apply H2. apply (proj2 (ftv_sch_mono _ _)). exact Ha.
Qed.

Lemma SOk_mono_ev : forall n T, SOk n (sch_mono T) -> EvT T.
Proof.
  intros n T ((_ & _ & H1 & H2) & _). split.
  - intros a Ha. apply H1. unfold ftv_sch. cbn [sch_mono s_body s_tq]. fsetdec.
  - intros a Ha. apply H2. unfold frv_sch. cbn [sch_mono s_body s_rq]. fsetdec.
Qed.

(* The fixing of the atoms a scheme quantifies: a derivation's substitution has
   no business with them, and the algorithm's context holds them odd. *)
Definition sfix (q : atoms) (S : sub) : sub :=
  Sub (fun a => if AtomSetImpl.mem a q then typ_Var a else sT S a) (sR S).

Lemma sfix_in : forall q S a, a `in` q -> sT (sfix q S) a = typ_Var a.
Proof. intros q S a Ha. cbn [sfix sT]. rewrite (AtomSetImpl.mem_1 Ha). reflexivity. Qed.

Lemma sfix_out : forall q S a, a `notin` q -> sT (sfix q S) a = sT S a.
Proof.
  intros q S a Ha. cbn [sfix sT]. destruct (AtomSetImpl.mem a q) eqn:E; [ | reflexivity ].
  exfalso. apply Ha. apply AtomSetFacts.mem_iff. exact E.
Qed.

Lemma GOk_nil : forall n, GOk n nil.
Proof. intros n. constructor. Qed.

Lemma GOk_cons : forall n x T G, TOk n T -> EvT T -> GOk n G -> GOk n ((x ~ sch_mono T) ++ G).
Proof. intros n x T G HT HE HG. constructor; [ exact (SOk_mono n T HT HE) | exact HG ]. Qed.

Lemma GOk_cons_sch : forall n x sc G, SOk n sc -> GOk n G -> GOk n ((x ~ sc) ++ G).
Proof. intros n x sc G Hs HG. constructor; [ exact Hs | exact HG ]. Qed.

Lemma SOk_mono_le : forall n n' sc, n <= n' -> SOk n sc -> SOk n' sc.
Proof.
  intros n n' sc Hl (H1 & H2 & H3 & H4). refine (conj H1 (conj H2 (conj H3 _))).
  intros a Ha. exact (old_le _ _ _ Hl (H4 a Ha)).
Qed.

Lemma GOk_mono : forall n n' G, n <= n' -> GOk n G -> GOk n' G.
Proof.
  intros n n' G Hl H. induction H as [|b G Hb _ IH]; constructor.
  - exact (SOk_mono_le _ _ _ Hl Hb).
  - exact IH.
Qed.

Lemma apS_mono : forall s T, apS s (sch_mono T) = sch_mono (apT s T).
Proof. reflexivity. Qed.

(* A step that is [OkS] fixes the odd atoms a scheme quantifies. *)
Lemma OkS_fix_tq : forall s sc, OkS s -> WfSch sc -> forall a, a `in` s_tq sc -> sT s a = typ_Var a.
Proof.
  intros s sc Hs (Hq & _) a Ha. destruct Hs as [_ [_ [_ [Hfx _]]]].
  exact (Hfx a (not_ev_od a (Hq a Ha))).
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

(* The live atoms are even: every atom the algorithm's types and context
   mention is. *)
Definition LEv (L : atoms) : Prop := forall a, a `in` L -> ev a.

Lemma LEv_empty : LEv {}.
Proof. intros a Ha. exfalso. revert Ha. fsetdec. Qed.

Lemma LEv_union : forall L1 L2, LEv L1 -> LEv L2 -> LEv (L1 `union` L2).
Proof.
  intros L1 L2 H1 H2 a Ha. apply AtomSetFacts.union_iff in Ha.
  destruct Ha as [Ha|Ha]; [ exact (H1 a Ha) | exact (H2 a Ha) ].
Qed.

Lemma LEv_sub : forall L1 L2, L1 [<=] L2 -> LEv L2 -> LEv L1.
Proof. intros L1 L2 H Hl a Ha. exact (Hl a (H a Ha)). Qed.

Lemma LEv_fresh : forall n L, LEv L -> LEv (L `union` {{ ea n }}).
Proof.
  intros n L H. apply LEv_union; [ exact H | ].
  intros a Ha. apply AtomSetFacts.singleton_iff in Ha. subst. apply ev_ea.
Qed.

Lemma LEv_ftv : forall T, EvT T -> LEv (ftv_typ T).
Proof. intros T [H _] a Ha. exact (H a Ha). Qed.

Lemma limg_ev : forall s L, OkS s -> LEv L -> LEv (limg s L).
Proof.
  intros s L Hs HL y Hy. apply limg_in in Hy. destruct Hy as (x & Hx & Hy).
  destruct Hs as [_ [Ht _]]. exact (proj1 (Ht x (HL x Hx)) y Hy).
Qed.

Lemma LEv_next : forall s L T, OkS s -> LEv L -> EvT T -> LEv (lnext s L T).
Proof.
  intros s L T Hs HL HT. apply LEv_union; [ exact (limg_ev s L Hs HL) | exact (LEv_ftv T HT) ].
Qed.

(* The atoms of the images of the live atoms stay inside a given set: the atoms
   a binder generalizes are chosen outside it. *)
Definition Avoid (B : atoms) (L : atoms) (Sg : sub) : Prop :=
  forall x, x `in` L -> ftv_typ (sT Sg x) [<=] B.

Lemma Avoid_mono : forall B B' L Sg, B [<=] B' -> Avoid B L Sg -> Avoid B' L Sg.
Proof. intros B B' L Sg Hb H x Hx y Hy. apply Hb. exact (H x Hx y Hy). Qed.

Lemma Avoid_sub : forall B L L' Sg, L' [<=] L -> Avoid B L Sg -> Avoid B L' Sg.
Proof. intros B L L' Sg Hl H x Hx. exact (H x (Hl x Hx)). Qed.

Lemma Avoid_empty : forall B Sg, Avoid B {} Sg.
Proof. intros B Sg x Hx. exfalso. revert Hx. fsetdec. Qed.

Lemma Avoid_fresh : forall B n L Sg U, LOld n L -> Avoid B L Sg -> ftv_typ U [<=] B ->
  Avoid B (L `union` {{ ea n }}) (supd Sg (ea n) U).
Proof.
  intros B n L Sg U Ho H HU x Hx. apply AtomSetFacts.union_iff in Hx. destruct Hx as [Hx|Hx].
  - rewrite supd_other by (intro E; exact (Ho x Hx n (le_n n) E)). exact (H x Hx).
  - apply AtomSetFacts.singleton_iff in Hx. subst x. rewrite supd_same. exact HU.
Qed.

Lemma Avoid_agree : forall B L Sg Sg', Avoid B L Sg -> (forall a, a `in` L -> sT Sg' a = sT Sg a) ->
  Avoid B L Sg'.
Proof. intros B L Sg Sg' H Ha x Hx. rewrite (Ha x Hx). exact (H x Hx). Qed.

Lemma apT_agree : forall S S' T, rf T ->
  (forall a, a `in` ftv_typ T -> sT S a = sT S' a) -> apT S T = apT S' T.
Proof.
  intros S S' T. induction T; simpl; intros H Hn; try contradiction; try reflexivity.
  - destruct H as [H1 H2]. rewrite !apT_Arrow.
    rewrite (IHT1 H1 (fun a Ha => Hn a ltac:(fsetdec))), (IHT2 H2 (fun a Ha => Hn a ltac:(fsetdec))).
    reflexivity.
  - rewrite !apT_Var. apply Hn. fsetdec.
Qed.

(* ---- the contexts, on the live atoms ---- *)

(* The types of the context's bindings lie over live atoms. *)
Definition GLive (L : atoms) (G : ctx) : Prop :=
  Forall (fun b => ftv_sch (snd b) [<=] L) G.

Lemma GLive_nil : forall L, GLive L nil.
Proof. intros L. constructor. Qed.

Lemma GLive_cons : forall L x T G, ftv_typ T [<=] L -> GLive L G -> GLive L ((x ~ sch_mono T) ++ G).
Proof.
  intros L x T G HT HG. constructor; [ | exact HG ].
  intros a Ha. apply HT. apply (proj1 (ftv_sch_mono _ _)). exact Ha.
Qed.

Lemma GLive_cons_sch : forall L x sc G, ftv_sch sc [<=] L -> GLive L G -> GLive L ((x ~ sc) ++ G).
Proof. intros L x sc G Hs HG. constructor; [ exact Hs | exact HG ]. Qed.

Lemma GLive_mono : forall L1 L2 G, L1 [<=] L2 -> GLive L1 G -> GLive L2 G.
Proof.
  intros L1 L2 G Hl H. induction H as [|b G HT _ IH]; constructor.
  - intros a Ha. apply Hl. apply HT. exact Ha.
  - exact IH.
Qed.

Lemma GLive_lookup : forall L G x sc, GLive L G -> lookup x G = Some sc -> ftv_sch sc [<=] L.
Proof.
  intros L G x sc H. induction H as [|[y s0] G HT _ IH]; intros Hl; [ discriminate Hl | ].
  cbn [lookup] in Hl. destruct (Atom.eq_dec x y) as [_|_].
  - injection Hl as Hl. subst s0. exact HT.
  - exact (IH Hl).
Qed.

(* A scheme's comparison reads the substitution on the atoms it keeps free,
   which are live. *)
Lemma apS_sfix_agree : forall n L sc Sg Sg', SOk n sc -> ftv_sch sc [<=] L ->
  (forall a, a `in` L -> sT Sg' a = sT Sg a) ->
  apS (sfix (s_tq sc) Sg') sc = apS (sfix (s_tq sc) Sg) sc.
Proof.
  intros n L sc Sg Sg' (_ & _ & Hrf & _) Hl Hag. unfold apS. cbn [s_tq s_rq s_sk s_rk].
  f_equal. apply apT_agree; [ exact Hrf | ].
  intros a Ha. destruct (in_dec_set a (s_tq sc)) as [Hq|Hq].
  - rewrite !sfix_in by exact Hq. reflexivity.
  - rewrite !sfix_out by exact Hq. apply Hag. apply Hl.
    unfold ftv_sch. apply AtomSetFacts.diff_iff. split; assumption.
Qed.
