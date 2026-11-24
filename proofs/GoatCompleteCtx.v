(* Completeness of algorithm W, stage 7.7: what the induction over the core
   carries (docs/design/phase7-proof-plan.md).

   The induction ([infer_complete_core], GoatCompleteCore.v) compares a run of
   [infer] with a derivation of a core term: a context [G] of the algorithm that
   the derivation's [G1] instantiates ([CI]), a set [L] of live atoms (the ones [G]
   and the pending types mention) and a substitution [Sg] that respects the sorts
   on [L] ([Live P L D D1 Sg]).  A run gives a step [SemL] to the derivation's
   side: the extension [S2] of [Sg] respects the sorts the run ends with on the
   images of the live atoms, [Sg] factors through the run's substitution at
   [teqD D1] on [L], and the type the run returns is [teqD D1] to the derivation's
   under [S2].  Nothing is asked of [Sg] off the live atoms: each call to the
   unifier ([unify_stepL]) rebuilds a full substitution ([restr]) that agrees
   with [Sg] on [L] and sends the other atoms to [Float], which satisfies every
   sort, and then reads the result back on the live atoms.  The allowed set [P]
   of images rides along: the unifier's extension invents no type ([Img]), and
   [Float] is in [P], so [P] holds of every image of the live atoms the run
   returns.

   A binding of the algorithm's context is a monotype, compared with the
   derivation's by [teqD], or a scheme the algorithm generalized ([gen_ren]),
   which the derivation's scheme instantiates ([SchI], [sch_leP]).  A scheme
   quantifies odd atoms, which a derivation's substitution never mentions, so
   the comparison reads the substitution with those atoms fixed ([sfix]).

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

(* The derivation's scheme [sd] is an instance of what the algorithm's [sc]
   becomes under [Sg]. *)
Definition SchI (D1 : denv) (Sg : sub) (sd sc : scheme) : Prop :=
  sch_leP D1 sd (apS (sfix (s_tq sc) Sg) sc).

(* The derivation's context holds, at each name, the type that the algorithm's
   is under [Sg], up to [teqD], or an instance of what its scheme becomes. *)
Definition CI (D1 : denv) (Sg : sub) (G1 G : ctx) : Prop :=
  Forall2 (fun b1 b => fst b1 = fst b /\
     ((exists T1 T, snd b1 = sch_mono T1 /\ snd b = sch_mono T /\ teqD D1 (apT Sg T) T1) \/
      SchI D1 Sg (snd b1) (snd b))) G1 G.

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

Lemma SOk_apS : forall n n' s sc, SI n n' s -> OkS s -> SOk n sc -> SOk n' (apS s sc).
Proof.
  intros n n' s sc HI Hs Hok. pose proof Hok as (Hw & Hr & Hrf & Hold). pose proof Hw as Hw0.
  destruct Hw0 as (Hq & Hqr & _).
  refine (conj (WfSch_ap s sc Hs Hw) (conj Hr (conj _ _))).
  - cbn [apS s_body]. apply rf_ap; [ exact Hrf | ].
    intros x Hx. destruct (in_dec_set x (s_tq sc)) as [Hxq|Hxq].
    + rewrite (OkS_fix_tq s sc Hs Hw x Hxq). exact I.
    + assert (Hf : x `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
      exact (proj1 (proj1 (proj2 HI) x (Hold x Hf))).
  - intros a Ha. unfold ftv_sch in Ha. cbn [apS s_body s_tq] in Ha.
    apply AtomSetFacts.diff_iff in Ha. destruct Ha as [Ha Hn].
    destruct (ftv_ap_rf s _ a Hrf Ha) as (x & Hx & Hax).
    destruct (in_dec_set x (s_tq sc)) as [Hxq|Hxq].
    + rewrite (OkS_fix_tq s sc Hs Hw x Hxq) in Hax. simpl in Hax.
      apply AtomSetFacts.singleton_iff in Hax. subst. contradiction.
    + assert (Hf : x `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
      exact (proj2 (proj1 (proj2 HI) x (Hold x Hf)) a Hax).
Qed.

Lemma GOk_apC : forall n n' s G, SI n n' s -> OkS s -> GOk n G -> GOk n' (apC s G).
Proof.
  intros n n' s G HI Hs H. rewrite apC_map. induction H as [|[y sc] G Hb _ IH]; simpl in *.
  - constructor.
  - constructor; [ | exact IH ]. exact (SOk_apS n n' s sc HI Hs Hb).
Qed.

Lemma CI_nil : forall D1 Sg, CI D1 Sg nil nil.
Proof. intros. constructor. Qed.

Lemma CI_cons : forall D1 Sg G1 G x T1 T,
  CI D1 Sg G1 G -> teqD D1 (apT Sg T) T1 ->
  CI D1 Sg ((x ~ sch_mono T1) ++ G1) ((x ~ sch_mono T) ++ G).
Proof.
  intros D1 Sg G1 G x T1 T H Ht. constructor; [ | exact H ].
  simpl. split; [ reflexivity | left; exists T1, T; repeat split; exact Ht ].
Qed.

Lemma CI_cons_sch : forall D1 Sg G1 G x sd sc,
  CI D1 Sg G1 G -> SchI D1 Sg sd sc ->
  CI D1 Sg ((x ~ sd) ++ G1) ((x ~ sc) ++ G).
Proof.
  intros D1 Sg G1 G x sd sc H Hs. constructor; [ | exact H ].
  simpl. split; [ reflexivity | right; exact Hs ].
Qed.

Lemma CI_dom : forall D1 Sg G1 G, CI D1 Sg G1 G -> dom G1 [=] dom G.
Proof.
  intros D1 Sg G1 G H. induction H as [|[x s1] [y s] G1 G [Hk _] _ IH]; simpl in *; [ reflexivity | ].
  subst y. rewrite IH. reflexivity.
Qed.

Lemma CI_uniq : forall D1 Sg G1 G, CI D1 Sg G1 G -> uniq G1 -> uniq G.
Proof.
  intros D1 Sg G1 G H. induction H as [|[x s1] [y s] G1 G [Hk _] Hrest IH]; intros Hu; simpl in *.
  - constructor.
  - subst y. inversion Hu; subst. constructor; [ exact (IH ltac:(assumption)) | ].
    rewrite <- (CI_dom _ _ _ _ Hrest). assumption.
Qed.

(* A name the derivation binds is bound by the algorithm, to a monotype the
   derivation's type is [teqD] to or to a scheme the derivation's is an instance
   of. *)
Lemma CI_lookup : forall D1 Sg G1 G x sc1,
  CI D1 Sg G1 G -> uniq G1 -> binds x sc1 G1 ->
  exists sc, lookup x G = Some sc /\
    ((exists T1 T, sc1 = sch_mono T1 /\ sc = sch_mono T /\ teqD D1 (apT Sg T) T1) \/ SchI D1 Sg sc1 sc).
Proof.
  intros D1 Sg G1 G x sc1 H. induction H as [|[y s1] [z sc] G1 G [Hk Hrel] _ IH]; intros Hu Hb.
  - inversion Hb.
  - simpl in *. subst z. apply binds_cons_1 in Hb. destruct Hb as [[Hxy Hs]|Hb].
    + subst x sc1. exists sc. split.
      * cbn [lookup]. destruct (Atom.eq_dec y y); [ reflexivity | contradiction ].
      * exact Hrel.
    + inversion Hu; subst.
      destruct (IH ltac:(assumption) Hb) as (sc' & Ea & Eb). exists sc'.
      split; [ | exact Eb ].
      cbn [lookup]. destruct (Atom.eq_dec x y) as [->|_]; [ | exact Ea ].
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

(* ---- a step, on the live atoms ---- *)

(* [Sg] factors through the step [s] by [S2], on the live atoms [L]; [S2]
   respects the sorts the run ends with, and sends the images of the live atoms
   to types [P] allows. *)
Definition SemL (P : typ -> Prop) (L : atoms) (DT : denv) (Sg : sub) (n : nat) (s : sub)
  (D' : denv) (n' : nat) (S2 : sub) : Prop :=
  rkres D' DT (sR S2) /\ Live P (limg s L) D' DT S2 /\ DOk D' n' /\ SI n n' s /\
  (forall x, x `in` L -> teqD DT (sT Sg x) (apT S2 (sT s x))) /\
  (forall q, old n q -> sR S2 q = sR Sg q) /\ OkS s.

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

Lemma SemL_OkS : forall P L DT Sg n s D' n' S2, SemL P L DT Sg n s D' n' S2 -> OkS s.
Proof. intros P L DT Sg n s D' n' S2 H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.

Arguments SemL_OkS {P L DT Sg n s D' n' S2} H.
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
  intros P L1 L2 DT Sg n s D' n' S2 Hsub (R & V & Hd & HI & F & Q & Ok).
  refine (conj R (conj (Live_mono _ _ _ _ _ _ (limg_mono s _ _ Hsub) V) (conj Hd (conj HI (conj _ (conj Q Ok)))))).
  intros x Hx. exact (F x (Hsub x Hx)).
Qed.

(* A step from a substitution that agrees with [Sg] on the live atoms, which lie
   below a smaller supply, is a step from [Sg]. *)
Lemma SemL_weaken : forall P L DT Sg Sg' n0 n1 s D' n' S2,
  n0 <= n1 -> LOld n0 L -> SemL P L DT Sg' n1 s D' n' S2 ->
  (forall x, x `in` L -> sT Sg' x = sT Sg x) -> (forall q, old n0 q -> sR Sg' q = sR Sg q) ->
  SemL P L DT Sg n0 s D' n' S2.
Proof.
  intros P L DT Sg Sg' n0 n1 s D' n' S2 Hl Ho (R & V & Hd & HI & F & Q & Ok) Ex Er.
  refine (conj R (conj V (conj Hd (conj (SI_weaken _ _ _ _ Hl HI) (conj _ (conj _ Ok)))))).
  - intros x Hx. rewrite <- (Ex x Hx). exact (F x Hx).
  - intros q Hq. rewrite <- (Er q Hq). exact (Q q (old_le _ _ _ Hl Hq)).
Qed.

Lemma SemL_id : forall P L DT Sg D n, rkres D DT (sR Sg) -> Live P L D DT Sg -> DOk D n ->
  SemL P L DT Sg n sid D n Sg.
Proof.
  intros P L DT Sg D n Hr HL Hd. refine (conj Hr (conj _ (conj Hd (conj (SI_id n) (conj _ (conj _ OkS_id)))))).
  - intros a Ha. exact (HL a (limg_sid L a Ha)).
  - intros x _. apply teqD_refl.
  - intros q _. reflexivity.
Qed.

(* A fresh variable of sort [k], sent to [U]. *)
Lemma SemL_fresh : forall P L DT D Sg n k U, rkres D DT (sR Sg) -> Live P L D DT Sg -> DOk D n ->
  LOld n L -> SemL P L DT Sg n sid (upd D (ea n) k) (S n) (supd Sg (ea n) U).
Proof.
  intros P L DT D Sg n k U Hr HL Hd Ho.
  refine (conj _ (conj _ (conj (DOk_upd D n k Hd) (conj (SI_id_le n (S n) (Nat.le_succ_diag_r n)) (conj _ (conj _ OkS_id)))))).
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
  intros P L Lm DT Sg n s D1 n1 S1 s' D2 n2 S2 Ho (R1 & V1 & Hd1 & I1 & F1 & Q1 & Ok1) Hsub
    (R2 & V2 & Hd2 & I2 & F2 & Q2 & Ok2).
  refine (conj R2 (conj _ (conj Hd2 (conj (SI_comp _ _ _ _ _ I1 I2) (conj _ (conj _ (OkS_comp _ _ Ok2 Ok1))))))).
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

Lemma GLive_apC : forall n n' s L G, SI n n' s -> OkS s -> GOk n G -> GLive L G ->
  GLive (limg s L) (apC s G).
Proof.
  intros n n' s L G HI Hs HG HL. rewrite apC_map. revert HG.
  induction HL as [|[y sc] G HT _ IH]; intros HG; simpl.
  - constructor.
  - inversion HG as [|b G' Hsc HG' Eb]; subst. simpl in *.
    destruct Hsc as (Hw & Hr & Hrf & Hold).
    constructor; [ | exact (IH HG') ].
    intros a Ha. unfold ftv_sch in Ha. cbn [apS s_body s_tq] in Ha.
    apply AtomSetFacts.diff_iff in Ha. destruct Ha as [Ha Hn].
    destruct (ftv_ap_rf s _ a Hrf Ha) as (x & Hx & Hax).
    destruct (in_dec_set x (s_tq sc)) as [Hxq|Hxq].
    + rewrite (OkS_fix_tq s sc Hs Hw x Hxq) in Hax. simpl in Hax.
      apply AtomSetFacts.singleton_iff in Hax. subst. contradiction.
    + assert (Hf : x `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
      apply limg_in. exists x. split; [ apply HT; exact Hf | exact Hax ].
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

(* The substitution may change off the live atoms. *)
Lemma CI_agree : forall D1 Sg Sg' G1 G L n, CI D1 Sg G1 G -> GOk n G -> GLive L G ->
  (forall a, a `in` L -> sT Sg' a = sT Sg a) -> CI D1 Sg' G1 G.
Proof.
  intros D1 Sg Sg' G1 G L n H. induction H as [|[x s1] [y s] G1 G [Hk Hrel] _ IH]; intros HO HG Hag.
  - constructor.
  - inversion HO as [|b G' Hsc HO' Eb]; subst.
    inversion HG as [|b2 G2 HL2 HG' Eb2]; subst. simpl in *. subst y.
    constructor; [ | exact (IH HO' HG' Hag) ].
    simpl. split; [ reflexivity | ]. destruct Hrel as [(T1 & T & E1 & E2 & Ht)|Hs].
    + left. exists T1, T. split; [ exact E1 | split; [ exact E2 | ] ].
      rewrite E2 in Hsc. pose proof (SOk_mono_inv _ _ Hsc) as HT.
      rewrite E2 in HL2. cbn [snd] in HL2.
      rewrite (apT_agree Sg' Sg T (proj1 HT) (fun a Ha => Hag a (HL2 a (proj2 (ftv_sch_mono T a) Ha)))). exact Ht.
    + right. unfold SchI in *. rewrite (apS_sfix_agree n L s Sg Sg' Hsc HL2 Hag). exact Hs.
Qed.

(* The run's step on the context: the derivation's bindings are still instances
   of the algorithm's, read at the extension. *)
Lemma CI_stepL : forall L D DT Sg n s D' n' S2 G1 G,
  SemL PEv L DT Sg n s D' n' S2 -> Live PEv L D DT Sg -> LEv L ->
  CI DT Sg G1 G -> GOk n G -> GLive L G ->
  CI DT S2 G1 (apC s G) /\ GOk n' (apC s G) /\ GLive (limg s L) (apC s G).
Proof.
  intros L D DT Sg n s D' n' S2 G1 G Hs HLv HLE HC HG HL.
  pose proof (SemL_OkS Hs) as Hok. pose proof (SemL_SI Hs) as HI.
  refine (conj _ (conj (GOk_apC _ _ _ _ HI Hok HG) (GLive_apC _ _ _ _ _ HI Hok HG HL))).
  rewrite apC_map. revert HG HL.
  induction HC as [|[x s1] [y sc] G1 G [Hk Hrel] _ IH]; intros HG HL.
  - constructor.
  - inversion HG as [|b G' Hsc HG' Eb]; subst.
    inversion HL as [|b2 G2 HL2 HL' Eb2]; subst. simpl in *. subst y.
    constructor; [ | exact (IH HG' HL') ].
    simpl. split; [ reflexivity | ].
    destruct Hrel as [(T1 & T & E1 & E2 & Ht)|Hsch].
    + left. rewrite E2 in Hsc. pose proof (SOk_mono_inv _ _ Hsc) as HT'.
      rewrite E2 in HL2. cbn [snd] in HL2.
      exists T1, (apT s T). split; [ exact E1 | split; [ rewrite E2; reflexivity | ] ].
      eapply teqD_trans; [ | exact Ht ]. apply teqD_sym.
      exact (SemL_factor PEv L DT Sg n s D' n' S2 T Hs (proj1 HT')
               (fun a Ha => HL2 a (proj2 (ftv_sch_mono T a) Ha))).
    + right. unfold SchI in *. change (s_tq (apS s sc)) with (s_tq sc).
      assert (Heq : apS (sfix (s_tq sc) S2) (apS s sc) = apS (sfix (s_tq sc) Sg) sc).
      { destruct Hsc as (Hw & Hr & Hrf & Hold). unfold apS. cbn [s_tq s_rq s_sk s_rk s_body].
        f_equal. rewrite apT_comp. apply apT_agree; [ exact Hrf | ].
        intros b Hb. change (sT (scomp (sfix (s_tq sc) S2) s) b) with (apT (sfix (s_tq sc) S2) (sT s b)).
        destruct (in_dec_set b (s_tq sc)) as [Hq|Hq].
        - rewrite (OkS_fix_tq s sc Hok Hw b Hq).
          change (sT (sfix (s_tq sc) S2) b = sT (sfix (s_tq sc) Sg) b).
          rewrite !sfix_in by exact Hq. reflexivity.
        - rewrite sfix_out by exact Hq.
          assert (Hbf : b `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
          pose proof (proj1 (proj2 HI) b (Hold b Hbf)) as [Hrb _].
          assert (Hag : apT (sfix (s_tq sc) S2) (sT s b) = apT S2 (sT s b)).
          { apply apT_agree; [ exact Hrb | ]. intros c Hc. apply sfix_out. intro Hcq.
            assert (Hcl : c `in` limg s L) by (apply limg_in; exists b; split; [ exact (HL2 b Hbf) | exact Hc ]).
            exact (ev_od c (limg_ev s L Hok HLE c Hcl) ((proj1 Hw) c Hcq)). }
          rewrite Hag.
          pose proof (SemL_F Hs b (HL2 b Hbf)) as Hf.
          pose proof (proj2 (HLv b (HL2 b Hbf))) as Hpb.
          exact (teqD_rf_eq _ _ _ (proj2 Hpb) Hf). }
      rewrite Heq. exact Hsch.
Qed.

(* The atoms the images of the live atoms mention stay in the set the derivation
   hands the next premise: the old ones by the factoring through the step, the
   result type's by its equality with the derivation's. *)
Lemma Avoid_next : forall B B' L D DT Sg n s D1 n1 S1 T Tp,
  LOld n L -> Avoid B L Sg -> Live PEv L D DT Sg -> SemL PEv L DT Sg n s D1 n1 S1 ->
  TOk n1 T -> Live PEv (ftv_typ T) D1 DT S1 -> teqD DT (apT S1 T) Tp ->
  B [<=] B' -> ftv_typ Tp [<=] B' -> Avoid B' (lnext s L T) S1.
Proof.
  intros B B' L D DT Sg n s D1 n1 S1 T Tp Ho HAv HLv Hs HT LvT Heq Hb HTp x Hx.
  unfold lnext in Hx. apply AtomSetFacts.union_iff in Hx. destruct Hx as [Hx|Hx].
  - apply limg_in in Hx. destruct Hx as (y & Hy & Hxy).
    pose proof (proj1 (proj2 (SemL_SI Hs)) y (Ho y Hy)) as [Hrf _].
    pose proof (SemL_F Hs y Hy) as Hf.
    pose proof (proj2 (HLv y Hy)) as Hpy.
    assert (Heq2 : apT S1 (sT s y) = sT Sg y) by exact (teqD_rf_eq _ _ _ (proj2 Hpy) Hf).
    intros z Hz. apply Hb. apply (HAv y Hy). rewrite <- Heq2.
    exact (ftv_ap_in1 (sT S1) (sR S1) (sT s y) z x Hxy Hz).
  - intros z Hz. apply HTp.
    assert (Hrf : rf (apT S1 T)).
    { apply rf_ap; [ exact (proj1 HT) | intros w Hw; exact (proj2 (proj2 (LvT w Hw))) ]. }
    rewrite (teqD_rf_eq _ _ _ Hrf Heq). exact (ftv_ap_in1 (sT S1) (sR S1) T z x Hx Hz).
Qed.

Lemma next_facts : forall Dd Gd D Sg n L s D1 n1 S1 T G,
  LOld n L -> LEv L -> Live PEv L D Dd Sg -> SemL PEv L Dd Sg n s D1 n1 S1 -> TOk n1 T -> EvT T ->
  Live PEv (ftv_typ T) D1 Dd S1 ->
  GOk n G -> GLive L G -> CI Dd Sg Gd G ->
  LOld n1 (lnext s L T) /\ LEv (lnext s L T) /\ Live PEv (lnext s L T) D1 Dd S1 /\ GOk n1 (apC s G) /\
  GLive (lnext s L T) (apC s G) /\ CI Dd S1 Gd (apC s G).
Proof.
  intros Dd Gd D Sg n L s D1 n1 S1 T G Ho HLE HLv Hs HT HE Lv HG HL HC.
  destruct (CI_stepL L D Dd Sg n s D1 n1 S1 Gd G Hs HLv HLE HC HG HL) as (HC1 & HG1 & HL1).
  refine (conj (LOld_union _ _ _ (limg_old _ _ _ _ Ho (SemL_SI Hs)) (LOld_ftv _ _ HT))
            (conj (LEv_next s L T (SemL_OkS Hs) HLE HE) (conj _ (conj HG1 (conj _ HC1))))).
  - exact (Live_union _ _ _ _ _ _ (SemL_live Hs) Lv).
  - exact (GLive_mono _ _ _ (limg_lnext s L T) HL1).
Qed.

(* The full substitution the unifier's completeness needs: [Sg] on the live
   atoms, and [Float], which satisfies every sort, elsewhere. *)
Definition restr (L : atoms) (Sg : sub) : sub :=
  Sub (fun a => if AtomSetImpl.mem a L then sT Sg a else typ_Float) (sR Sg).

Lemma restr_in : forall L Sg a, a `in` L -> sT (restr L Sg) a = sT Sg a.
Proof. intros L Sg a Ha. cbn [restr sT]. rewrite (AtomSetImpl.mem_1 Ha). reflexivity. Qed.

Lemma EvT_rf_live : forall L T, rf T -> LEv L -> ftv_typ T [<=] L -> EvT T.
Proof.
  intros L T Hr HL Hs. split.
  - intros a Ha. exact (HL a (Hs a Ha)).
  - intros a Ha. exfalso. exact (proj1 (proj2 (proj2 (rf_facts T Hr))) a Ha).
Qed.

Lemma unify_stepL : forall P DT D Sg L T1 T2 n,
  P typ_Float -> DOk D n -> RA D -> LOld n L -> LEv L -> Live P L D DT Sg ->
  rf T1 -> rf T2 -> ftv_typ T1 [<=] L -> ftv_typ T2 [<=] L ->
  teqD DT (apT Sg T1) (apT Sg T2) ->
  exists s D' n' S2,
    Stable (fun f => unify_coD f D T1 T2 n = Some (s, D', nil, n')) /\
    SemL P L DT Sg n s D' n' S2 /\ RA D'.
Proof.
  intros P DT D Sg L T1 T2 n HPI Hd HRA Ho HLE HL R1 R2 S1 S2 Heq.
  pose proof (rkres_RA D DT (sR Sg) HRA) as Hr.
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
  pose proof (unify_coD_stable f0 D T1 T2 n s D' n' (Hf0 f0 (le_n f0))) as St.
  destruct St as [f1 Hf1].
  destruct (unify_coD_sound f1 D T1 T2 n s D' nil n' (Hf1 f1 (le_n f1)) Hd
              (EvT_rf_live L T1 R1 HLE S1) (EvT_rf_live L T2 R2 HLE S2)) as (Hok & _ & _).
  destruct (unify_tD_rf_drk f0 D T1 T2 n s D' n' (Hf0 f0 (le_n f0)) R1 R2) as [Hdrk _].
  exists s, D', n', S3. split; [ | split ].
  - exists f1. exact Hf1.
  - refine (conj (proj2 K) (conj _ (conj Hd' (conj HI (conj _ (conj Q Hok)))))).
    + intros a _. exact (conj (proj1 K a) (Img_bound P _ S3 Im HPall a)).
    + intros x Hx. rewrite <- (restr_in L Sg x Hx). exact (F x (Ho x Hx)).
  - exact (RA_of_drk D D' Hdrk HRA).
Qed.

