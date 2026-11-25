(* Completeness of algorithm W, stage 7.8h: the induction's invariants past the
   record-free fragment (docs/design/phase7-proof-plan.md).

   GoatCompleteCtxW.v states the core's invariants for record-free types: a step
   is a [SemC], the context's bodies are [rf] with no quantified row, no row
   variable is live.  A record turns each into its fragment form.

   - A step is [SemW evA evA] (GoatCompleteBound.v) itself: its [SIg] says the
     images of the live atoms and live row variables are in the fragment
     ([pf]), below the new supply ([atT]), with every presence entry present
     under the extension ([ps]); [LiveG evA evA] is the live clause, with the
     evenness of what the images mention.  [DoneG evA evA]
     (GoatCompleteLive.v) is the conclusion, and returns the equations the run
     holds ([HOkC]).
   - A scheme of the algorithm's context may quantify rows.  A derivation's
     substitution has no business with the atoms and rows a scheme quantifies
     ([sfixS] fixes both), and the comparison [SchIP] reads it through that.
   - [SOkP], [GOkP], [GLiveP] and [GPsP] are [SOk], [GOk], [GLive] and [GPsT]
     over live rows and the fragment: the context's bodies are [pf], its free
     atoms and rows lie below the supply and inside the live sets, and every
     entry of a body is present under the extension that fixes its
     quantifiers.
   - [CI_stepP] is [CI_stepW] on these: it carries [GPsP] through the step with
     [ps_pull] (GoatCompleteRfRows.v), which moves the presence of an entry
     along a step that factors the old substitution through the new.

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
Require Import Goat.GoatInferGen.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferW.
Require Import Goat.GoatHeld.
Require Import Goat.GoatCompleteHeld.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteRewrite.
Require Import Goat.GoatCompleteInst.
Require Import Goat.GoatCompleteGen.
Require Import Goat.GoatCompleteMono.
Require Import Goat.GoatCompleteDrk.
Require Import Goat.GoatCompleteEr.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteLive.
Require Import Goat.GoatCompleteLiveRf.
Require Import Goat.GoatCompleteBound.
Require Import Goat.GoatCompleteSchT.
Require Import Goat.GoatCompleteMonoT.
Require Import Goat.GoatCompleteCtxT.
Require Import Goat.GoatCompleteCtxW.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the substitution a scheme's comparison reads ---- *)

(* [S] with the atoms and rows [sc] quantifies sent to themselves. *)
Definition sfixS (sc : scheme) (S : sub) : sub :=
  Sub (fun a => if AtomSetImpl.mem a (s_tq sc) then typ_Var a else sT S a)
      (fun r => if AtomSetImpl.mem r (s_rq sc) then row_Var r else sR S r).

Lemma sfixS_tin : forall sc S a, a `in` s_tq sc -> sT (sfixS sc S) a = typ_Var a.
Proof. intros sc S a Ha. cbn [sfixS sT]. rewrite (AtomSetImpl.mem_1 Ha). reflexivity. Qed.

Lemma sfixS_tout : forall sc S a, a `notin` s_tq sc -> sT (sfixS sc S) a = sT S a.
Proof.
  intros sc S a Ha. cbn [sfixS sT]. destruct (AtomSetImpl.mem a (s_tq sc)) eqn:E; [ | reflexivity ].
  exfalso. apply Ha. apply AtomSetFacts.mem_iff. exact E.
Qed.

Lemma sfixS_rin : forall sc S r, r `in` s_rq sc -> sR (sfixS sc S) r = row_Var r.
Proof. intros sc S r Hr. cbn [sfixS sR]. rewrite (AtomSetImpl.mem_1 Hr). reflexivity. Qed.

Lemma sfixS_rout : forall sc S r, r `notin` s_rq sc -> sR (sfixS sc S) r = sR S r.
Proof.
  intros sc S r Hr. cbn [sfixS sR]. destruct (AtomSetImpl.mem r (s_rq sc)) eqn:E; [ | reflexivity ].
  exfalso. apply Hr. apply AtomSetFacts.mem_iff. exact E.
Qed.

(* A type over even atoms and rows does not meet what a scheme quantifies. *)
Lemma sfixS_ev_ap : forall sc S T, WfSch sc -> EvT T -> apT (sfixS sc S) T = apT S T.
Proof.
  intros sc S T (Hq & Hr & _) [Ht Hv]. unfold apT. apply ap_typ_ext.
  - intros a Ha. apply sfixS_tout. intro Hq'. exact (ev_od a (Ht a Ha) (Hq a Hq')).
  - intros r Hr'. apply sfixS_rout. intro Hq'. exact (ev_od r (Hv r Hr') (Hr r Hq')).
Qed.

Lemma sfixS_ev_apR : forall sc S R, WfSch sc -> EvR R -> apR (sfixS sc S) R = apR S R.
Proof.
  intros sc S R (Hq & Hr & _) [Ht Hv]. unfold apR. apply (proj2 ap_ext_mut).
  - intros a Ha. apply sfixS_tout. intro Hq'. exact (ev_od a (Ht a Ha) (Hq a Hq')).
  - intros r Hr'. apply sfixS_rout. intro Hq'. exact (ev_od r (Hv r Hr') (Hr r Hq')).
Qed.

Lemma apR_Var : forall S r, apR S (row_Var r) = sR S r.
Proof. reflexivity. Qed.

(* ---- the contexts ---- *)

Definition SchIP (Pt : typ -> Prop) (D1 : denv) (Sg : sub) (sd sc : scheme) : Prop :=
  sch_leT Pt D1 sd (apS (sfixS sc Sg) sc).

Definition CIP (Pt : typ -> Prop) (D1 : denv) (Sg : sub) (G1 G : ctx) : Prop :=
  Forall2 (fun b1 b => fst b1 = fst b /\
     ((exists T1 T, snd b1 = sch_mono T1 /\ snd b = sch_mono T /\ teq (apT Sg T) T1) \/
      SchIP Pt D1 Sg (snd b1) (snd b))) G1 G.

(* A binding of the algorithm's context: a well formed scheme over the
   fragment, its free atoms and rows below the supply. *)
Definition SOkP (n : nat) (sc : scheme) : Prop :=
  WfSch sc /\ pf (s_body sc) /\ (forall a, a `in` ftv_sch sc -> old n a) /\
  (forall q, q `in` frv_sch sc -> old n q).

Definition GOkP (n : nat) (G : ctx) : Prop := Forall (fun b => SOkP n (snd b)) G.

Definition GLiveP (L LR : atoms) (G : ctx) : Prop :=
  Forall (fun b => ftv_sch (snd b) [<=] L /\ frv_sch (snd b) [<=] LR) G.

(* Every entry of a body is present under the substitution that fixes the
   scheme's quantifiers. *)
Definition GPsP (Sg : sub) (G : ctx) : Prop :=
  Forall (fun b => ps (sfixS (snd b) Sg) (s_body (snd b))) G.

Lemma SOkP_mono_le : forall n n' sc, n <= n' -> SOkP n sc -> SOkP n' sc.
Proof.
  intros n n' sc Hl (Hw & Hp & Ha & Hq). refine (conj Hw (conj Hp (conj _ _))).
  - intros a Ha'. exact (old_le _ _ _ Hl (Ha a Ha')).
  - intros q Hq'. exact (old_le _ _ _ Hl (Hq q Hq')).
Qed.

Lemma GOkP_mono : forall n n' G, n <= n' -> GOkP n G -> GOkP n' G.
Proof.
  intros n n' G Hl H. induction H as [|b G Hb _ IH]; constructor;
    [ exact (SOkP_mono_le _ _ _ Hl Hb) | exact IH ].
Qed.

Lemma GOkP_lookup : forall n G x sc, GOkP n G -> lookup x G = Some sc -> SOkP n sc.
Proof.
  intros n G x sc H. induction H as [|[y s0] G Hb _ IH]; intros Hl; [ discriminate Hl | ].
  cbn [lookup] in Hl. destruct (Atom.eq_dec x y) as [_|_].
  - injection Hl as Hl. subst s0. exact Hb.
  - exact (IH Hl).
Qed.

Lemma SOkP_mono : forall n T, pf T -> atT n T -> EvT T -> SOkP n (sch_mono T).
Proof.
  intros n T Hp [Ha Hq] HE. refine (conj (WfSch_mono T HE) (conj Hp (conj _ _))).
  - intros a Hin. apply Ha. apply (proj1 (ftv_sch_mono _ _)). exact Hin.
  - intros q Hin. apply Hq. apply (proj1 (frv_sch_mono T q)). exact Hin.
Qed.

Lemma SOkP_mono_inv : forall n T, SOkP n (sch_mono T) -> pf T /\ atT n T.
Proof.
  intros n T (_ & Hp & Ha & Hq). refine (conj Hp (conj _ _)).
  - intros a Hin. apply Ha. apply (proj2 (ftv_sch_mono _ _)). exact Hin.
  - intros q Hin. apply Hq. apply (proj2 (frv_sch_mono T q)). exact Hin.
Qed.

Lemma GOkP_nil : forall n, GOkP n nil.
Proof. intros n. constructor. Qed.

Lemma GOkP_cons : forall n x sc G, SOkP n sc -> GOkP n G -> GOkP n ((x ~ sc) ++ G).
Proof. intros n x sc G H HG. constructor; [ exact H | exact HG ]. Qed.

Lemma GOkP_of_GOk : forall n G, GOk n G -> GOkP n G.
Proof.
  intros n G H. induction H as [|b G Hb _ IH]; constructor; [ | exact IH ].
  destruct Hb as (Hw & Hr & Hrf & Hold). refine (conj Hw (conj (proj1 (rf_facts _ Hrf)) (conj Hold _))).
  intros q Hq. exfalso. apply AtomSetFacts.diff_iff in Hq. destruct Hq as [Hq _].
  exact (proj1 (proj2 (proj2 (rf_facts _ Hrf))) q Hq).
Qed.

Lemma GLiveP_nil : forall L LR, GLiveP L LR nil.
Proof. intros L LR. constructor. Qed.

Lemma GLiveP_cons_sch : forall L LR x sc G,
  ftv_sch sc [<=] L -> frv_sch sc [<=] LR -> GLiveP L LR G -> GLiveP L LR ((x ~ sc) ++ G).
Proof. intros L LR x sc G H1 H2 HG. constructor; [ exact (conj H1 H2) | exact HG ]. Qed.

Lemma GLiveP_cons : forall L LR x T G,
  ftv_typ T [<=] L -> frv_typ T [<=] LR -> GLiveP L LR G -> GLiveP L LR ((x ~ sch_mono T) ++ G).
Proof.
  intros L LR x T G H1 H2 HG. apply GLiveP_cons_sch; [ | | exact HG ].
  - intros a Ha. apply H1. apply (proj1 (ftv_sch_mono _ _)). exact Ha.
  - intros q Hq. apply H2. apply (proj1 (frv_sch_mono T q)). exact Hq.
Qed.

Lemma GLiveP_mono : forall L1 L2 LR1 LR2 G, L1 [<=] L2 -> LR1 [<=] LR2 -> GLiveP L1 LR1 G -> GLiveP L2 LR2 G.
Proof.
  intros L1 L2 LR1 LR2 G Hl Hr H. induction H as [|b G (H1 & H2) _ IH]; constructor.
  - split; [ intros a Ha; apply Hl; apply H1; exact Ha | intros q Hq; apply Hr; apply H2; exact Hq ].
  - exact IH.
Qed.

Lemma GLiveP_lookup : forall L LR G x sc, GLiveP L LR G -> lookup x G = Some sc ->
  ftv_sch sc [<=] L /\ frv_sch sc [<=] LR.
Proof.
  intros L LR G x sc H. induction H as [|[y s0] G HT _ IH]; intros Hl; [ discriminate Hl | ].
  cbn [lookup] in Hl. destruct (Atom.eq_dec x y) as [_|_].
  - injection Hl as Hl. subst s0. exact HT.
  - exact (IH Hl).
Qed.

Lemma GPsP_nil : forall Sg, GPsP Sg nil.
Proof. intros Sg. constructor. Qed.

Lemma GPsP_cons_mono : forall Sg x T G, pf T -> ps Sg T -> GPsP Sg G -> GPsP Sg ((x ~ sch_mono T) ++ G).
Proof.
  intros Sg x T G Hp Hs HG. constructor; [ | exact HG ]. cbn [snd s_body].
  refine (proj1 (ps_agree Sg _) T Hp _ Hs). intros y _.
  cbn [sfixS sT sch_mono s_tq]. destruct (AtomSetImpl.mem y {}) eqn:E; [ | reflexivity ].
  exfalso. apply AtomSetFacts.mem_iff in E. revert E. fsetdec.
Qed.

Lemma GPsP_cons_sch : forall Sg x sc G, ps (sfixS sc Sg) (s_body sc) -> GPsP Sg G -> GPsP Sg ((x ~ sc) ++ G).
Proof. intros Sg x sc G H HG. constructor; [ exact H | exact HG ]. Qed.

Lemma GPsP_of_rf : forall Sg n G, GOk n G -> GPsP Sg G.
Proof.
  intros Sg n G H. induction H as [|b G (Hw & Hr & Hrf & Ho) _ IH]; constructor; [ | exact IH ].
  exact (ps_rf _ _ Hrf).
Qed.

Lemma CIP_nil : forall Pt D1 Sg, CIP Pt D1 Sg nil nil.
Proof. intros. constructor. Qed.

Lemma CIP_cons : forall Pt D1 Sg G1 G x T1 T,
  CIP Pt D1 Sg G1 G -> teq (apT Sg T) T1 ->
  CIP Pt D1 Sg ((x ~ sch_mono T1) ++ G1) ((x ~ sch_mono T) ++ G).
Proof.
  intros Pt D1 Sg G1 G x T1 T H Ht. constructor; [ | exact H ].
  simpl. split; [ reflexivity | left; exists T1, T; repeat split; exact Ht ].
Qed.

Lemma CIP_cons_sch : forall Pt D1 Sg G1 G x sd sc,
  CIP Pt D1 Sg G1 G -> SchIP Pt D1 Sg sd sc -> CIP Pt D1 Sg ((x ~ sd) ++ G1) ((x ~ sc) ++ G).
Proof.
  intros Pt D1 Sg G1 G x sd sc H Hs. constructor; [ | exact H ].
  simpl. split; [ reflexivity | right; exact Hs ].
Qed.

Lemma CIP_dom : forall Pt D1 Sg G1 G, CIP Pt D1 Sg G1 G -> dom G1 [=] dom G.
Proof.
  intros Pt D1 Sg G1 G H. induction H as [|[y s1] [z sc] G1 G [Hk _] _ IH]; simpl in *; [ reflexivity | ].
  rewrite Hk, IH. reflexivity.
Qed.

Lemma CIP_lookup : forall Pt D1 Sg G1 G x sc1,
  CIP Pt D1 Sg G1 G -> uniq G1 -> binds x sc1 G1 ->
  exists sc, lookup x G = Some sc /\
    ((exists T1 T, sc1 = sch_mono T1 /\ sc = sch_mono T /\ teq (apT Sg T) T1) \/ SchIP Pt D1 Sg sc1 sc).
Proof.
  intros Pt D1 Sg G1 G x sc1 H. induction H as [|[y s1] [z sc] G1 G [Hk Hrel] _ IH]; intros Hu Hb.
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

(* ---- a step, read on a scheme ---- *)

(* The derivation's substitution fixes a scheme's quantifiers and sends the
   rest through the step: on the atoms and rows the scheme's body mentions,
   [Sg] is the extension after [s] (up to conversion), because [OkS s] fixes
   what is odd and the images of what is live are even. *)
Lemma sfixS_step : forall L LR DT Sg n s D' n' S2 sc,
  SemW evA evA L LR DT Sg n s D' n' S2 -> LEv L -> LEv LR -> WfSch sc ->
  ftv_sch sc [<=] L -> frv_sch sc [<=] LR ->
  (forall y, y `in` ftv_typ (s_body sc) ->
     teq (sT (sfixS sc Sg) y) (apT (sfixS sc S2) (sT s y))) /\
  (forall q, q `in` frv_typ (s_body sc) ->
     req (sR (sfixS sc Sg) q) (apR (sfixS sc S2) (sR s q))).
Proof.
  intros L LR DT Sg n s D' n' S2 sc H HL HR Hw Hl Hr.
  pose proof (SemW_OkS _ _ _ _ _ _ _ _ _ _ _ H) as Hok.
  destruct Hok as (_ & Ht & Hrw & Hfx & Hfxr). pose proof Hw as (Hq & Hrq & _). split.
  - intros y Hy. destruct (in_dec_set y (s_tq sc)) as [Hyq|Hyq].
    + rewrite (Hfx y (not_ev_od y (Hq y Hyq))), apT_Var, !sfixS_tin by exact Hyq. apply teq_refl.
    + assert (Hf : y `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
      rewrite sfixS_tout by exact Hyq. rewrite (sfixS_ev_ap sc S2 _ Hw (Ht y (HL y (Hl y Hf)))).
      exact (SemW_F _ _ _ _ _ _ _ _ _ _ _ H y (Hl y Hf)).
  - intros q Hqf. destruct (in_dec_set q (s_rq sc)) as [Hqq|Hqq].
    + rewrite (Hfxr q (not_ev_od q (Hrq q Hqq))), apR_Var, !sfixS_rin by exact Hqq. apply req_refl.
    + assert (Hf : q `in` frv_sch sc) by (unfold frv_sch; apply AtomSetFacts.diff_iff; split; assumption).
      rewrite sfixS_rout by exact Hqq. rewrite (sfixS_ev_apR sc S2 _ Hw (Hrw q (HR q (Hr q Hf)))).
      exact (SemW_FR _ _ _ _ _ _ _ _ _ _ _ H q (Hr q Hf)).
Qed.

(* A binding stays inside the fragment and the live sets under a step. *)
Lemma SOkP_apS : forall L LR DT Sg n s D' n' S2 sc,
  SemW evA evA L LR DT Sg n s D' n' S2 -> SOkP n sc -> ftv_sch sc [<=] L -> frv_sch sc [<=] LR ->
  SOkP n' (apS s sc) /\ ftv_sch (apS s sc) [<=] limgT s L LR /\ frv_sch (apS s sc) [<=] limgR s L LR.
Proof.
  intros L LR DT Sg n s D' n' S2 sc H Hok Hl Hr.
  pose proof Hok as (Hw & Hp & _ & _). pose proof Hw as (Hq & Hrq & _).
  pose proof (SemW_OkS _ _ _ _ _ _ _ _ _ _ _ H) as Hs. destruct Hs as (_ & _ & _ & Hfx & Hfxr).
  pose proof (SemW_SIg _ _ _ _ _ _ _ _ _ _ _ H) as SI. destruct SI as (_ & SIx & SIq).
  assert (Hf : ftv_sch (apS s sc) [<=] limgT s L LR).
  { intros a Ha. unfold ftv_sch in Ha. cbn [apS s_body s_tq] in Ha.
    apply AtomSetFacts.diff_iff in Ha. destruct Ha as [Ha Hn]. unfold apT in Ha.
    destruct (ftv_ap_typ _ _ _ _ Ha) as [(b & Hb & Hab)|(p & Hp' & Hap)].
    - destruct (in_dec_set b (s_tq sc)) as [Hbq|Hbq].
      + rewrite (Hfx b (not_ev_od b (Hq b Hbq))) in Hab. simpl in Hab.
        apply AtomSetFacts.singleton_iff in Hab. subst. contradiction.
      + assert (Hb' : b `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
        apply limgT_in. left. exists b. split; [ exact (Hl b Hb') | exact Hab ].
    - destruct (in_dec_set p (s_rq sc)) as [Hpq|Hpq].
      + rewrite (Hfxr p (not_ev_od p (Hrq p Hpq))) in Hap. simpl in Hap. exfalso. revert Hap. fsetdec.
      + assert (Hp2 : p `in` frv_sch sc) by (unfold frv_sch; apply AtomSetFacts.diff_iff; split; assumption).
        apply limgT_in. right. exists p. split; [ exact (Hr p Hp2) | exact Hap ]. }
  assert (Hfr : frv_sch (apS s sc) [<=] limgR s L LR).
  { intros a Ha. unfold frv_sch in Ha. cbn [apS s_body s_rq] in Ha.
    apply AtomSetFacts.diff_iff in Ha. destruct Ha as [Ha Hn]. unfold apT in Ha.
    destruct (frv_ap_typ _ _ _ _ Ha) as [(b & Hb & Hab)|(p & Hp' & Hap)].
    - destruct (in_dec_set b (s_tq sc)) as [Hbq|Hbq].
      + rewrite (Hfx b (not_ev_od b (Hq b Hbq))) in Hab. simpl in Hab. exfalso. revert Hab. fsetdec.
      + assert (Hb' : b `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
        apply limgR_in. left. exists b. split; [ exact (Hl b Hb') | exact Hab ].
    - destruct (in_dec_set p (s_rq sc)) as [Hpq|Hpq].
      + rewrite (Hfxr p (not_ev_od p (Hrq p Hpq))) in Hap. simpl in Hap.
        apply AtomSetFacts.singleton_iff in Hap. subst. contradiction.
      + assert (Hp2 : p `in` frv_sch sc) by (unfold frv_sch; apply AtomSetFacts.diff_iff; split; assumption).
        apply limgR_in. right. exists p. split; [ exact (Hr p Hp2) | exact Hap ]. }
  refine (conj (conj (WfSch_ap s sc (SemW_OkS _ _ _ _ _ _ _ _ _ _ _ H) Hw) (conj _ (conj _ _))) (conj Hf Hfr)).
  - cbn [apS s_body]. apply (proj1 (pf_ap s)); [ exact Hp | | ].
    + intros x Hx. destruct (in_dec_set x (s_tq sc)) as [Hxq|Hxq].
      * rewrite (Hfx x (not_ev_od x (Hq x Hxq))). exact I.
      * assert (Hx' : x `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
        exact (proj1 (SIx x (Hl x Hx'))).
    + intros x Hx. destruct (in_dec_set x (s_rq sc)) as [Hxq|Hxq].
      * rewrite (Hfxr x (not_ev_od x (Hrq x Hxq))). exact I.
      * assert (Hx' : x `in` frv_sch sc) by (unfold frv_sch; apply AtomSetFacts.diff_iff; split; assumption).
        exact (proj1 (SIq x (Hr x Hx'))).
  - intros a Ha. exact (limgT_old n n' s S2 L LR (SemW_SIg _ _ _ _ _ _ _ _ _ _ _ H) a (Hf a Ha)).
  - intros a Ha. exact (limgR_old n n' s S2 L LR (SemW_SIg _ _ _ _ _ _ _ _ _ _ _ H) a (Hfr a Ha)).
Qed.

(* A body whose entries are present under [Sg] stays so under the extension. *)
Lemma ps_stepP : forall L LR DT Sg n s D' n' S2 sc,
  SemW evA evA L LR DT Sg n s D' n' S2 -> LEv L -> LEv LR -> WfSch sc -> pf (s_body sc) ->
  ftv_sch sc [<=] L -> frv_sch sc [<=] LR ->
  ps (sfixS sc Sg) (s_body sc) -> ps (sfixS sc S2) (apT s (s_body sc)).
Proof.
  intros L LR DT Sg n s D' n' S2 sc H HL HR Hw Hp Hl Hr Hps.
  pose proof (sfixS_step L LR DT Sg n s D' n' S2 sc H HL HR Hw Hl Hr) as (Fx & Fr).
  pose proof (SemW_OkS _ _ _ _ _ _ _ _ _ _ _ H) as Hs. destruct Hs as (_ & Ht & Hrw & Hfx & Hfxr).
  pose proof (SemW_SIg _ _ _ _ _ _ _ _ _ _ _ H) as SI. destruct SI as (_ & SIx & SIq).
  pose proof Hw as (Hq & Hrq & _).
  apply (proj1 (ps_pull (sfixS sc Sg) (sfixS sc S2) s)); [ exact Hp | exact Hps | | ].
  - intros y Hy. refine (conj (Fx y Hy) _). destruct (in_dec_set y (s_tq sc)) as [Hyq|Hyq].
    + rewrite (Hfx y (not_ev_od y (Hq y Hyq))). exact I.
    + assert (Hf : y `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
      destruct (SIx y (Hl y Hf)) as (Pf & _ & Ps).
      refine (proj1 (ps_agree S2 (sfixS sc S2)) _ Pf _ Ps).
      intros z Hz. symmetry. apply sfixS_tout. intro Hzq.
      exact (ev_od z (proj1 (Ht y (HL y (Hl y Hf))) z Hz) (Hq z Hzq)).
  - intros q Hq'. destruct (in_dec_set q (s_rq sc)) as [Hqq|Hqq].
    + rewrite (Hfxr q (not_ev_od q (Hrq q Hqq))). exact I.
    + assert (Hf : q `in` frv_sch sc) by (unfold frv_sch; apply AtomSetFacts.diff_iff; split; assumption).
      destruct (SIq q (Hr q Hf)) as (Pf & _ & Ps).
      refine (proj2 (ps_agree S2 (sfixS sc S2)) _ Pf _ Ps).
      intros z Hz. symmetry. apply sfixS_tout. intro Hzq.
      exact (ev_od z (proj1 (Hrw q (HR q (Hr q Hf))) z Hz) (Hq z Hzq)).
Qed.

(* The run's step on the context: the derivation's bindings are still
   comparable with the algorithm's, read at the extension, and the
   algorithm's context keeps its invariants. *)
Lemma CI_stepP : forall Pt L LR DT Sg n s D' n' S2 G1 G,
  SemW evA evA L LR DT Sg n s D' n' S2 -> LEv L -> LEv LR ->
  CIP Pt DT Sg G1 G -> GOkP n G -> GLiveP L LR G -> GPsP Sg G ->
  CIP Pt DT S2 G1 (apC s G) /\ GOkP n' (apC s G) /\
  GLiveP (limgT s L LR) (limgR s L LR) (apC s G) /\ GPsP S2 (apC s G).
Proof.
  intros Pt L LR DT Sg n s D' n' S2 G1 G H HL HR HC.
  rewrite apC_map.
  induction HC as [|[x s1] [y sc] G1 G [Hk Hrel] _ IH]; intros HG HGL HPS;
    [ refine (conj _ (conj _ (conj _ _))); constructor | ].
  inversion HG as [|b G' Hsc HG' Eb]; subst.
  inversion HGL as [|b2 G2 (HL2 & HR2) HL' Eb2]; subst.
  inversion HPS as [|b3 G3 HP3 HPS' Eb3]; subst. simpl in *. subst y.
  destruct (IH HG' HL' HPS') as (IC & IG & ILv & IPS).
  destruct (SOkP_apS L LR DT Sg n s D' n' S2 sc H Hsc HL2 HR2) as (Hso & Hfl & Hfr).
  pose proof Hsc as (Hw & Hp & _ & _).
  refine (conj _ (conj _ (conj _ _))).
  - constructor; [ | exact IC ]. simpl. split; [ reflexivity | ].
    destruct Hrel as [(T1 & T & E1 & E2 & Ht)|Hsch].
    + left. subst sc.
      exists T1, (apT s T). split; [ exact E1 | split; [ reflexivity | ] ].
      eapply teq_trans; [ | exact Ht ]. apply teq_sym.
      apply ap_factor.
      * intros z Hz. exact (SemW_F _ _ _ _ _ _ _ _ _ _ _ H z (HL2 z (proj2 (ftv_sch_mono T z) Hz))).
      * intros q Hq. exact (SemW_FR _ _ _ _ _ _ _ _ _ _ _ H q (HR2 q (proj2 (frv_sch_mono T q) Hq))).
    + right. unfold SchIP in Hsch |- *.
      change (sfixS (apS s sc) S2) with (sfixS sc S2).
      refine (sch_leT_trans _ _ _ _ _ Hsch _).
      apply sch_leT_conv; try reflexivity.
      cbn [apS s_body]. apply ap_factor.
      * exact (proj1 (sfixS_step L LR DT Sg n s D' n' S2 sc H HL HR Hw HL2 HR2)).
      * exact (proj2 (sfixS_step L LR DT Sg n s D' n' S2 sc H HL HR Hw HL2 HR2)).
  - constructor; [ exact Hso | exact IG ].
  - constructor; [ exact (conj Hfl Hfr) | exact ILv ].
  - constructor; [ | exact IPS ]. cbn [snd apS s_body].
    exact (ps_stepP L LR DT Sg n s D' n' S2 sc H HL HR Hw Hp HL2 HR2 HP3).
Qed.
