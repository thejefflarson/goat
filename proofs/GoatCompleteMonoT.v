(* Completeness of algorithm W, stage 7.8f: [gen_mono] up to conversion
   (docs/design/phase7-proof-plan.md).

   [gen_mono] (GoatCompleteMono.v) takes the derivation's type to be the image
   [apT S2 T'] of the algorithm's, and compares the schemes by [sch_leP].  Over the
   fragment the derivation's type [T1] is only convertible to the image, and the
   comparison is [sch_leT] (GoatCompleteSchT.v).  Three things change.

   - The images the derivation's instance is read at are the canonical
     representatives [erT (sT S2 b)]: an instance of the derivation's scheme
     says nothing of the atoms that [T1] mentions only in absent fields.  That
     is enough, because [ps S2 T'] (every entry of [T'] is present under [S2])
     puts the atoms of each representative inside the representative of the
     image of [T'] ([er_ap_sub]), which is the derivation's up to [er_inv].
   - The context is [frozenE]: the representatives of the images of the atoms
     the algorithm keeps free lie in the derivation's context.
   - The instance is only convertible to the one it is compared with
     ([teq_ap] and [ap_cong_on]).

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Goat.GoatConv.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferGen.
Require Import Goat.GoatSatTeq.
Require Import Goat.GoatCompleteInst.
Require Import Goat.GoatCompleteGen.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRewrite.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteEr.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteBound.
Require Import Goat.GoatCompleteMono.
Require Import Goat.GoatCompleteSchT.
Require Import Stdlib.Lists.List.
Import ListNotations.

Lemma EvT_var : forall c, ev c -> EvT (typ_Var c).
Proof.
  intros c Hc. split; intros x Hx; simpl in Hx;
    [ apply AtomSetFacts.singleton_iff in Hx; subst; exact Hc | fsetdec ].
Qed.

Lemma EvR_er : forall R, EvR R -> EvR (erR R).
Proof.
  intros R [H1 H2]. destruct (proj2 er_sub R) as [E1 E2].
  split; intros x Hx; [ apply H1; apply E1; exact Hx | apply H2; apply E2; exact Hx ].
Qed.

Lemma EvT_er : forall T, EvT T -> EvT (erT T).
Proof.
  intros T [H1 H2]. destruct (proj1 er_sub T) as [E1 E2].
  split; intros x Hx; [ apply H1; apply E1; exact Hx | apply H2; apply E2; exact Hx ].
Qed.

Section GenMonoT.
Variables (Pt : typ -> Prop) (D Dal : denv) (S2 : sub) (Gp Gq : ctx) (T' T1 : typ)
  (k : sort_fn) (rk : rkind_fn).
Hypotheses
  (HPlc : forall X, Pt X -> lct 0 X)
  (HPev : forall X, Pt X -> EvT X)
  (HPer : forall X, Pt X -> Pt (erT X))
  (HPvar : forall c, ev c -> Pt (typ_Var c))
  (HPap : forall st sr X, lc_sub st sr -> Pt X ->
            (forall c, c `in` ftv_typ X -> Pt (st c)) ->
            (forall p, p `in` frv_typ X -> EvR (sr p)) -> Pt (ap_typ st sr X)).
Hypotheses (Hfz : frozenE S2 Gp Gq) (Hpf : pf T') (Hps : ps S2 T') (Hteq : teq T1 (apT S2 T')).
Hypotheses
  (HFt : forall b, b `in` s_tq (gen_ren Dal Gp T') -> sT S2 b = typ_Var b)
  (HFr : forall r, r `in` s_rq (gen_ren Dal Gp T') -> sR S2 r = row_Var r)
  (HEt : forall a, a `in` ftv_ctx Gp -> EvT (sT S2 a))
  (HEr : forall r, r `in` frv_ctx Gp -> EvR (sR S2 r))
  (HPt : forall a, a `in` ftv_typ T' -> Pt (sT S2 a))
  (HPr : forall r, r `in` frv_typ T' -> EvR (sR S2 r) /\ lcr 0 (sR S2 r)).

Local Notation Vt := (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx Gq)).
Local Notation Vr := (AtomSetImpl.diff (frv_typ T1) (frv_ctx Gq)).
Local Notation la := (gen_vars_t Gp T').
Local Notation lr := (gen_vars_r Gp T').
Local Notation sa := (apS S2 (gen_ren Dal Gp T')).
Local Notation sd := (gen Gq T1 k rk).

Hypotheses (Hk : forall b, b `in` ftv_typ T' -> sat (extr (ext D Vt k) Vr rk) (Dal b) (sT S2 b))
           (Hr : forall r, r `in` frv_typ T' -> rkok (extr (ext D Vt k) Vr rk) (drk Dal r) (sR S2 r)).

Lemma gmT_vis : (forall x, x `in` ftv_typ T' ->
     ftv_typ (erT (sT S2 x)) [<=] ftv_typ (erT T1) /\ frv_typ (erT (sT S2 x)) [<=] frv_typ (erT T1)) /\
  (forall r, r `in` frv_typ T' ->
     ftv_row (erR (sR S2 r)) [<=] ftv_typ (erT T1) /\ frv_row (erR (sR S2 r)) [<=] frv_typ (erT T1)).
Proof. exact (vis_of_ps S2 T' T1 Hpf Hps (teq_sym _ _ Hteq)). Qed.

(* The representatives of the images of the variables the algorithm keeps free
   are fixed by an instance that fixes the derivation's free variables and the
   even atoms. *)
Lemma gmT_id : forall st sr st' sr',
  (forall c, ev c -> st c = typ_Var c) -> (forall p, ev p -> sr p = row_Var p) ->
  (forall c, c `in` ftv_ctx Gq -> st' c = typ_Var c) ->
  (forall p, p `in` frv_ctx Gq -> sr' p = row_Var p) ->
  (forall a, a `in` ftv_ctx Gp -> ap_typ st sr (erT (sT S2 a)) = ap_typ st' sr' (erT (sT S2 a))) /\
  (forall r, r `in` frv_ctx Gp -> ap_row st sr (erR (sR S2 r)) = ap_row st' sr' (erR (sR S2 r))).
Proof.
  intros st sr st' sr' H1 H2 H3 H4. destruct Hfz as [Hf1 Hf2]. split.
  - intros a Ha. pose proof (EvT_er _ (HEt a Ha)) as [Ev1 Ev2].
    apply ap_typ_ext.
    + intros c Hc. rewrite (H1 c (Ev1 c Hc)). symmetry. apply H3. exact (proj1 (Hf1 a Ha) c Hc).
    + intros p Hp. rewrite (H2 p (Ev2 p Hp)). symmetry. apply H4. exact (proj2 (Hf1 a Ha) p Hp).
  - intros r Hr0. pose proof (EvR_er _ (HEr r Hr0)) as [Ev1 Ev2].
    apply (proj2 ap_ext_mut).
    + intros c Hc. rewrite (H1 c (Ev1 c Hc)). symmetry. apply H3. exact (proj1 (Hf2 r Hr0) c Hc).
    + intros p Hp. rewrite (H2 p (Ev2 p Hp)). symmetry. apply H4. exact (proj2 (Hf2 r Hr0) p Hp).
Qed.

(* Every instance of the derivation's scheme is convertible to an instance of the algorithm's. *)
Lemma gmT_inst : forall (D' : denv) T,
  (forall a, a `in` ftv_schE sd -> D' a = D a) ->
  (forall r, r `in` frv_schE sd -> drk D' r = drk D r) ->
  instT Pt D' T sd -> exists T', instT Pt D' T' sa /\ teq T T'.
Proof.
  intros D' T Hda Hdr (st' & sr' & t1 & t2 & t3 & t4 & t5 & t6 & t7 & t8).
  cbn [gen s_tq s_rq s_body s_sk s_rk] in t1, t2, t3, t4, t5.
  destruct gmT_vis as [HvT HvR].
  set (ft := fun a => ap_typ st' sr' (erT (sT S2 a))).
  set (fr := fun r => ap_row st' sr' (erR (sR S2 r))).
  assert (Hst : forall c, ev c -> sel_t la ft c = typ_Var c).
  { intros c Hc. apply sel_t_out. intros a' Ha' Heq. subst c. exact (ev_od _ Hc (od_oa _)). }
  assert (Hsr : forall c, ev c -> sel_r lr fr c = row_Var c).
  { intros c Hc. apply sel_r_out. intros a' Ha' Heq. subst c. exact (ev_od _ Hc (od_oa _)). }
  assert (Hq1 : forall c, c `in` ftv_ctx Gq -> st' c = typ_Var c).
  { intros c Hc. apply t1. intro Hd. apply AtomSetFacts.diff_iff in Hd. tauto. }
  assert (Hq2 : forall c, c `in` frv_ctx Gq -> sr' c = row_Var c).
  { intros c Hc. apply t2. intro Hd. apply AtomSetFacts.diff_iff in Hd. tauto. }
  destruct (gmT_id (sel_t la ft) (sel_r lr fr) st' sr' Hst Hsr Hq1 Hq2) as [Gid Rid].
  exists (ap_typ (sel_t la ft) (sel_r lr fr) (s_body sa)). split.
  - exists (sel_t la ft), (sel_r lr fr).
    refine (conj _ (conj _ (conj eq_refl (conj _ (conj _ (conj _ (conj _ _))))))).
    + intros a Ha. apply sel_t_out. intros a' Ha' Heq. apply Ha. cbn [apS s_tq].
      apply gen_ren_tq. exists a'. split; assumption.
    + intros a Ha. apply sel_r_out. intros a' Ha' Heq. apply Ha. cbn [apS s_rq].
      apply gen_ren_rq. exists a'. split; assumption.
    + intros a Ha. cbn [apS s_tq] in Ha. apply gen_ren_tq in Ha. destruct Ha as (b & Hb & ->).
      cbn [apS s_sk gen_ren]. rewrite (gen_sk_at Dal la b Hb). rewrite (sel_t_at la ft b Hb).
      assert (Hb' : b `in` ftv_typ T') by (apply In_la in Hb; tauto).
      refine (gm_sat D D' _ _ k rk st' sr' (Dal b) (erT (sT S2 b)) t1 t2 t4 t5 _ _ _).
      * intros c Hc Hn. apply Hda. unfold ftv_schE. cbn [gen s_body s_tq].
        apply AtomSetFacts.diff_iff. split; [ | exact Hn ]. exact (proj1 (HvT b Hb') c Hc).
      * intros p Hp Hn. apply Hdr. unfold frv_schE. cbn [gen s_body s_rq].
        apply AtomSetFacts.diff_iff. split; [ | exact Hn ]. exact (proj2 (HvT b Hb') p Hp).
      * exact (sat_teq _ _ _ _ (teq_sym _ _ (proj1 er_teq _)) (Hk b Hb')).
    + intros a Ha. cbn [apS s_rq] in Ha. apply gen_ren_rq in Ha. destruct Ha as (b & Hb & ->).
      cbn [apS s_rk gen_ren]. rewrite (gen_rk_at Dal lr b Hb). rewrite (sel_r_at lr fr b Hb).
      assert (Hb' : b `in` frv_typ T') by (apply In_lr in Hb; tauto).
      refine (gm_rkok D D' _ _ k rk st' sr' (drk Dal b) (erR (sR S2 b)) t1 t2 t4 t5 _ _ _).
      * intros c Hc Hn. apply Hda. unfold ftv_schE. cbn [gen s_body s_tq].
        apply AtomSetFacts.diff_iff. split; [ | exact Hn ]. exact (proj1 (HvR b Hb') c Hc).
      * intros p Hp Hn. apply Hdr. unfold frv_schE. cbn [gen s_body s_rq].
        apply AtomSetFacts.diff_iff. split; [ | exact Hn ]. exact (proj2 (HvR b Hb') p Hp).
      * exact (rkok_req _ _ _ _ (req_sym _ _ (proj2 er_teq _)) (Hr b Hb')).
    + split.
      * intro b. apply sel_t_lc. intros a Ha.
        assert (Ha' : a `in` ftv_typ T') by (apply In_la in Ha; tauto).
        exact (ap_lc _ _ _ 0 t6 (proj1 er_lc _ 0 (HPlc _ (HPt a Ha')))).
      * intro b. apply sel_r_lc. intros a Ha.
        assert (Ha' : a `in` frv_typ T') by (apply In_lr in Ha; tauto).
        exact (ap_lcr _ _ _ 0 t6 (proj2 er_lc _ 0 (proj2 (HPr a Ha')))).
    + intros a Ha. cbn [apS s_tq] in Ha. apply gen_ren_tq in Ha. destruct Ha as (b & Hb & ->).
      rewrite (sel_t_at la ft b Hb).
      assert (Hb' : b `in` ftv_typ T') by (apply In_la in Hb; tauto).
      pose proof (HPt b Hb') as Hpb. pose proof (HPev _ Hpb) as [Hev1 Hev2].
      change (Pt (ap_typ st' sr' (erT (sT S2 b)))).
      apply HPap; [ exact t6 | exact (HPer _ Hpb) | | ].
      * intros c Hc. destruct (in_dec_set c (s_tq sd)) as [Hq|Hq].
        -- exact (t7 c Hq).
        -- rewrite (t1 c Hq). apply HPvar. apply Hev1. exact (proj1 (proj1 er_sub _) c Hc).
      * intros p Hp. destruct (in_dec_set p (s_rq sd)) as [Hq|Hq].
        -- exact (t8 p Hq).
        -- rewrite (t2 p Hq). split; intros x Hx; simpl in Hx;
             [ fsetdec | apply AtomSetFacts.singleton_iff in Hx; subst x; apply Hev2; exact (proj2 (proj1 er_sub _) p Hp) ].
    + intros a Ha. cbn [apS s_rq] in Ha. apply gen_ren_rq in Ha. destruct Ha as (b & Hb & ->).
      rewrite (sel_r_at lr fr b Hb).
      assert (Hb' : b `in` frv_typ T') by (apply In_lr in Hb; tauto).
      pose proof (HPr b Hb') as [Hpb _].
      change (EvR (ap_row st' sr' (erR (sR S2 b)))).
      apply EvT_Record. change (EvT (ap_typ st' sr' (typ_Record (erR (sR S2 b))))).
      apply EvT_ap_gen; [ apply EvT_Record; exact (EvR_er _ Hpb) | | ].
      * intros c Hc. destruct (in_dec_set c (s_tq sd)) as [Hq|Hq].
        -- exact (HPev _ (t7 c Hq)).
        -- rewrite (t1 c Hq). apply EvT_var. exact (proj1 (EvR_er _ Hpb) c Hc).
      * intros p Hp. destruct (in_dec_set p (s_rq sd)) as [Hq|Hq].
        -- exact (t8 p Hq).
        -- rewrite (t2 p Hq). split; intros x Hx; simpl in Hx;
             [ fsetdec | apply AtomSetFacts.singleton_iff in Hx; subst x; exact (proj2 (EvR_er _ Hpb) p Hp) ].
  - (* the conversion *)
    assert (Hmid : teq (ap_typ (sel_t la ft) (sel_r lr fr) (s_body sa)) (ap_typ st' sr' (apT S2 T'))).
    { cbn [apS s_body]. rewrite gen_body.
      change (ap_typ (rename_t la) (rename_r lr) T') with (apT (Sub (rename_t la) (rename_r lr)) T').
      change (ap_typ (sel_t la ft) (sel_r lr fr) (apT S2 (apT (Sub (rename_t la) (rename_r lr)) T')))
        with (apT (Sub (sel_t la ft) (sel_r lr fr)) (apT S2 (apT (Sub (rename_t la) (rename_r lr)) T'))).
      change (ap_typ st' sr' (apT S2 T')) with (apT (Sub st' sr') (apT S2 T')).
      rewrite (apT_comp S2 (Sub (rename_t la) (rename_r lr)) T').
      rewrite (apT_comp (Sub (sel_t la ft) (sel_r lr fr)) (scomp S2 (Sub (rename_t la) (rename_r lr))) T').
      rewrite (apT_comp (Sub st' sr') S2 T').
      apply (proj1 (ap_cong_on _ _)).
      - intros x Hx. change (teq (apT (Sub (sel_t la ft) (sel_r lr fr)) (apT S2 (rename_t la x))) (apT (Sub st' sr') (sT S2 x))).
        destruct (in_dec Atom.eq_dec x la) as [Hin|Hin].
        + assert (Hmq : oa (idx x la) `in` s_tq (gen_ren Dal Gp T'))
            by (apply gen_ren_tq; exists x; split; [ exact Hin | reflexivity ]).
          unfold rename_t. destruct (in_dec Atom.eq_dec x la) as [_|Hn]; [ | contradiction ].
          change (teq (apT (Sub (sel_t la ft) (sel_r lr fr)) (sT S2 (oa (idx x la)))) (apT (Sub st' sr') (sT S2 x))).
          rewrite (HFt _ Hmq). change (teq (sel_t la ft (oa (idx x la))) (ap_typ st' sr' (sT S2 x))).
          rewrite (sel_t_at la ft x Hin). exact (teq_ap _ _ st' sr' (proj1 er_teq _)).
        + assert (Hap : x `in` ftv_ctx Gp).
          { destruct (in_dec_set x (ftv_ctx Gp)) as [H|H]; [ exact H | exfalso; apply Hin; apply In_la; auto ]. }
          unfold rename_t. destruct (in_dec Atom.eq_dec x la) as [H|_]; [ contradiction | ].
          change (teq (apT (Sub (sel_t la ft) (sel_r lr fr)) (sT S2 x)) (ap_typ st' sr' (sT S2 x))).
          eapply teq_trans; [ exact (teq_ap _ _ (sel_t la ft) (sel_r lr fr) (teq_sym _ _ (proj1 er_teq _))) | ].
          rewrite (Gid x Hap). exact (teq_ap _ _ st' sr' (proj1 er_teq _)).
      - intros q Hq. change (req (apR (Sub (sel_t la ft) (sel_r lr fr)) (apR S2 (rename_r lr q))) (apR (Sub st' sr') (sR S2 q))).
        destruct (in_dec Atom.eq_dec q lr) as [Hin|Hin].
        + assert (Hmq : oa (idx q lr) `in` s_rq (gen_ren Dal Gp T'))
            by (apply gen_ren_rq; exists q; split; [ exact Hin | reflexivity ]).
          unfold rename_r. destruct (in_dec Atom.eq_dec q lr) as [_|Hn]; [ | contradiction ].
          change (req (apR (Sub (sel_t la ft) (sel_r lr fr)) (sR S2 (oa (idx q lr)))) (ap_row st' sr' (sR S2 q))).
          rewrite (HFr _ Hmq). change (req (sel_r lr fr (oa (idx q lr))) (ap_row st' sr' (sR S2 q))).
          rewrite (sel_r_at lr fr q Hin). exact (proj2 teq_ap_mut _ _ (proj2 er_teq _) st' sr').
        + assert (Hap : q `in` frv_ctx Gp).
          { destruct (in_dec_set q (frv_ctx Gp)) as [H|H]; [ exact H | exfalso; apply Hin; apply In_lr; auto ]. }
          unfold rename_r. destruct (in_dec Atom.eq_dec q lr) as [H|_]; [ contradiction | ].
          change (req (apR (Sub (sel_t la ft) (sel_r lr fr)) (sR S2 q)) (ap_row st' sr' (sR S2 q))).
          eapply req_trans; [ exact (proj2 teq_ap_mut _ _ (req_sym _ _ (proj2 er_teq _)) (sel_t la ft) (sel_r lr fr)) | ].
          rewrite (Rid q Hap). exact (proj2 teq_ap_mut _ _ (proj2 er_teq _) st' sr'). }
    rewrite t3. eapply teq_trans; [ | apply teq_sym; exact Hmid ].
    exact (teq_ap _ _ st' sr' Hteq).
Qed.

(* The derivation's generalization is convertible to an instance of the algorithm's. *)
Theorem gen_monoT : sch_leT Pt D sd sa.
Proof.
  destruct gmT_vis as [HvT HvR]. destruct Hfz as [Hf1 Hf2].
  split; [ | split ].
  - intros c Hc. unfold ftv_schE in Hc |- *. cbn [apS s_body s_tq] in Hc.
    apply AtomSetFacts.diff_iff in Hc as [Hc Hn].
    rewrite gen_body in Hc.
    change (ap_typ (rename_t la) (rename_r lr) T') with (apT (Sub (rename_t la) (rename_r lr)) T') in Hc.
    rewrite apT_comp in Hc.
    cbn [gen s_body s_tq]. apply AtomSetFacts.diff_iff.
    assert (Hgoal : c `in` ftv_typ (erT T1) /\ c `in` ftv_ctx Gq).
    { destruct (proj1 (er_ap_atoms (scomp S2 (Sub (rename_t la) (rename_r lr)))) T' Hpf) as [A _].
      destruct (A c Hc) as [(x & Hx & Hcx)|(r & Hr0 & Hcr)].
      - change (sT (scomp S2 (Sub (rename_t la) (rename_r lr))) x) with (apT S2 (rename_t la x)) in Hcx.
        unfold rename_t in Hcx. destruct (in_dec Atom.eq_dec x la) as [Hin|Hin].
        + exfalso. assert (Hmq : oa (idx x la) `in` s_tq (gen_ren Dal Gp T'))
            by (apply gen_ren_tq; exists x; split; [ exact Hin | reflexivity ]).
          change (apT S2 (typ_Var (oa (idx x la)))) with (sT S2 (oa (idx x la))) in Hcx.
          rewrite (HFt _ Hmq) in Hcx. simpl in Hcx. apply AtomSetFacts.singleton_iff in Hcx. subst c.
          apply Hn. exact Hmq.
        + assert (Hap : x `in` ftv_ctx Gp).
          { destruct (in_dec_set x (ftv_ctx Gp)) as [H|H]; [ exact H | exfalso; apply Hin; apply In_la; auto ]. }
          change (apT S2 (typ_Var x)) with (sT S2 x) in Hcx.
          split; [ exact (proj1 (HvT x Hx) c Hcx) | exact (proj1 (Hf1 x Hap) c Hcx) ].
      - change (sR (scomp S2 (Sub (rename_t la) (rename_r lr))) r) with (apR S2 (rename_r lr r)) in Hcr.
        unfold rename_r in Hcr. destruct (in_dec Atom.eq_dec r lr) as [Hin|Hin].
        + exfalso. assert (Hmq : oa (idx r lr) `in` s_rq (gen_ren Dal Gp T'))
            by (apply gen_ren_rq; exists r; split; [ exact Hin | reflexivity ]).
          change (apR S2 (row_Var (oa (idx r lr)))) with (sR S2 (oa (idx r lr))) in Hcr.
          rewrite (HFr _ Hmq) in Hcr. simpl in Hcr. fsetdec.
        + assert (Hap : r `in` frv_ctx Gp).
          { destruct (in_dec_set r (frv_ctx Gp)) as [H|H]; [ exact H | exfalso; apply Hin; apply In_lr; auto ]. }
          change (apR S2 (row_Var r)) with (sR S2 r) in Hcr.
          split; [ exact (proj1 (HvR r Hr0) c Hcr) | exact (proj1 (Hf2 r Hap) c Hcr) ]. }
    destruct Hgoal as [G1 G2]. split; [ exact G1 | ].
    intro Hd. apply AtomSetFacts.diff_iff in Hd. exact (proj2 Hd G2).
  - intros c Hc. unfold frv_schE in Hc |- *. cbn [apS s_body s_rq] in Hc.
    apply AtomSetFacts.diff_iff in Hc as [Hc Hn].
    rewrite gen_body in Hc.
    change (ap_typ (rename_t la) (rename_r lr) T') with (apT (Sub (rename_t la) (rename_r lr)) T') in Hc.
    rewrite apT_comp in Hc.
    cbn [gen s_body s_rq]. apply AtomSetFacts.diff_iff.
    assert (Hgoal : c `in` frv_typ (erT T1) /\ c `in` frv_ctx Gq).
    { destruct (proj1 (er_ap_atoms (scomp S2 (Sub (rename_t la) (rename_r lr)))) T' Hpf) as [_ A].
      destruct (A c Hc) as [(x & Hx & Hcx)|(r & Hr0 & Hcr)].
      - change (sT (scomp S2 (Sub (rename_t la) (rename_r lr))) x) with (apT S2 (rename_t la x)) in Hcx.
        unfold rename_t in Hcx. destruct (in_dec Atom.eq_dec x la) as [Hin|Hin].
        + exfalso. assert (Hmq : oa (idx x la) `in` s_tq (gen_ren Dal Gp T'))
            by (apply gen_ren_tq; exists x; split; [ exact Hin | reflexivity ]).
          change (apT S2 (typ_Var (oa (idx x la)))) with (sT S2 (oa (idx x la))) in Hcx.
          rewrite (HFt _ Hmq) in Hcx. simpl in Hcx. fsetdec.
        + assert (Hap : x `in` ftv_ctx Gp).
          { destruct (in_dec_set x (ftv_ctx Gp)) as [H|H]; [ exact H | exfalso; apply Hin; apply In_la; auto ]. }
          change (apT S2 (typ_Var x)) with (sT S2 x) in Hcx.
          split; [ exact (proj2 (HvT x Hx) c Hcx) | exact (proj2 (Hf1 x Hap) c Hcx) ].
      - change (sR (scomp S2 (Sub (rename_t la) (rename_r lr))) r) with (apR S2 (rename_r lr r)) in Hcr.
        unfold rename_r in Hcr. destruct (in_dec Atom.eq_dec r lr) as [Hin|Hin].
        + exfalso. assert (Hmq : oa (idx r lr) `in` s_rq (gen_ren Dal Gp T'))
            by (apply gen_ren_rq; exists r; split; [ exact Hin | reflexivity ]).
          change (apR S2 (row_Var (oa (idx r lr)))) with (sR S2 (oa (idx r lr))) in Hcr.
          rewrite (HFr _ Hmq) in Hcr. simpl in Hcr. apply AtomSetFacts.singleton_iff in Hcr. subst c.
          apply Hn. exact Hmq.
        + assert (Hap : r `in` frv_ctx Gp).
          { destruct (in_dec_set r (frv_ctx Gp)) as [H|H]; [ exact H | exfalso; apply Hin; apply In_lr; auto ]. }
          change (apR S2 (row_Var r)) with (sR S2 r) in Hcr.
          split; [ exact (proj2 (HvR r Hr0) c Hcr) | exact (proj2 (Hf2 r Hap) c Hcr) ]. }
    destruct Hgoal as [G1 G2]. split; [ exact G1 | ].
    intro Hd. apply AtomSetFacts.diff_iff in Hd. exact (proj2 Hd G2).
  - intros D' Hd Hr' T H. exact (gmT_inst D' T Hd Hr' H).
Qed.

End GenMonoT.
