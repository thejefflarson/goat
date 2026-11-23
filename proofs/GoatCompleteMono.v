(* Completeness of algorithm W, stage 7.5, part L1: [gen_mono]
   (docs/design/phase7-proof-plan.md).

   The let case's scheme comparison.  The derivation generalizes [T1 = S2 T']
   over its context [Gq] (the pin included), recording the sorts [k] and kinds
   [rk]; the algorithm generalizes [T'] over its context [Gp], recording the
   sorts [Dal] gives ([gen_ren], GoatInfer.v).  Applying [S2] to the
   algorithm's scheme, as the induction does to its whole context, gives a
   scheme of which the derivation's is an instance ([sch_le], GoatCompleteInst.v).

   The algorithm's quantified variables are odd atoms [S2] leaves alone, so an
   instance of the derivation's scheme becomes one of the algorithm's by
   sending the odd atom that stands for [a] to what the instance sends [S2 a]
   to; [kres Dal Dd S2], where [Dd] is the environment the derivation's
   premise lives in, carries the sorts across ([gm_sat], GoatCompleteGen.v).

   What the comparison needs of the contexts is [frozen]: [S2] sends each
   variable the algorithm keeps free (a free variable of [Gp]) to a type over
   variables the derivation keeps free (free in [Gq]).  The pin enters through
   [Gp] and [Gq], which are [pin_ctx] of the contexts, so a numeral variable
   the algorithm pins ([let_pin], GoatInfer.v) is frozen by the derivation's
   [lit_pinned] premise ([lit_pin_frozen]). *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferKnot.
Require Import Goat.GoatInferGen.
Require Import Goat.GoatCompleteInst.
Require Import Goat.GoatCompleteGen.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Import ListNotations.

(* ---- the witness that sends each quantified odd atom to an image ---- *)

Definition sel_t (la : list atom) (f : atom -> typ) : tsub :=
  fun b => fold_right (fun a acc => if Atom.eq_dec b (oa (idx a la)) then f a else acc) (typ_Var b) la.

Definition sel_r (lr : list atom) (f : atom -> row) : rsub :=
  fun b => fold_right (fun r acc => if Atom.eq_dec b (oa (idx r lr)) then f r else acc) (row_Var b) lr.

Lemma oa_idx_inj : forall l a a', In a l -> In a' l -> oa (idx a' l) = oa (idx a l) -> a' = a.
Proof.
  intros l a a' Ha Ha' H. unfold oa in H. apply idx_atom_inj in H.
  apply (idx_inj a' a l Ha' Ha). lia.
Qed.

Lemma sel_at_gen : forall {A : Type} (l : list atom) (f : atom -> A) (d : A) a,
  In a l ->
  fold_right (fun a' acc => if Atom.eq_dec (oa (idx a l)) (oa (idx a' l)) then f a' else acc) d l = f a.
Proof.
  intros A l f d a Ha.
  apply (sel_at (fun a' => oa (idx a' l)) f (oa (idx a l)) d l a Ha eq_refl).
  intros a' Ha' H. rewrite (oa_idx_inj l a a' Ha Ha' H). reflexivity.
Qed.

Lemma sel_t_at : forall la f a, In a la -> sel_t la f (oa (idx a la)) = f a.
Proof. intros la f a Ha. unfold sel_t. apply (sel_at_gen la f). exact Ha. Qed.

Lemma sel_r_at : forall lr f a, In a lr -> sel_r lr f (oa (idx a lr)) = f a.
Proof. intros lr f a Ha. unfold sel_r. apply (sel_at_gen lr f). exact Ha. Qed.

Lemma sel_t_out : forall la f b,
  (forall a, In a la -> b <> oa (idx a la)) -> sel_t la f b = typ_Var b.
Proof. intros la f b H. unfold sel_t. exact (sel_out (fun a => oa (idx a la)) f b _ la H). Qed.

Lemma sel_r_out : forall lr f b,
  (forall a, In a lr -> b <> oa (idx a lr)) -> sel_r lr f b = row_Var b.
Proof. intros lr f b H. unfold sel_r. exact (sel_out (fun a => oa (idx a lr)) f b _ lr H). Qed.

Lemma fold_sel_P : forall {A : Type} (P : A -> Prop) (key : atom -> atom) (f : atom -> A) (d : A) b l,
  P d -> (forall a, In a l -> P (f a)) ->
  P (fold_right (fun a acc => if Atom.eq_dec b (key a) then f a else acc) d l).
Proof.
  intros A P key f d b l Hd Hf. induction l as [|a l IH]; [ exact Hd | ]. simpl.
  destruct (Atom.eq_dec b (key a)) as [_|_];
    [ apply Hf; left; reflexivity | apply IH; intros; apply Hf; right; assumption ].
Qed.

Lemma sel_t_lc : forall la f, (forall a, In a la -> lct 0 (f a)) -> forall b, lct 0 (sel_t la f b).
Proof.
  intros la f H b. unfold sel_t.
  apply (fold_sel_P (lct 0) (fun a => oa (idx a la)) f (typ_Var b) b la); [ exact I | exact H ].
Qed.

Lemma sel_r_lc : forall lr f, (forall a, In a lr -> lcr 0 (f a)) -> forall b, lcr 0 (sel_r lr f b).
Proof.
  intros lr f H b. unfold sel_r.
  apply (fold_sel_P (lcr 0) (fun a => oa (idx a lr)) f (row_Var b) b lr); [ exact I | exact H ].
Qed.

(* ---- what the comparison assumes of the contexts ---- *)

Definition frozen (S2 : sub) (Gp Gq : ctx) : Prop :=
  (forall a, a `in` ftv_ctx Gp ->
     ftv_typ (sT S2 a) [<=] ftv_ctx Gq /\ frv_typ (sT S2 a) [<=] frv_ctx Gq) /\
  (forall r, r `in` frv_ctx Gp ->
     ftv_row (sR S2 r) [<=] ftv_ctx Gq /\ frv_row (sR S2 r) [<=] frv_ctx Gq).

Definition even_ctx (G : ctx) : Prop :=
  (forall a, a `in` ftv_ctx G -> ev a) /\ (forall r, r `in` frv_ctx G -> ev r).

Section GenMono.
Variables (D Dal : denv) (S2 : sub) (Gp Gq : ctx) (T' : typ) (k : sort_fn) (rk : rkind_fn).
Hypotheses (HOk : OkS S2) (Hfz : frozen S2 Gp Gq) (Hev : even_ctx Gp).

Local Notation T1 := (apT S2 T').
Local Notation Vt := (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx Gq)).
Local Notation Vr := (AtomSetImpl.diff (frv_typ T1) (frv_ctx Gq)).
Local Notation la := (gen_vars_t Gp T').
Local Notation lr := (gen_vars_r Gp T').
Local Notation sa := (apS S2 (gen_ren Dal Gp T')).
Local Notation sd := (gen Gq T1 k rk).

Lemma gm_free_t : forall c,
  c `in` ftv_sch sa -> c `in` ftv_ctx Gq /\ c `in` ftv_typ T1.
Proof.
  intros c Hc. unfold ftv_sch in Hc. cbn [apS s_body s_tq] in Hc.
  apply AtomSetFacts.diff_iff in Hc as [Hc Hn]. unfold apT in Hc.
  destruct HOk as [_ [_ [_ [Hfx Hfxr]]]].
  apply ftv_ap_typ in Hc. destruct Hc as [[b [Hb Hc]]|[p [Hp Hc]]].
  - destruct (body_ftv Dal Gp T' b Hb) as [Hq|[Hb1 Hb2]].
    + exfalso. rewrite (Hfx b (not_ev_od b (gen_ren_od_t _ _ _ _ Hq))) in Hc. simpl in Hc.
      apply AtomSetFacts.singleton_iff in Hc. subst c. contradiction.
    + assert (Hbp : b `in` ftv_ctx Gp).
      { destruct (in_dec_set b (ftv_ctx Gp)) as [H|H]; [ exact H | exfalso; apply Hb2; apply In_la; auto ]. }
      split; [ exact (proj1 ((proj1 Hfz) b Hbp) c Hc) | ].
      unfold apT. exact (ftv_ap_in1 _ _ _ _ _ Hb1 Hc).
  - destruct (body_frv Dal Gp T' p Hp) as [Hq|[Hp1 Hp2]].
    + exfalso. rewrite (Hfxr p (not_ev_od p (gen_ren_od_r _ _ _ _ Hq))) in Hc. simpl in Hc. fsetdec.
    + assert (Hpp : p `in` frv_ctx Gp).
      { destruct (in_dec_set p (frv_ctx Gp)) as [H|H]; [ exact H | exfalso; apply Hp2; apply In_lr; auto ]. }
      split; [ exact (proj1 ((proj2 Hfz) p Hpp) c Hc) | ].
      unfold apT. exact (ftv_ap_in2 _ _ _ _ _ Hp1 Hc).
Qed.

Lemma gm_free_r : forall c,
  c `in` frv_sch sa -> c `in` frv_ctx Gq /\ c `in` frv_typ T1.
Proof.
  intros c Hc. unfold frv_sch in Hc. cbn [apS s_body s_rq] in Hc.
  apply AtomSetFacts.diff_iff in Hc as [Hc Hn]. unfold apT in Hc.
  destruct HOk as [_ [_ [_ [Hfx Hfxr]]]].
  apply frv_ap_typ in Hc. destruct Hc as [[b [Hb Hc]]|[p [Hp Hc]]].
  - destruct (body_ftv Dal Gp T' b Hb) as [Hq|[Hb1 Hb2]].
    + exfalso. rewrite (Hfx b (not_ev_od b (gen_ren_od_t _ _ _ _ Hq))) in Hc. simpl in Hc. fsetdec.
    + assert (Hbp : b `in` ftv_ctx Gp).
      { destruct (in_dec_set b (ftv_ctx Gp)) as [H|H]; [ exact H | exfalso; apply Hb2; apply In_la; auto ]. }
      split; [ exact (proj2 ((proj1 Hfz) b Hbp) c Hc) | ].
      unfold apT. exact (frv_ap_in1 _ _ _ _ _ Hb1 Hc).
  - destruct (body_frv Dal Gp T' p Hp) as [Hq|[Hp1 Hp2]].
    + exfalso. rewrite (Hfxr p (not_ev_od p (gen_ren_od_r _ _ _ _ Hq))) in Hc. simpl in Hc.
      apply AtomSetFacts.singleton_iff in Hc. subst c. contradiction.
    + assert (Hpp : p `in` frv_ctx Gp).
      { destruct (in_dec_set p (frv_ctx Gp)) as [H|H]; [ exact H | exfalso; apply Hp2; apply In_lr; auto ]. }
      split; [ exact (proj2 ((proj2 Hfz) p Hpp) c Hc) | ].
      unfold apT. exact (frv_ap_in2 _ _ _ _ _ Hp1 Hc).
Qed.

(* A substitution that fixes the even atoms and one that fixes the
   derivation's free variables agree on what [S2] sends a variable the
   algorithm keeps free to. *)
Lemma gm_id : forall st sr st' sr',
  (forall c, ev c -> st c = typ_Var c) -> (forall p, ev p -> sr p = row_Var p) ->
  (forall c, c `in` ftv_ctx Gq -> st' c = typ_Var c) ->
  (forall p, p `in` frv_ctx Gq -> sr' p = row_Var p) ->
  (forall a, a `in` ftv_ctx Gp -> ap_typ st sr (sT S2 a) = ap_typ st' sr' (sT S2 a)) /\
  (forall r, r `in` frv_ctx Gp -> ap_row st sr (sR S2 r) = ap_row st' sr' (sR S2 r)).
Proof.
  intros st sr st' sr' H1 H2 H3 H4.
  pose proof HOk as (_ & HE1 & HE2 & _). destruct Hfz as [Hf1 Hf2]. destruct Hev as [He1 He2].
  split.
  - intros a Ha. pose proof (HE1 a (He1 a Ha)) as [Ev1 Ev2].
    apply ap_typ_ext.
    + intros c Hc. rewrite (H1 c (Ev1 c Hc)). symmetry. apply H3. exact (proj1 (Hf1 a Ha) c Hc).
    + intros p Hp. rewrite (H2 p (Ev2 p Hp)). symmetry. apply H4. exact (proj2 (Hf1 a Ha) p Hp).
  - intros r Hr. pose proof (HE2 r (He2 r Hr)) as [Ev1 Ev2].
    apply (proj2 ap_ext_mut).
    + intros c Hc. rewrite (H1 c (Ev1 c Hc)). symmetry. apply H3. exact (proj1 (Hf2 r Hr) c Hc).
    + intros p Hp. rewrite (H2 p (Ev2 p Hp)). symmetry. apply H4. exact (proj2 (Hf2 r Hr) p Hp).
Qed.

Hypotheses (Hk : kres Dal (extr (ext D Vt k) Vr rk) (sT S2))
           (Hr : rkres Dal (extr (ext D Vt k) Vr rk) (sR S2)).

(* Every instance of the derivation's scheme is an instance of the algorithm's. *)
Lemma gm_inst : forall (D' : denv) T,
  (forall a, a `in` ftv_sch sd -> D' a = D a) ->
  (forall r, r `in` frv_sch sd -> drk D' r = drk D r) ->
  inst D' T sd -> inst D' T sa.
Proof.
  intros D' T Hda Hdr (st' & sr' & t1 & t2 & t3 & t4 & t5 & t6).
  cbn [gen s_tq s_rq s_body s_sk s_rk] in t1, t2, t3, t4, t5.
  pose proof HOk as (_ & HE1 & HE2 & Hfx & Hfxr).
  pose proof (OkS_lc S2 HOk) as [Hl1 Hl2].
  set (ft := fun a => ap_typ st' sr' (sT S2 a)).
  set (fr := fun r => ap_row st' sr' (sR S2 r)).
  assert (Hst : forall c, ev c -> sel_t la ft c = typ_Var c).
  { intros c Hc. apply sel_t_out. intros a' Ha' Heq. subst c. exact (ev_od _ Hc (od_oa _)). }
  assert (Hsr : forall c, ev c -> sel_r lr fr c = row_Var c).
  { intros c Hc. apply sel_r_out. intros a' Ha' Heq. subst c. exact (ev_od _ Hc (od_oa _)). }
  assert (Hq1 : forall c, c `in` ftv_ctx Gq -> st' c = typ_Var c).
  { intros c Hc. apply t1. intro Hd. apply AtomSetFacts.diff_iff in Hd. tauto. }
  assert (Hq2 : forall c, c `in` frv_ctx Gq -> sr' c = row_Var c).
  { intros c Hc. apply t2. intro Hd. apply AtomSetFacts.diff_iff in Hd. tauto. }
  destruct (gm_id (sel_t la ft) (sel_r lr fr) st' sr' Hst Hsr Hq1 Hq2) as [Gid Rid].
  exists (sel_t la ft), (sel_r lr fr).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - intros a Ha. apply sel_t_out. intros a' Ha' Heq. apply Ha. cbn [apS s_tq].
    apply gen_ren_tq. exists a'. split; assumption.
  - intros a Ha. apply sel_r_out. intros a' Ha' Heq. apply Ha. cbn [apS s_rq].
    apply gen_ren_rq. exists a'. split; assumption.
  - cbn [apS s_body]. rewrite gen_body. unfold apT in *. rewrite t3.
    rewrite !ap_typ_comp. apply ap_typ_ext.
    + intros a Ha. unfold tcomp, rename_t.
      destruct (in_dec Atom.eq_dec a la) as [Hin|Hin].
      * simpl. rewrite (Hfx _ (not_ev_od _ (od_oa _))). simpl.
        rewrite (sel_t_at la ft a Hin). reflexivity.
      * assert (Hap : a `in` ftv_ctx Gp).
        { destruct (in_dec_set a (ftv_ctx Gp)) as [H|H]; [ exact H | exfalso; apply Hin; apply In_la; auto ]. }
        simpl. exact (eq_sym (Gid a Hap)).
    + intros p Hp. unfold rcomp, rename_r.
      destruct (in_dec Atom.eq_dec p lr) as [Hin|Hin].
      * simpl. rewrite (Hfxr _ (not_ev_od _ (od_oa _))). simpl.
        rewrite (sel_r_at lr fr p Hin). reflexivity.
      * assert (Hap : p `in` frv_ctx Gp).
        { destruct (in_dec_set p (frv_ctx Gp)) as [H|H]; [ exact H | exfalso; apply Hin; apply In_lr; auto ]. }
        simpl. exact (eq_sym (Rid p Hap)).
  - intros a Ha. cbn [apS s_tq] in Ha. apply gen_ren_tq in Ha. destruct Ha as (b & Hb & ->).
    cbn [apS s_sk gen_ren]. rewrite (gen_sk_at Dal la b Hb). rewrite (sel_t_at la ft b Hb).
    assert (Hb' : b `in` ftv_typ T') by (apply In_la in Hb; tauto).
    refine (gm_sat D D' _ _ k rk st' sr' (Dal b) (sT S2 b) t1 t2 t4 t5 _ _ (Hk b)).
    + intros c Hc Hn. apply Hda. unfold ftv_sch. cbn [gen s_body s_tq].
      apply AtomSetFacts.diff_iff. split; [ | exact Hn ].
      unfold apT. exact (ftv_ap_in1 _ _ _ _ _ Hb' Hc).
    + intros p Hp Hn. apply Hdr. unfold frv_sch. cbn [gen s_body s_rq].
      apply AtomSetFacts.diff_iff. split; [ | exact Hn ].
      unfold apT. exact (frv_ap_in1 _ _ _ _ _ Hb' Hp).
  - intros a Ha. cbn [apS s_rq] in Ha. apply gen_ren_rq in Ha. destruct Ha as (b & Hb & ->).
    cbn [apS s_rk gen_ren]. rewrite (gen_rk_at Dal lr b Hb). rewrite (sel_r_at lr fr b Hb).
    assert (Hb' : b `in` frv_typ T') by (apply In_lr in Hb; tauto).
    refine (gm_rkok D D' _ _ k rk st' sr' (drk Dal b) (sR S2 b) t1 t2 t4 t5 _ _ (Hr b)).
    + intros c Hc Hn. apply Hda. unfold ftv_sch. cbn [gen s_body s_tq].
      apply AtomSetFacts.diff_iff. split; [ | exact Hn ].
      unfold apT. exact (ftv_ap_in2 _ _ _ _ _ Hb' Hc).
    + intros p Hp Hn. apply Hdr. unfold frv_sch. cbn [gen s_body s_rq].
      apply AtomSetFacts.diff_iff. split; [ | exact Hn ].
      unfold apT. exact (frv_ap_in2 _ _ _ _ _ Hb' Hp).
  - split.
    + intro b. apply sel_t_lc. intros a Ha. exact (ap_lc _ _ _ 0 t6 (Hl1 a)).
    + intro b. apply sel_r_lc. intros a Ha. exact (ap_lcr _ _ _ 0 t6 (Hl2 a)).
Qed.

(* The derivation's generalization is an instance of the algorithm's. *)
Theorem gen_mono : sch_le D sd sa.
Proof.
  split; [ | split ].
  - intros c Hc. destruct (gm_free_t c Hc) as [H1 H2].
    unfold ftv_sch. cbn [gen s_body s_tq]. apply AtomSetFacts.diff_iff.
    split; [ exact H2 | intro Hd; apply AtomSetFacts.diff_iff in Hd; exact (proj2 Hd H1) ].
  - intros c Hc. destruct (gm_free_r c Hc) as [H1 H2].
    unfold frv_sch. cbn [gen s_body s_rq]. apply AtomSetFacts.diff_iff.
    split; [ exact H2 | intro Hd; apply AtomSetFacts.diff_iff in Hd; exact (proj2 Hd H1) ].
  - intros D' Hd Hr' T H. exact (gm_inst D' T Hd Hr' H).
Qed.

End GenMono.

(* ---- the pin ---- *)

Lemma ftv_pin_of : forall l a, a `in` ftv_typ (pin_of l) <-> In a l.
Proof.
  induction l as [|b l IH]; intros a; simpl.
  - split; [ intro H; fsetdec | intros [] ].
  - rewrite AtomSetFacts.union_iff, AtomSetFacts.singleton_iff, IH.
    split; [ intros [H|H]; [ left; congruence | right; exact H ]
           | intros [H|H]; [ left; congruence | right; exact H ] ].
Qed.

Lemma frv_pin_of : forall l a, a `notin` frv_typ (pin_of l).
Proof. induction l as [|b l IH]; intros a; simpl; [ fsetdec | ]. specialize (IH a). fsetdec. Qed.

Lemma lit_vars_in : forall D T a,
  In a (lit_vars D T) <-> a `in` ftv_typ T /\ D a = k_Literal.
Proof.
  intros D T a. unfold lit_vars. rewrite filter_In, In_elements.
  split; intros [H1 H2]; split; try exact H1;
    destruct (D a); first [ exact H2 | discriminate H2 | reflexivity ].
Qed.

(* A type that satisfies [Literal] is a number type or a [Literal] variable. *)
Lemma sat_literal_shape : forall (D : denv) T,
  sat D k_Literal T -> T = typ_Int \/ T = typ_Float \/ exists c, T = typ_Var c /\ D c = k_Literal.
Proof.
  intros D T H. destruct T; simpl in H;
    first [ (left; reflexivity) | (right; left; reflexivity) | contradiction
          | (destruct H as [H|H]; discriminate H) | discriminate H | idtac ].
  right; right. exists a. split; [ reflexivity | ].
  inversion H; subst; reflexivity.
Qed.

(* The variables a [let] pins are frozen by the derivation: the derivation's
   [lit_pinned] premise says no variable it generalizes has the sort
   [Literal], and the sort [Dal] gives a pinned variable reaches the variable
   [S2] sends it to. *)
Lemma let_pin_frozen : forall (D Dal : denv) (S2 : sub) (Gq : ctx) e T' (k : sort_fn) (rk : rkind_fn),
  let_open e = false ->
  lit_pinned e (AtomSetImpl.diff (ftv_typ (apT S2 T')) (ftv_ctx Gq)) k ->
  kres Dal (extr (ext D (AtomSetImpl.diff (ftv_typ (apT S2 T')) (ftv_ctx Gq)) k)
                 (AtomSetImpl.diff (frv_typ (apT S2 T')) (frv_ctx Gq)) rk) (sT S2) ->
  forall a, a `in` ftv_typ (let_pin Dal e T') ->
    ftv_typ (sT S2 a) [<=] ftv_ctx Gq /\ frv_typ (sT S2 a) [<=] frv_ctx Gq.
Proof.
  intros D Dal S2 Gq e T' k rk Hopen Hlit Hk a Ha.
  unfold let_pin in Ha. rewrite Hopen in Ha. apply ftv_pin_of in Ha.
  apply lit_vars_in in Ha as [Hat Hal].
  pose proof (Hk a) as Hs. rewrite Hal in Hs.
  destruct (sat_literal_shape _ _ Hs) as [H|[H|[c [Hc Hdc]]]]; [ rewrite H | rewrite H | rewrite Hc ]; simpl.
  - split; intros x Hx; fsetdec.
  - split; intros x Hx; fsetdec.
  - split; intros x Hx; [ | fsetdec ].
    apply AtomSetFacts.singleton_iff in Hx. subst x.
    destruct (AtomSetProperties.In_dec c (ftv_ctx Gq)) as [Hin|Hn]; [ exact Hin | exfalso ].
    assert (Hcin : c `in` ftv_typ (apT S2 T')).
    { unfold apT. apply (ftv_ap_in1 (sT S2) (sR S2) T' c a Hat). rewrite Hc. simpl. fsetdec. }
    assert (Hv : c `in` AtomSetImpl.diff (ftv_typ (apT S2 T')) (ftv_ctx Gq))
      by (apply AtomSetFacts.diff_iff; split; assumption).
    rewrite extr_dsort in Hdc. rewrite (ext_in _ _ _ _ Hv) in Hdc.
    exact (Hlit Hopen c Hv Hdc).
Qed.

(* The contexts the let case compares are the contexts extended by pins. *)
Lemma frozen_pin : forall S2 Ga Gd Ta Tm,
  frozen S2 Ga Gd ->
  (forall a, a `in` ftv_typ Ta ->
     ftv_typ (sT S2 a) [<=] ftv_ctx (pin_ctx Tm Gd) /\ frv_typ (sT S2 a) [<=] frv_ctx (pin_ctx Tm Gd)) ->
  (forall r, r `in` frv_typ Ta ->
     ftv_row (sR S2 r) [<=] ftv_ctx (pin_ctx Tm Gd) /\ frv_row (sR S2 r) [<=] frv_ctx (pin_ctx Tm Gd)) ->
  frozen S2 (pin_ctx Ta Ga) (pin_ctx Tm Gd).
Proof.
  intros S2 Ga Gd Ta Tm [Hf1 Hf2] Ht Hr.
  pose proof (ftv_pin_ctx Ta Ga) as A1. pose proof (frv_pin_ctx Ta Ga) as A2.
  pose proof (ftv_pin_ctx Tm Gd) as B1. pose proof (frv_pin_ctx Tm Gd) as B2.
  split.
  - intros a Ha.
    assert (Hu : a `in` ftv_typ Ta \/ a `in` ftv_ctx Ga) by fsetdec.
    destruct Hu as [Hu|Hu]; [ exact (Ht a Hu) | ].
    destruct (Hf1 a Hu) as [H1 H2]. split; intros x Hx.
    + assert (x `in` ftv_ctx Gd) by (apply H1; exact Hx). fsetdec.
    + assert (x `in` frv_ctx Gd) by (apply H2; exact Hx). fsetdec.
  - intros r Hr0.
    assert (Hu : r `in` frv_typ Ta \/ r `in` frv_ctx Ga) by fsetdec.
    destruct Hu as [Hu|Hu]; [ exact (Hr r Hu) | ].
    destruct (Hf2 r Hu) as [H1 H2]. split; intros x Hx.
    + assert (x `in` ftv_ctx Gd) by (apply H1; exact Hx). fsetdec.
    + assert (x `in` frv_ctx Gd) by (apply H2; exact Hx). fsetdec.
Qed.
