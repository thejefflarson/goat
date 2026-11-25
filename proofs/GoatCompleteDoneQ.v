(* Completeness of algorithm W, stage 7.8j: the induction's conclusion with the
   held equations packed into the result type
   (docs/design/phase7-proof-plan.md).

   [HOkC] (GoatCompleteHeld.v) does not step along a [SemW]: its step needs
   [Pkg], which speaks of every old atom, while a [SemW] speaks of the live
   ones, and the atoms of a held equation (a re-held equation's field variable
   and the atoms of its value) need not occur in the run's result type.  The
   conclusion [DoneQ] therefore states the type facts of the result packed with
   the equations' types ([pack]), whose atoms are the live set the next premise
   starts from.  [HOkC_stepW] then moves the equations along a step over that
   live set, and [seq_Q] is what each binary construct of the core (call,
   [let], [if], the operators) uses to compose two runs.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatSubst.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferW.
Require Import Goat.GoatHeld.
Require Import Goat.GoatCompleteHeld.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteLive.
Require Import Goat.GoatCompleteBound.
Require Import Goat.GoatCompleteCtxW.
Require Import Goat.GoatCompleteCtxP.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the equations' types as one type ---- *)

Definition heqs_ty (H : list heq) : typ :=
  fold_right (fun h acc => typ_Arrow (typ_Arrow (h_fld h) (h_val h)) acc) typ_Unit H.

Definition pack (T : typ) (H : list heq) : typ := typ_Arrow T (heqs_ty H).

Lemma ftv_heqs : forall H b, b `in` ftv_typ (heqs_ty H) ->
  exists h, In h H /\ (b `in` ftv_typ (h_fld h) \/ b `in` ftv_typ (h_val h)).
Proof.
  induction H as [|h H IH]; intros b Hb; [ simpl in Hb; fsetdec | ].
  simpl in Hb. repeat rewrite AtomSetFacts.union_iff in Hb.
  destruct Hb as [[Hb|Hb]|Hb].
  - exists h. split; [ left; reflexivity | left; exact Hb ].
  - exists h. split; [ left; reflexivity | right; exact Hb ].
  - destruct (IH b Hb) as (h' & Hh & Hb'). exists h'. split; [ right; exact Hh | exact Hb' ].
Qed.

Lemma frv_heqs : forall H b, b `in` frv_typ (heqs_ty H) ->
  exists h, In h H /\ (b `in` frv_typ (h_fld h) \/ b `in` frv_typ (h_val h)).
Proof.
  induction H as [|h H IH]; intros b Hb; [ simpl in Hb; fsetdec | ].
  simpl in Hb. repeat rewrite AtomSetFacts.union_iff in Hb.
  destruct Hb as [[Hb|Hb]|Hb].
  - exists h. split; [ left; reflexivity | left; exact Hb ].
  - exists h. split; [ left; reflexivity | right; exact Hb ].
  - destruct (IH b Hb) as (h' & Hh & Hb'). exists h'. split; [ right; exact Hh | exact Hb' ].
Qed.

Lemma heqs_ftv_in : forall H b h, In h H ->
  (b `in` ftv_typ (h_fld h) \/ b `in` ftv_typ (h_val h)) -> b `in` ftv_typ (heqs_ty H).
Proof.
  induction H as [|h0 H IH]; intros b h Hh Hb; [ inversion Hh | ].
  simpl. repeat rewrite AtomSetFacts.union_iff. destruct Hh as [<-|Hh].
  - destruct Hb as [Hb|Hb]; [ left; left; exact Hb | left; right; exact Hb ].
  - right. exact (IH b h Hh Hb).
Qed.

Lemma heqs_frv_in : forall H b h, In h H ->
  (b `in` frv_typ (h_fld h) \/ b `in` frv_typ (h_val h)) -> b `in` frv_typ (heqs_ty H).
Proof.
  induction H as [|h0 H IH]; intros b h Hh Hb; [ inversion Hh | ].
  simpl. repeat rewrite AtomSetFacts.union_iff. destruct Hh as [<-|Hh].
  - destruct Hb as [Hb|Hb]; [ left; left; exact Hb | left; right; exact Hb ].
  - right. exact (IH b h Hh Hb).
Qed.

Lemma pf_heqs : forall H, Forall (fun h => pf (h_fld h) /\ pf (h_val h)) H -> pf (heqs_ty H).
Proof.
  induction H as [|h H IH]; intros F; [ exact I | ]. inversion F as [|? ? (A & B) F']; subst.
  simpl. exact (conj (conj A B) (IH F')).
Qed.

Lemma ps_heqs : forall S H, Forall (fun h => ps S (h_fld h) /\ ps S (h_val h)) H -> ps S (heqs_ty H).
Proof.
  induction H as [|h H IH]; intros F; [ exact I | ]. inversion F as [|? ? (A & B) F']; subst.
  simpl. exact (conj (conj A B) (IH F')).
Qed.

Lemma pf_pack : forall T H, pf (pack T H) <-> pf T /\ pf (heqs_ty H).
Proof. intros T H. reflexivity. Qed.

Lemma ps_pack : forall S T H, ps S (pack T H) <-> ps S T /\ ps S (heqs_ty H).
Proof. intros S T H. reflexivity. Qed.

Lemma ftv_pack : forall T H, ftv_typ (pack T H) [=] ftv_typ T `union` ftv_typ (heqs_ty H).
Proof. intros T H. reflexivity. Qed.

Lemma frv_pack : forall T H, frv_typ (pack T H) [=] frv_typ T `union` frv_typ (heqs_ty H).
Proof. intros T H. reflexivity. Qed.

(* ---- the conclusion ---- *)

(* [DoneP] (GoatCompleteCtxP.v) with the result's type facts stated of
   [pack T H]: the run's step is a [SemW], the packed type is in the fragment
   with every entry present, and the equations the run holds are ones [dis]
   discharges.  A run that holds no equation is a [DoneP]'s with [pack T nil]
   the result type applied to [Unit]. *)
Definition DoneQ (L LR : atoms) (D1 : denv) (G : ctx) (e : exp) (D : denv) (n : nat)
  (Sg : sub) (T1 : typ) : Prop :=
  exists s D' n' S2 T e' H,
    Stable (fun f => infer true f D G e n = Some (s, D', T, n', e', H)) /\
    SemW evA evA L LR D1 Sg n s D' n' S2 /\
    pf (pack T H) /\ atT n' (pack T H) /\ ps S2 (pack T H) /\ EvT (pack T H) /\
    LiveG evA evA (ftv_typ (pack T H)) (frv_typ (pack T H)) D' D1 S2 /\
    HOkC S2 n' H /\ teq (apT S2 T) T1 /\ is_gen_value e' = is_gen_value e /\ let_open e' = let_open e.

Lemma DoneQ_P : forall L LR D1 G e D n Sg T1,
  DoneQ L LR D1 G e D n Sg T1 -> DoneP L LR D1 G e D n Sg T1.
Proof.
  intros L LR D1 G e D n Sg T1 (s & D' & n' & S2 & T & e' & H & Hst & Hsem & Hpf & Hat & Hps & Hev & Hlv & Hok & Ht & Hg & Hl).
  exists s, D', n', S2, T, e', H.
  refine (conj Hst (conj Hsem (conj (proj1 Hpf) (conj _ (conj (proj1 Hps) (conj _ (conj _ (conj Hok (conj Ht (conj Hg Hl))))))))));
    [ split; [ intros x Hx; apply (proj1 Hat); simpl; fsetdec | intros x Hx; apply (proj2 Hat); simpl; fsetdec ]
    | split; [ intros x Hx; apply (proj1 Hev); simpl; fsetdec | intros x Hx; apply (proj2 Hev); simpl; fsetdec ]
    | eapply LiveG_mono; [ | | exact Hlv ]; intros x Hx; simpl; fsetdec ].
Qed.

(* ---- the equations along a step ---- *)

Definition EqLive (L LR : atoms) (H : list heq) : Prop :=
  ftv_typ (heqs_ty H) [<=] L /\ frv_typ (heqs_ty H) [<=] LR.

Lemma EqLive_tail : forall L LR h H, EqLive L LR (h :: H) -> EqLive L LR H.
Proof.
  intros L LR h H [A B]. split; intros x Hx; [ apply A | apply B ]; simpl; fsetdec.
Qed.

Lemma HOkC_stepW : forall L LR DT Sg n s D' n' S2 H,
  SemW evA evA L LR DT Sg n s D' n' S2 -> HOkC Sg n H -> EqLive L LR H ->
  HOkC S2 n' (apH s H).
Proof.
  intros L LR DT Sg n s D' n' S2 H Hs. induction H as [|h H IH]; intros Hk Hl; simpl; [ constructor | ].
  inversion Hk as [|h' H' Hh Hrest]; subst. constructor.
  - intros Hb. cbn [apE h_pres] in Hb.
    destruct (Hh (is_bool_ap s _ Hb)) as (F1 & V1 & A1 & AV & P1 & PV & Ht).
    destruct Hl as [HlT HlR].
    assert (Hf : ftv_typ (h_fld h) [<=] L /\ frv_typ (h_fld h) [<=] LR /\
                 ftv_typ (h_val h) [<=] L /\ frv_typ (h_val h) [<=] LR).
    { simpl in HlT, HlR. repeat split; intros x Hx; [ apply HlT | apply HlR | apply HlT | apply HlR ]; fsetdec. }
    destruct Hf as (f1 & f2 & f3 & f4).
    pose proof (SemW_SIg _ _ _ _ _ _ _ _ _ _ _ Hs) as SI.
    destruct (SemG_ap_T Sg S2 s n n' L LR _ SI f1 f2 F1 P1 (SemW_F _ _ _ _ _ _ _ _ _ _ _ Hs)) as (F2 & A2 & P2).
    destruct (SemG_ap_T Sg S2 s n n' L LR _ SI f3 f4 V1 PV (SemW_F _ _ _ _ _ _ _ _ _ _ _ Hs)) as (V2 & AV2 & PV2).
    refine (conj F2 (conj V2 (conj A2 (conj AV2 (conj P2 (conj PV2 _)))))).
    cbn [apE h_fld h_val].
    eapply teq_trans; [ apply teq_sym; exact (SemW_factor _ _ _ _ _ _ _ _ _ _ _ _ Hs f1 f2) | ].
    eapply teq_trans; [ exact Ht | exact (SemW_factor _ _ _ _ _ _ _ _ _ _ _ _ Hs f3 f4) ].
  - exact (IH Hrest (EqLive_tail _ _ _ _ Hl)).
Qed.

(* Two runs in sequence: the steps compose, and the equations of the first, moved
   along the second step, are held beside the second's.  [Lm] and [LRm] are the
   second premise's live sets, which the first run's result type packed with its
   equations lies in. *)
Lemma seq_Q : forall L LR Lm LRm DT Sg n s1 D1 n1 S1 s2 D2 n2 S2 H1 H2,
  SemW evA evA L LR DT Sg n s1 D1 n1 S1 -> limgT s1 L LR [<=] Lm -> limgR s1 L LR [<=] LRm ->
  SemW evA evA Lm LRm DT S1 n1 s2 D2 n2 S2 ->
  HOkC S1 n1 H1 -> EqLive Lm LRm H1 -> HOkC S2 n2 H2 ->
  SemW evA evA L LR DT Sg n (scomp s2 s1) D2 n2 S2 /\ HOkC S2 n2 (apH s2 H1 ++ H2).
Proof.
  intros L LR Lm LRm DT Sg n s1 D1 n1 S1 s2 D2 n2 S2 H1 H2 Hs1 HT HR Hs2 Hk1 Hl Hk2.
  refine (conj (SemW_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs1 HT HR Hs2) _).
  unfold HOkC. apply Forall_app. split; [ exact (HOkC_stepW _ _ _ _ _ _ _ _ _ _ Hs2 Hk1 Hl) | exact Hk2 ].
Qed.
