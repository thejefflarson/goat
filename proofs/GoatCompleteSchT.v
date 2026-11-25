(* Completeness of algorithm W, stage 7.8f: schemes compared up to conversion
   (docs/design/phase7-proof-plan.md).

   After a step the algorithm's scheme is [apS (sfix S2) (apS s sc)] and the
   derivation's side is [apS (sfix Sg) sc].  Over the fragment their bodies are
   convertible, not equal: the field of an absent entry is free ([req_absf]), so
   the first may mention atoms the second does not.  [sch_leT] compares schemes
   up to [teq]: an instance of the derivation's scheme is convertible to an
   instance of the algorithm's, and the free atoms are compared on the
   canonical representatives [erT] (GoatCompleteEr.v), which a conversion leaves
   alone ([er_inv]).

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
Require Import Goat.GoatCompleteInst.
Require Import Goat.GoatCompleteGen.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteEr.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteBound.
Require Import Goat.GoatCompleteMono.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the representative's atoms across a substitution ---- *)

Lemma er_rf : forall T, rf T -> erT T = T.
Proof.
  induction T; simpl; intros H; try contradiction; try reflexivity.
  - destruct H as [H1 H2]. cbn [erT]. rewrite (IHT1 H1), (IHT2 H2). reflexivity.
Qed.

Lemma er_lc : (forall T k, lct k T -> lct k (erT T)) /\ (forall R k, lcr k R -> lcr k (erR R)).
Proof.
  apply typ_row_mutind; cbn [erT erR lct lcr]; try (intros; assumption).
  - intros A IHA B IHB k [HA HB]. split; [ apply IHA | apply IHB ]; assumption.
  - intros R IH k H. apply IH. exact H.
  - intros B IH k H. apply IH. exact H.
  - intros w A IH k H. apply IH. exact H.
  - intros l T IHT R IHR k [HT HR]. split; [ apply IHT | apply IHR ]; assumption.
  - intros l P IHP T IHT R IHR k [HP [HT HR]]. destruct (is_abs P) eqn:E; cbn [lct lcr].
    + split; [ exact HP | split; [ exact I | apply IHR; exact HR ] ].
    + split; [ apply IHP; exact HP | split; [ apply IHT; exact HT | apply IHR; exact HR ] ].
Qed.


(* The atoms of the representative of an image come from the representatives of
   the images of the variables: [proj] and [projR] read the type atoms or the
   row variables. *)
Definition ErAt (S : sub) (c : atom) (proj : typ -> atoms) (projR : row -> atoms)
  (xs rs : atoms) : Prop :=
  (exists x, x `in` xs /\ c `in` proj (erT (sT S x))) \/
  (exists r, r `in` rs /\ c `in` projR (erR (sR S r))).

Lemma ErAt_mono : forall S c proj projR xs xs' rs rs',
  xs [<=] xs' -> rs [<=] rs' -> ErAt S c proj projR xs rs -> ErAt S c proj projR xs' rs'.
Proof.
  intros S c proj projR xs xs' rs rs' Hx Hr [(x & Hx0 & H)|(r & Hr0 & H)];
    [ left; exists x | right; exists r ]; split; try exact H; [ apply Hx | apply Hr ]; assumption.
Qed.

Ltac erm H := eapply ErAt_mono; [ | | exact H ]; fsetdec.

Lemma er_ap_atoms : forall S,
  (forall T, pf T ->
     (forall c, c `in` ftv_typ (erT (apT S T)) -> ErAt S c ftv_typ ftv_row (ftv_typ T) (frv_typ T)) /\
     (forall c, c `in` frv_typ (erT (apT S T)) -> ErAt S c frv_typ frv_row (ftv_typ T) (frv_typ T))) /\
  (forall R, prf R ->
     (forall c, c `in` ftv_row (erR (apR S R)) -> ErAt S c ftv_typ ftv_row (ftv_row R) (frv_row R)) /\
     (forall c, c `in` frv_row (erR (apR S R)) -> ErAt S c frv_typ frv_row (ftv_row R) (frv_row R))).
Proof.
  intros S. apply typ_row_mutind; cbn [pf prf]; try (intros; contradiction);
    try (intros _; split; intros c Hc; cbn [apT ap_typ apR ap_row erT erR ftv_typ frv_typ ftv_row frv_row] in Hc; exfalso; fsetdec; fail).
  - (* arrow *)
    intros A IHA B IHB [PA PB]. destruct (IHA PA) as [A1 A2]. destruct (IHB PB) as [B1 B2].
    rewrite apT_Arrow. cbn [erT ftv_typ frv_typ]. split;
      (intros c Hc; apply AtomSetFacts.union_iff in Hc; destruct Hc as [Hc|Hc]);
      [ erm (A1 c Hc)
      | erm (B1 c Hc)
      | erm (A2 c Hc)
      | erm (B2 c Hc) ].
  - (* record *)
    intros R IH HR. destruct (IH HR) as [H1 H2].
    change (apT S (typ_Record R)) with (typ_Record (apR S R)). cbn [erT ftv_typ frv_typ]. split; assumption.
  - (* variable *)
    intros a _. rewrite apT_Var. split; intros c Hc; left; exists a; (split; [ simpl; fsetdec | exact Hc ]).
  - (* group *)
    intros w A IH [HA _]. destruct (IH HA) as [H1 H2].
    change (apT S (typ_Grp w A)) with (typ_Grp w (apT S A)). cbn [erT ftv_typ frv_typ]. split; assumption.
  - (* row variable *)
    intros r _. change (apR S (row_Var r)) with (sR S r). split; intros c Hc; right; exists r; (split; [ simpl; fsetdec | exact Hc ]).
  - (* present entry *)
    intros l T IHT R IHR [HT HR]. destruct (IHT HT) as [T1 T2]. destruct (IHR HR) as [R1 R2].
    change (apR S (row_Ext l T R)) with (row_Ext l (apT S T) (apR S R)). cbn [erR ftv_row frv_row]. split;
      (intros c Hc; apply AtomSetFacts.union_iff in Hc; destruct Hc as [Hc|Hc]);
      [ erm (T1 c Hc)
      | erm (R1 c Hc)
      | erm (T2 c Hc)
      | erm (R2 c Hc) ].
  - (* maybe entry *)
    intros l P IHP T IHT R IHR [HP [HT HR]]. destruct (IHP HP) as [P1 P2]. destruct (IHT HT) as [T1 T2]. destruct (IHR HR) as [R1 R2].
    change (apR S (row_Maybe l P T R)) with (row_Maybe l (apT S P) (apT S T) (apR S R)).
    cbn [erR]. destruct (is_abs (apT S P)) eqn:Ea.
    + apply abs_is_bool in Ea. rewrite Ea. cbn [ftv_row frv_row ftv_typ frv_typ erT]. split;
        (intros c Hc; apply AtomSetFacts.union_iff in Hc; destruct Hc as [Hc|Hc]; [ exfalso; fsetdec | ];
         apply AtomSetFacts.union_iff in Hc; destruct Hc as [Hc|Hc]; [ exfalso; fsetdec | ]).
      * erm (R1 c Hc).
      * erm (R2 c Hc).
    + cbn [ftv_row frv_row]. split;
        (intros c Hc; apply AtomSetFacts.union_iff in Hc; destruct Hc as [Hc|Hc]).
      * erm (P1 c Hc).
      * apply AtomSetFacts.union_iff in Hc. destruct Hc as [Hc|Hc];
          [ erm (T1 c Hc)
          | erm (R1 c Hc) ].
      * erm (P2 c Hc).
      * apply AtomSetFacts.union_iff in Hc. destruct Hc as [Hc|Hc];
          [ erm (T2 c Hc)
          | erm (R2 c Hc) ].
Qed.

(* ---- the transfer for row variables and the atoms' row variables ---- *)

Lemma er_ap_sub_frv : forall S,
  (forall T, pf T -> ps S T ->
     (forall x, x `in` ftv_typ T -> frv_typ (erT (sT S x)) [<=] frv_typ (erT (apT S T))) /\
     (forall r, r `in` frv_typ T -> frv_row (erR (sR S r)) [<=] frv_typ (erT (apT S T)))) /\
  (forall R, prf R -> psr S R ->
     (forall x, x `in` ftv_row R -> frv_typ (erT (sT S x)) [<=] frv_row (erR (apR S R))) /\
     (forall r, r `in` frv_row R -> frv_row (erR (sR S r)) [<=] frv_row (erR (apR S R)))).
Proof.
  intros S. apply typ_row_mutind; cbn [pf prf ps psr]; try (intros; contradiction);
    try (intros _ _; split; intros x Hx; simpl in Hx; fsetdec; fail).
  - intros A IHA B IHB [PA PB] [SA SB].
    destruct (IHA PA SA) as [A1 A2]. destruct (IHB PB SB) as [B1 B2].
    rewrite apT_Arrow. cbn [erT frv_typ ftv_typ]. split.
    + intros x Hx. apply AtomSetFacts.union_iff in Hx. destruct Hx as [Hx|Hx];
        [ pose proof (A1 x Hx) | pose proof (B1 x Hx) ]; fsetdec.
    + intros r Hr. apply AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr];
        [ pose proof (A2 r Hr) | pose proof (B2 r Hr) ]; fsetdec.
  - intros R IH HR PR. destruct (IH HR PR) as [H1 H2].
    change (apT S (typ_Record R)) with (typ_Record (apR S R)). cbn [erT frv_typ]. split; assumption.
  - intros a _ _. rewrite apT_Var. split.
    + intros x Hx. apply AtomSetFacts.singleton_iff in Hx. subst x. intros y Hy. exact Hy.
    + intros r Hr. exfalso. fsetdec.
  - intros w A IH [HA _] PA. destruct (IH HA PA) as [H1 H2].
    change (apT S (typ_Grp w A)) with (typ_Grp w (apT S A)). cbn [erT frv_typ]. split; assumption.
  - intros r _ _. change (apR S (row_Var r)) with (sR S r). split.
    + intros x Hx. exfalso. fsetdec.
    + intros q Hq. apply AtomSetFacts.singleton_iff in Hq. subst q. intros y Hy. exact Hy.
  - intros l T IHT R IHR [HT HR] [PT PR]. destruct (IHT HT PT) as [T1 T2]. destruct (IHR HR PR) as [R1 R2].
    change (apR S (row_Ext l T R)) with (row_Ext l (apT S T) (apR S R)). cbn [erR frv_row ftv_row]. split.
    + intros x Hx. apply AtomSetFacts.union_iff in Hx. destruct Hx as [Hx|Hx];
        [ pose proof (T1 x Hx) | pose proof (R1 x Hx) ]; fsetdec.
    + intros r Hr. apply AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr];
        [ pose proof (T2 r Hr) | pose proof (R2 r Hr) ]; fsetdec.
  - intros l P IHP T IHT R IHR [HP [HT HR]] [PP [PT PR]]. destruct (IHT HT PT) as [T1 T2]. destruct (IHR HR PR) as [R1 R2].
    change (apR S (row_Maybe l P T R)) with (row_Maybe l (apT S P) (apT S T) (apR S R)).
    rewrite PP. cbn [erR is_abs erT frv_row ftv_row frv_typ ftv_typ]. split.
    + intros x Hx. apply AtomSetFacts.union_iff in Hx. destruct Hx as [Hx|Hx].
      * destruct (pres_shape S P HP PP) as [->|[v [-> Hv]]].
        -- simpl in Hx. fsetdec.
        -- simpl in Hx. apply AtomSetFacts.singleton_iff in Hx. subst x. rewrite Hv. simpl. fsetdec.
      * apply AtomSetFacts.union_iff in Hx. destruct Hx as [Hx|Hx];
          [ pose proof (T1 x Hx) | pose proof (R1 x Hx) ]; fsetdec.
    + intros r Hr. apply AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr].
      * exfalso. exact (pres_frv S P r HP PP Hr).
      * apply AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr];
          [ pose proof (T2 r Hr) | pose proof (R2 r Hr) ]; fsetdec.
Qed.

(* What the derivation's type must mention of the images of an algorithm type's
   atoms: the atoms of their representatives lie in those of its representative. *)
Lemma vis_of_ps : forall S T T1, pf T -> ps S T -> teq (apT S T) T1 ->
  (forall x, x `in` ftv_typ T ->
     ftv_typ (erT (sT S x)) [<=] ftv_typ (erT T1) /\ frv_typ (erT (sT S x)) [<=] frv_typ (erT T1)) /\
  (forall r, r `in` frv_typ T ->
     ftv_row (erR (sR S r)) [<=] ftv_typ (erT T1) /\ frv_row (erR (sR S r)) [<=] frv_typ (erT T1)).
Proof.
  intros S T T1 HT PT Heq.
  destruct (proj1 er_inv _ _ Heq) as [E1 E2].
  pose proof (proj1 (er_ap_sub S) T HT PT) as (A1 & A2).
  pose proof (proj1 (er_ap_sub_frv S) T HT PT) as (B1 & B2). split.
  - intros x Hx. split; intros y Hy; [ apply E1; exact (A1 x Hx y Hy) | apply E2; exact (B1 x Hx y Hy) ].
  - intros r Hr. split; intros y Hy; [ apply E1; exact (A2 r Hr y Hy) | apply E2; exact (B2 r Hr y Hy) ].
Qed.

(* ---- the comparison ---- *)

Definition ftv_schE (s : scheme) : atoms := AtomSetImpl.diff (ftv_typ (erT (s_body s))) (s_tq s).
Definition frv_schE (s : scheme) : atoms := AtomSetImpl.diff (frv_typ (erT (s_body s))) (s_rq s).

Lemma ftv_schE_sub : forall s, ftv_schE s [<=] ftv_sch s.
Proof.
  intros s y Hy. unfold ftv_schE in Hy. unfold ftv_sch. apply AtomSetFacts.diff_iff in Hy as [H1 H2].
  apply AtomSetFacts.diff_iff. split; [ exact (proj1 (proj1 er_sub _) y H1) | exact H2 ].
Qed.

Lemma frv_schE_sub : forall s, frv_schE s [<=] frv_sch s.
Proof.
  intros s y Hy. unfold frv_schE in Hy. unfold frv_sch. apply AtomSetFacts.diff_iff in Hy as [H1 H2].
  apply AtomSetFacts.diff_iff. split; [ exact (proj2 (proj1 er_sub _) y H1) | exact H2 ].
Qed.

(* An instance whose type images satisfy [Pt] and whose row images are even. *)
Definition instT (Pt : typ -> Prop) (D : denv) (T : typ) (s : scheme) : Prop :=
  exists (st : tsub) (sr : rsub),
    (forall a, a `notin` s_tq s -> st a = typ_Var a) /\
    (forall r, r `notin` s_rq s -> sr r = row_Var r) /\
    T = ap_typ st sr (s_body s) /\
    (forall a, a `in` s_tq s -> sat D (s_sk s a) (st a)) /\
    (forall r, r `in` s_rq s -> rkok D (s_rk s r) (sr r)) /\
    lc_sub st sr /\
    (forall a, a `in` s_tq s -> Pt (st a)) /\
    (forall r, r `in` s_rq s -> EvR (sr r)).

Lemma instT_PEv : forall D T s, instT PEv D T s <-> instP D T s.
Proof. intros D T s. split; intro H; exact H. Qed.

(* [sd] is an instance of [sa] up to conversion: each instance of [sd] is
   convertible to an instance of [sa], and the free atoms of [sa]'s
   representative are free in [sd]'s. *)
Definition sch_leT (Pt : typ -> Prop) (D : denv) (sd sa : scheme) : Prop :=
  ftv_schE sa [<=] ftv_schE sd /\ frv_schE sa [<=] frv_schE sd /\
  forall D' : denv, (forall a, a `in` ftv_schE sd -> D' a = D a) ->
    (forall r, r `in` frv_schE sd -> drk D' r = drk D r) ->
    forall T, instT Pt D' T sd -> exists T', instT Pt D' T' sa /\ teq T T'.

Lemma sch_leT_refl : forall Pt D s, sch_leT Pt D s s.
Proof.
  intros Pt D s. split; [ fsetdec | split; [ fsetdec | ] ].
  intros D' _ _ T H. exists T. split; [ exact H | apply teq_refl ].
Qed.


Lemma sch_leT_trans : forall Pt D s1 s2 s3, sch_leT Pt D s1 s2 -> sch_leT Pt D s2 s3 -> sch_leT Pt D s1 s3.
Proof.
  intros Pt D s1 s2 s3 (A1 & B1 & C1) (A2 & B2 & C2).
  split; [ fsetdec | split; [ fsetdec | ] ].
  intros D' Hd Hr T H. destruct (C1 D' Hd Hr T H) as (T2 & H2 & E2).
  destruct (C2 D' (fun a Ha => Hd a (A1 a Ha)) (fun r Hrr => Hr r (B1 r Hrr)) T2 H2) as (T3 & H3 & E3).
  exists T3. split; [ exact H3 | exact (teq_trans _ _ _ E2 E3) ].
Qed.

Lemma sch_leT_inst : forall Pt D s s' T, sch_leT Pt D s s' -> instT Pt D T s ->
  exists T', instT Pt D T' s' /\ teq T T'.
Proof. intros Pt D s s' T (_ & _ & H) Hi. exact (H D (fun _ _ => eq_refl) (fun _ _ => eq_refl) T Hi). Qed.

Lemma sch_leT_env : forall Pt (D D2 : denv) s s',
  (forall a, a `in` ftv_schE s -> D2 a = D a) ->
  (forall r, r `in` frv_schE s -> drk D2 r = drk D r) ->
  sch_leT Pt D s s' -> sch_leT Pt D2 s s'.
Proof.
  intros Pt D D2 s s' Hv Hr (A & B & C). split; [ exact A | split; [ exact B | ] ].
  intros D' Hd Hdr T H. apply (C D'); [ | | exact H ].
  - intros a Ha. rewrite (Hd a Ha). apply Hv. exact Ha.
  - intros r Hrr. rewrite (Hdr r Hrr). apply Hr. exact Hrr.
Qed.

Lemma sch_leT_ext : forall Pt D V k s s',
  (forall a, a `in` ftv_schE s -> a `notin` V) ->
  sch_leT Pt D s s' -> sch_leT Pt (ext D V k) s s'.
Proof.
  intros Pt D V k s s' Hv H. eapply sch_leT_env; [ | | exact H ].
  - intros a Ha. apply ext_out. apply Hv. exact Ha.
  - intros r Hr. reflexivity.
Qed.

Lemma sch_leT_extr : forall Pt D V rk s s',
  (forall r, r `in` frv_schE s -> r `notin` V) ->
  sch_leT Pt D s s' -> sch_leT Pt (extr D V rk) s s'.
Proof.
  intros Pt D V rk s s' Hv H. eapply sch_leT_env; [ | | exact H ].
  - intros a Ha. reflexivity.
  - intros r Hr. unfold extr; simpl.
    destruct (AtomSetImpl.mem r V) eqn:Em; [ | reflexivity ].
    apply AtomSetFacts.mem_iff in Em. exfalso. apply (Hv r Hr). exact Em.
Qed.

(* On record-free schemes the old comparison is this one. *)
Lemma sch_leP_T : forall D s s', rf (s_body s) -> rf (s_body s') ->
  sch_leP D s s' -> sch_leT PEv D s s'.
Proof.
  intros D s s' Hs Hs' (A & B & C).
  assert (E1 : ftv_schE s = ftv_sch s) by (unfold ftv_schE, ftv_sch; rewrite (er_rf _ Hs); reflexivity).
  assert (E2 : frv_schE s = frv_sch s) by (unfold frv_schE, frv_sch; rewrite (er_rf _ Hs); reflexivity).
  assert (E3 : ftv_schE s' = ftv_sch s') by (unfold ftv_schE, ftv_sch; rewrite (er_rf _ Hs'); reflexivity).
  assert (E4 : frv_schE s' = frv_sch s') by (unfold frv_schE, frv_sch; rewrite (er_rf _ Hs'); reflexivity).
  unfold sch_leT. rewrite E1, E2, E3, E4. split; [ exact A | split; [ exact B | ] ].
  intros D' Hd Hr T H. exists T. split; [ | apply teq_refl ].
  exact (C D' Hd Hr T H).
Qed.

(* ---- what the comparison assumes of the contexts ---- *)

(* [frozen] (GoatCompleteMono.v) on representatives. *)
Definition frozenE (S2 : sub) (Gp Gq : ctx) : Prop :=
  (forall a, a `in` ftv_ctx Gp ->
     ftv_typ (erT (sT S2 a)) [<=] ftv_ctx Gq /\ frv_typ (erT (sT S2 a)) [<=] frv_ctx Gq) /\
  (forall r, r `in` frv_ctx Gp ->
     ftv_row (erR (sR S2 r)) [<=] ftv_ctx Gq /\ frv_row (erR (sR S2 r)) [<=] frv_ctx Gq).

Lemma frozen_E : forall S2 Gp Gq, frozen S2 Gp Gq -> frozenE S2 Gp Gq.
Proof.
  intros S2 Gp Gq [H1 H2]. split.
  - intros a Ha. destruct (H1 a Ha) as [A B]. destruct (proj1 er_sub (sT S2 a)) as [E1 E2].
    split; [ intros y Hy; apply A; apply E1; exact Hy | intros y Hy; apply B; apply E2; exact Hy ].
  - intros r Hr. destruct (H2 r Hr) as [A B]. destruct (proj2 er_sub (sR S2 r)) as [E1 E2].
    split; [ intros y Hy; apply A; apply E1; exact Hy | intros y Hy; apply B; apply E2; exact Hy ].
Qed.

Lemma frozenE_pin : forall S2 Ga Gd Ta Tm,
  frozenE S2 Ga Gd ->
  (forall a, a `in` ftv_typ Ta ->
     ftv_typ (erT (sT S2 a)) [<=] ftv_ctx (pin_ctx Tm Gd) /\ frv_typ (erT (sT S2 a)) [<=] frv_ctx (pin_ctx Tm Gd)) ->
  (forall r, r `in` frv_typ Ta ->
     ftv_row (erR (sR S2 r)) [<=] ftv_ctx (pin_ctx Tm Gd) /\ frv_row (erR (sR S2 r)) [<=] frv_ctx (pin_ctx Tm Gd)) ->
  frozenE S2 (pin_ctx Ta Ga) (pin_ctx Tm Gd).
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
