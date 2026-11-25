(* Completeness of algorithm W, stage 7.8f: the contexts and the [let] case
   compared up to conversion (docs/design/phase7-proof-plan.md).

   [CIT] is [CI] (GoatCompleteCtx.v) with the scheme comparison [sch_leT]
   (GoatCompleteSchT.v) and a monotype compared at plain [teq]: a derivation's
   binding is a type convertible to the algorithm's image, or a scheme of
   which an instance is convertible to an instance of what the algorithm's
   scheme becomes.  [CIT_env] moves it to another environment and
   [CIT_frozen] reads the derivation's context off it: the representatives of
   the images of the atoms of the algorithm's context lie in the derivation's
   ([frozenE]).  [gen_mono_letT] is [gen_mono_let] (GoatCompleteLet.v) for the
   comparison up to conversion.

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
Require Import Goat.GoatCompleteInst.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteEr.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteLive.
Require Import Goat.GoatCompleteBound.
Require Import Goat.GoatCompleteMono.
Require Import Goat.GoatCompleteLet.
Require Import Goat.GoatCompleteSchT.
Require Import Goat.GoatCompleteMonoT.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the [let] case ---- *)

(* The variables a [let] pins are frozen by the derivation, on representatives:
   a pinned variable is sent to a number type or to a [Literal] variable, which
   the representative of the image of the type mentions, hence the
   representative of the derivation's type. *)
Lemma let_pin_frozenT : forall (D Dal : denv) (S2 : sub) (Gq : ctx) e T' T1 (k : sort_fn) (rk : rkind_fn),
  pf T' -> ps S2 T' -> teq T1 (apT S2 T') ->
  let_open e = false ->
  lit_pinned e (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx Gq)) k ->
  (forall b, b `in` ftv_typ T' ->
     sat (extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx Gq)) k)
               (AtomSetImpl.diff (frv_typ T1) (frv_ctx Gq)) rk) (Dal b) (sT S2 b)) ->
  forall a, a `in` ftv_typ (let_pin Dal e T') ->
    ftv_typ (erT (sT S2 a)) [<=] ftv_ctx Gq /\ frv_typ (erT (sT S2 a)) [<=] frv_ctx Gq.
Proof.
  intros D Dal S2 Gq e T' T1 k rk Hpf Hps Hteq Hopen Hlit Hk a Ha.
  unfold let_pin in Ha. rewrite Hopen in Ha. apply ftv_pin_of in Ha.
  apply lit_vars_in in Ha as [Hat Hal].
  pose proof (Hk a Hat) as Hs. rewrite Hal in Hs.
  destruct (sat_literal_shape _ _ Hs) as [H|[H|[c [Hc Hdc]]]]; [ rewrite H | rewrite H | rewrite Hc ]; simpl.
  - split; intros x Hx; fsetdec.
  - split; intros x Hx; fsetdec.
  - split; intros x Hx; [ | fsetdec ].
    apply AtomSetFacts.singleton_iff in Hx. subst x.
    destruct (AtomSetProperties.In_dec c (ftv_ctx Gq)) as [Hin|Hn]; [ exact Hin | exfalso ].
    destruct (vis_of_ps S2 T' T1 Hpf Hps (teq_sym _ _ Hteq)) as [Hv _].
    pose proof (proj1 (Hv a Hat)) as Hsub.
    assert (Hcer : c `in` ftv_typ (erT (sT S2 a))) by (rewrite Hc; simpl; fsetdec).
    assert (Hc1 : c `in` ftv_typ T1) by exact (proj1 (proj1 er_sub T1) c (Hsub c Hcer)).
    assert (Hv' : c `in` AtomSetImpl.diff (ftv_typ T1) (ftv_ctx Gq))
      by (apply AtomSetFacts.diff_iff; split; assumption).
    rewrite extr_dsort in Hdc. rewrite (ext_in _ _ _ _ Hv') in Hdc.
    exact (Hlit Hopen c Hv' Hdc).
Qed.

Lemma let_frozenT : forall (D Dal : denv) (S2 : sub) (Ga Gd : ctx) (Tm T' T1 : typ) e
  (k : sort_fn) (rk : rkind_fn),
  frozenE S2 Ga Gd -> pf T' -> ps S2 T' -> teq T1 (apT S2 T') ->
  lit_pinned e (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm Gd))) k ->
  (forall b, b `in` ftv_typ T' ->
     sat (extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm Gd))) k)
               (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm Gd))) rk) (Dal b) (sT S2 b)) ->
  frozenE S2 (pin_ctx (let_pin Dal e T') Ga) (pin_ctx Tm Gd).
Proof.
  intros D Dal S2 Ga Gd Tm T' T1 e k rk Hfz Hpf Hps Hteq Hlit Hk.
  apply frozenE_pin; [ exact Hfz | | ].
  - intros a Ha. destruct (let_open e) eqn:Eo.
    + unfold let_pin in Ha. rewrite Eo in Ha. simpl in Ha. fsetdec.
    + exact (let_pin_frozenT D Dal S2 _ e T' T1 k rk Hpf Hps Hteq Eo Hlit Hk a Ha).
  - intros r Hr0. exfalso. apply (let_pin_frv Dal e T' r Hr0).
Qed.

Section LetT.
Variables (Pt : typ -> Prop).
Hypotheses
  (HPlc : forall X, Pt X -> lct 0 X)
  (HPev : forall X, Pt X -> EvT X)
  (HPer : forall X, Pt X -> Pt (erT X))
  (HPvar : forall c, ev c -> Pt (typ_Var c))
  (HPap : forall st sr X, lc_sub st sr -> Pt X ->
            (forall c, c `in` ftv_typ X -> Pt (st c)) ->
            (forall p, p `in` frv_typ X -> EvR (sr p)) -> Pt (ap_typ st sr X)).

(* [gen_mono_let] for the comparison up to conversion: the derivation's type
   [T1] is only convertible to the image of the algorithm's. *)
Theorem gen_mono_letT : forall (D Dal : denv) (S2 : sub) (Ga Gd : ctx) (Tm T' T1 : typ) e
  (k : sort_fn) (rk : rkind_fn),
  frozenE S2 Ga Gd -> pf T' -> ps S2 T' -> teq T1 (apT S2 T') ->
  (forall b, b `in` s_tq (gen_ren Dal (pin_ctx (let_pin Dal e T') Ga) T') -> sT S2 b = typ_Var b) ->
  (forall r, r `in` s_rq (gen_ren Dal (pin_ctx (let_pin Dal e T') Ga) T') -> sR S2 r = row_Var r) ->
  (forall a, a `in` ftv_ctx (pin_ctx (let_pin Dal e T') Ga) -> EvT (sT S2 a)) ->
  (forall r, r `in` frv_ctx (pin_ctx (let_pin Dal e T') Ga) -> EvR (sR S2 r)) ->
  (forall a, a `in` ftv_typ T' -> Pt (sT S2 a)) ->
  (forall r, r `in` frv_typ T' -> EvR (sR S2 r) /\ lcr 0 (sR S2 r)) ->
  lit_pinned e (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm Gd))) k ->
  (forall b, b `in` ftv_typ T' ->
     sat (extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm Gd))) k)
               (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm Gd))) rk) (Dal b) (sT S2 b)) ->
  (forall r, r `in` frv_typ T' ->
     rkok (extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm Gd))) k)
                (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm Gd))) rk) (drk Dal r) (sR S2 r)) ->
  sch_leT Pt D (gen (pin_ctx Tm Gd) T1 k rk)
               (apS S2 (gen_ren Dal (pin_ctx (let_pin Dal e T') Ga) T')).
Proof.
  intros D Dal S2 Ga Gd Tm T' T1 e k rk Hfz Hpf Hps Hteq HFt HFr HEt HEr HPt HPr Hlit Hk Hr.
  refine (gen_monoT Pt D Dal S2 _ _ T' T1 k rk HPlc HPev HPer HPvar HPap _ Hpf Hps Hteq HFt HFr HEt HEr HPt HPr Hk Hr).
  exact (let_frozenT D Dal S2 Ga Gd Tm T' T1 e k rk Hfz Hpf Hps Hteq Hlit Hk).
Qed.

End LetT.

(* ---- the contexts ---- *)

Definition SchIT (Pt : typ -> Prop) (D1 : denv) (Sg : sub) (sd sc : scheme) : Prop :=
  sch_leT Pt D1 sd (apS (sfix (s_tq sc) Sg) sc).

Definition CIT (Pt : typ -> Prop) (D1 : denv) (Sg : sub) (G1 G : ctx) : Prop :=
  Forall2 (fun b1 b => fst b1 = fst b /\
     ((exists T1 T, snd b1 = sch_mono T1 /\ snd b = sch_mono T /\ teq (apT Sg T) T1) \/
      SchIT Pt D1 Sg (snd b1) (snd b))) G1 G.

(* The step [var_sch_done] takes at a variable: an instance of the derivation's
   scheme is convertible to an instance of what the algorithm's becomes. *)
Lemma SchIT_inst : forall Pt D Sg sd sc T, SchIT Pt D Sg sd sc -> instT Pt D T sd ->
  exists T', instT Pt D T' (apS (sfix (s_tq sc) Sg) sc) /\ teq T T'.
Proof. intros Pt D Sg sd sc T H Hi. exact (sch_leT_inst Pt D _ _ T H Hi). Qed.

Lemma CIT_nil : forall Pt D1 Sg, CIT Pt D1 Sg nil nil.
Proof. intros. constructor. Qed.

Lemma CIT_cons : forall Pt D1 Sg G1 G x T1 T,
  CIT Pt D1 Sg G1 G -> teq (apT Sg T) T1 ->
  CIT Pt D1 Sg ((x ~ sch_mono T1) ++ G1) ((x ~ sch_mono T) ++ G).
Proof.
  intros Pt D1 Sg G1 G x T1 T H Ht. constructor; [ | exact H ].
  simpl. split; [ reflexivity | left; exists T1, T; repeat split; exact Ht ].
Qed.

Lemma CIT_cons_sch : forall Pt D1 Sg G1 G x sd sc,
  CIT Pt D1 Sg G1 G -> SchIT Pt D1 Sg sd sc ->
  CIT Pt D1 Sg ((x ~ sd) ++ G1) ((x ~ sc) ++ G).
Proof.
  intros Pt D1 Sg G1 G x sd sc H Hs. constructor; [ | exact H ].
  simpl. split; [ reflexivity | right; exact Hs ].
Qed.

Lemma CIT_dom : forall Pt D1 Sg G1 G, CIT Pt D1 Sg G1 G -> dom G1 [=] dom G.
Proof.
  intros Pt D1 Sg G1 G H. induction H as [|[x s1] [y s] G1 G [Hk _] _ IH]; simpl in *; [ reflexivity | ].
  subst y. rewrite IH. reflexivity.
Qed.

(* A derivation's context read at another environment. *)
Lemma CIT_env : forall Pt (Dd Dg : denv) Sg G1 G, CIT Pt Dd Sg G1 G ->
  (forall a, a `in` ftv_ctx G1 -> Dg a = Dd a) -> (forall r, r `in` frv_ctx G1 -> drk Dg r = drk Dd r) ->
  CIT Pt Dg Sg G1 G.
Proof.
  intros Pt Dd Dg Sg G1 G H Hs Hr.
  induction H as [|[x s1] [y sc] G1 G [Hk Hrel] _ IH]; [ constructor | ].
  constructor.
  - simpl in *. split; [ exact Hk | ]. destruct Hrel as [(T1 & T & E1 & E2 & Ht)|Hsch].
    + left. exists T1, T. split; [ exact E1 | split; [ exact E2 | exact Ht ] ].
    + right. eapply (sch_leT_env Pt Dd Dg); [ | | exact Hsch ].
      * intros a Ha. apply Hs. apply AtomSetFacts.union_iff. left. exact (ftv_schE_sub _ a Ha).
      * intros r Hrr. apply Hr. apply AtomSetFacts.union_iff. left. exact (frv_schE_sub _ r Hrr).
  - apply IH.
    + intros a Ha. apply Hs. simpl. apply AtomSetFacts.union_iff. right. exact Ha.
    + intros r Ha. apply Hr. simpl. apply AtomSetFacts.union_iff. right. exact Ha.
Qed.

(* What the algorithm's context must satisfy for the derivation's to hold the
   atoms of the images' representatives: its bodies are in the fragment, every
   entry present under the substitution that fixes the quantified atoms, and
   its schemes are well formed. *)
Definition GPsT (Sg : sub) (G : ctx) : Prop :=
  Forall (fun b => WfSch (snd b) /\ pf (s_body (snd b)) /\
                   ps (sfix (s_tq (snd b)) Sg) (s_body (snd b))) G.

Lemma ps_sfix_nil : forall Sg T, pf T -> ps (sfix {} Sg) T -> ps Sg T.
Proof.
  intros Sg T Hp Hs. refine (proj1 (ps_agree (sfix {} Sg) Sg) T Hp _ Hs).
  intros x _. cbn [sfix sT]. destruct (AtomSetImpl.mem x {}) eqn:E; [ | reflexivity ].
  exfalso. apply AtomSetFacts.mem_iff in E. revert E. fsetdec.
Qed.

Lemma GPsT_cons_mono : forall Sg x T G, pf T -> ps Sg T -> EvT T -> GPsT Sg G ->
  GPsT Sg ((x ~ sch_mono T) ++ G).
Proof.
  intros Sg x T G Hp Hs He HG. constructor; [ | exact HG ]. cbn [snd s_body s_tq sch_mono].
  refine (conj (WfSch_mono T He) (conj Hp _)).
  refine (proj1 (ps_agree Sg (sfix {} Sg)) T Hp _ Hs).
  intros y _. cbn [sfix sT]. destruct (AtomSetImpl.mem y {}) eqn:E; [ | reflexivity ].
  exfalso. apply AtomSetFacts.mem_iff in E. revert E. fsetdec.
Qed.

(* The derivation's context holds every atom the representatives of the images
   of the algorithm's context mention. *)
Lemma CIT_frozen : forall Pt (D1 : denv) Sg G1 G, CIT Pt D1 Sg G1 G -> GPsT Sg G ->
  (forall a, a `in` ftv_ctx G -> EvT (sT Sg a)) -> (forall r, r `in` frv_ctx G -> EvR (sR Sg r)) ->
  frozenE Sg G G1.
Proof.
  intros Pt D1 Sg G1 G H. induction H as [|[x s1] [y sc] G1 G [Hk Hrel] _ IH]; intros HP HEt HEr.
  - split; intros a Ha; simpl in Ha; exfalso; revert Ha; fsetdec.
  - inversion HP as [|b G' (Hw & Hpf & Hps) HP' Eb]; subst. simpl in *. subst y.
    destruct (IH HP' (fun a Ha => HEt a (proj2 (AtomSetFacts.union_iff _ _ _) (or_intror Ha)))
                    (fun r Ha => HEr r (proj2 (AtomSetFacts.union_iff _ _ _) (or_intror Ha)))) as [IH1 IH2].
    set (q := s_tq sc) in *.
    (* the head binding's contribution *)
    assert (Head : (forall a, a `in` ftv_sch sc ->
                      ftv_typ (erT (sT Sg a)) [<=] ftv_ctx ((fst (x, s1) ~ s1) ++ G1) /\
                      frv_typ (erT (sT Sg a)) [<=] frv_ctx ((fst (x, s1) ~ s1) ++ G1)) /\
                   (forall r, r `in` frv_sch sc ->
                      ftv_row (erR (sR Sg r)) [<=] ftv_ctx ((fst (x, s1) ~ s1) ++ G1) /\
                      frv_row (erR (sR Sg r)) [<=] frv_ctx ((fst (x, s1) ~ s1) ++ G1))).
    { cbn [fst]. destruct Hrel as [(T1 & T & E1 & E2 & Ht)|Hsch].
      - subst s1 sc. cbn [snd s_body s_tq sch_mono] in Hpf, Hps.
        pose proof (ps_sfix_nil Sg T Hpf Hps) as HsT.
        destruct (vis_of_ps Sg T T1 Hpf HsT Ht) as [Hv1 Hv2].
        assert (Hsub1 : ftv_typ T1 [<=] ftv_ctx ((x ~ sch_mono T1) ++ G1))
          by (intros y Hy; simpl; apply AtomSetFacts.union_iff; left; apply (proj2 (ftv_sch_mono _ y)); exact Hy).
        assert (Hsub2 : frv_typ T1 [<=] frv_ctx ((x ~ sch_mono T1) ++ G1))
          by (intros y Hy; simpl; apply AtomSetFacts.union_iff; left; unfold frv_sch; cbn [sch_mono s_body s_rq];
              apply AtomSetFacts.diff_iff; split; [ exact Hy | fsetdec ]).
        pose proof (proj1 er_sub T1) as (Er1 & Er2).
        split.
        + intros a Ha. apply (proj1 (ftv_sch_mono T a)) in Ha. destruct (Hv1 a Ha) as [A B]. split;
            [ intros y Hy; apply Hsub1; apply Er1; apply A; exact Hy | intros y Hy; apply Hsub2; apply Er2; apply B; exact Hy ].
        + intros r Hr0. unfold frv_sch in Hr0. cbn [sch_mono s_body s_rq] in Hr0.
          apply AtomSetFacts.diff_iff in Hr0 as [Hr0 _]. destruct (Hv2 r Hr0) as [A B]. split;
            [ intros y Hy; apply Hsub1; apply Er1; apply A; exact Hy | intros y Hy; apply Hsub2; apply Er2; apply B; exact Hy ].
      - destruct Hsch as (A & B & _).
        pose proof (er_ap_sub (sfix (s_tq sc) Sg)) as (Hap & _).
        pose proof (proj1 (er_ap_sub_frv (sfix (s_tq sc) Sg)) (s_body sc) Hpf Hps) as (Fa & Fr).
        pose proof (Hap (s_body sc) Hpf Hps) as (Ta & Tr).
        destruct Hw as (Hq & Hqr & _).
        split.
        + intros a Ha. unfold ftv_sch in Ha. apply AtomSetFacts.diff_iff in Ha as [Haf Haq].
          assert (Hs' : sT (sfix (s_tq sc) Sg) a = sT Sg a) by (apply sfix_out; exact Haq).
          pose proof (HEt a ltac:(simpl; apply AtomSetFacts.union_iff; left; unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption)) as [Ev1 Ev2].
          pose proof (proj1 er_sub (sT Sg a)) as (Er1 & Er2).
          split.
          * intros c Hc. simpl. apply AtomSetFacts.union_iff. left. apply ftv_schE_sub.
            apply A. unfold ftv_schE. cbn [apS s_body s_tq]. apply AtomSetFacts.diff_iff. split.
            -- apply (Ta a Haf). rewrite Hs'. exact Hc.
            -- intro Hcq. exact (ev_od c (Ev1 c (Er1 c Hc)) (Hq c Hcq)).
          * intros c Hc. simpl. apply AtomSetFacts.union_iff. left. apply frv_schE_sub.
            apply B. unfold frv_schE. cbn [apS s_body s_rq]. apply AtomSetFacts.diff_iff. split.
            -- apply (Fa a Haf). rewrite Hs'. exact Hc.
            -- intro Hcq. exact (ev_od c (Ev2 c (Er2 c Hc)) (Hqr c Hcq)).
        + intros r Hr0. unfold frv_sch in Hr0. apply AtomSetFacts.diff_iff in Hr0 as [Hrf Hrq].
          assert (Hs' : sR (sfix (s_tq sc) Sg) r = sR Sg r) by reflexivity.
          pose proof (HEr r ltac:(simpl; apply AtomSetFacts.union_iff; left; unfold frv_sch; apply AtomSetFacts.diff_iff; split; assumption)) as [Ev1 Ev2].
          pose proof (proj2 er_sub (sR Sg r)) as (Er1 & Er2).
          split.
          * intros c Hc. simpl. apply AtomSetFacts.union_iff. left. apply ftv_schE_sub.
            apply A. unfold ftv_schE. cbn [apS s_body s_tq]. apply AtomSetFacts.diff_iff. split.
            -- apply (Tr r Hrf). exact Hc.
            -- intro Hcq. exact (ev_od c (Ev1 c (Er1 c Hc)) (Hq c Hcq)).
          * intros c Hc. simpl. apply AtomSetFacts.union_iff. left. apply frv_schE_sub.
            apply B. unfold frv_schE. cbn [apS s_body s_rq]. apply AtomSetFacts.diff_iff. split.
            -- apply (Fr r Hrf). exact Hc.
            -- intro Hcq. exact (ev_od c (Ev2 c (Er2 c Hc)) (Hqr c Hcq)). }
    destruct Head as [Hd1 Hd2].
    split.
    + intros a Ha. simpl in Ha. apply AtomSetFacts.union_iff in Ha as [Ha|Ha].
      * destruct (Hd1 a Ha) as [A B]. split;
          [ intros c Hc; exact (A c Hc) | intros c Hc; exact (B c Hc) ].
      * destruct (IH1 a Ha) as [A B]. split;
          [ intros c Hc; simpl; apply AtomSetFacts.union_iff; right; exact (A c Hc)
          | intros c Hc; simpl; apply AtomSetFacts.union_iff; right; exact (B c Hc) ].
    + intros r Hr0. simpl in Hr0. apply AtomSetFacts.union_iff in Hr0 as [Hr0|Hr0].
      * destruct (Hd2 r Hr0) as [A B]. split;
          [ intros c Hc; exact (A c Hc) | intros c Hc; exact (B c Hc) ].
      * destruct (IH2 r Hr0) as [A B]. split;
          [ intros c Hc; simpl; apply AtomSetFacts.union_iff; right; exact (A c Hc)
          | intros c Hc; simpl; apply AtomSetFacts.union_iff; right; exact (B c Hc) ].
Qed.
