(* The typed converse of [erase_step] (phase 5, stage 4, part 2;
   docs/design/phase5-proof-plan.md, section 2.3).

   [erase_step] reads an elaborated step as a step of the source program.  The
   converse says the elaborated term can follow the source program: if a
   well-typed elaborated term [e'] has an erasure that steps to [r], then [e']
   runs, by steps that include [unfold (fold v) --> v], to a term whose
   erasure is [r] ([erase_converse]).

   An untyped converse is false: [unfold e] with [e] a variable erases to a
   term that steps no further than [e] does, and a stuck [unfold (num)] erases
   to a value.  Types supply what the proof needs from the elaborated side:
   a value that erases to a function is a function, not a [fold] around one
   (canonical forms), and an elaborated term whose erasure is a value reaches
   a value by erasure-invisible steps ([value_reach]). *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatPresence.
Require Import Goat.GoatMu.
Require Import Goat.GoatTags.
Require Import Goat.GoatMeta.
Require Import Goat.GoatConv.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatElab.
Require Import Stdlib.Lists.List.
From Stdlib Require Import Lia.
Import ListNotations.

(* ---- running inside a context ---- *)

Lemma multistep_trans : forall a b c, multistep a b -> multistep b c -> multistep a c.
Proof.
  intros a b c H. induction H; intros H2; [ exact H2 | eapply ms_step; [ eassumption | auto ] ].
Qed.

Lemma multistep_ctx : forall f, (forall a b, step a b -> step (f a) (f b)) ->
  forall a b, multistep a b -> multistep (f a) (f b).
Proof.
  intros f Hf a b H. induction H;
    [ apply ms_refl | eapply ms_step; [ apply Hf; eassumption | exact IHmultistep ] ].
Qed.

(* A record field runs while the fields before it are values. *)
Inductive msf : fields -> fields -> Prop :=
 | msf_refl : forall fs, msf fs fs
 | msf_step : forall fs1 fs2 fs3, step_fields fs1 fs2 -> msf fs2 fs3 -> msf fs1 fs3.

Lemma msf_rec : forall fs fs', msf fs fs' -> multistep (e_rec fs) (e_rec fs').
Proof.
  intros fs fs' H. induction H;
    [ apply ms_refl | eapply ms_step; [ apply st_rec; eassumption | exact IHmsf ] ].
Qed.

Lemma msf_trans : forall a b c, msf a b -> msf b c -> msf a c.
Proof.
  intros a b c H. induction H; intros H2; [ exact H2 | eapply msf_step; [ eassumption | auto ] ].
Qed.

Lemma msf_here : forall l e e' fs, multistep e e' -> msf (fs_cons l e fs) (fs_cons l e' fs).
Proof.
  intros l e e' fs H. induction H;
    [ apply msf_refl | eapply msf_step; [ apply stf_here; eassumption | exact IHmultistep ] ].
Qed.

Lemma msf_here_meth : forall l e e' fs, multistep e e' -> msf (fs_meth l e fs) (fs_meth l e' fs).
Proof.
  intros l e e' fs H. induction H;
    [ apply msf_refl | eapply msf_step; [ apply stf_meth_here; eassumption | exact IHmultistep ] ].
Qed.

Lemma msf_meth : forall l v fs fs', value v -> msf fs fs' -> msf (fs_meth l v fs) (fs_meth l v fs').
Proof.
  intros l v fs fs' Hv H. induction H;
    [ apply msf_refl | eapply msf_step; [ apply stf_meth_cons; eassumption | exact IHmsf ] ].
Qed.

Lemma msf_cons : forall l v fs fs', value v -> msf fs fs' -> msf (fs_cons l v fs) (fs_cons l v fs').
Proof.
  intros l v fs fs' Hv H. induction H;
    [ apply msf_refl | eapply msf_step; [ apply stf_cons; eassumption | exact IHmsf ] ].
Qed.

Lemma preservation_multi : forall D S e e' T,
  supp_ok D S -> typing D nil e T -> multistep e e' -> typing D nil e' T.
Proof.
  intros D S e e' T HS Hty H. induction H; [ exact Hty | ].
  apply IHmultistep. eapply preservation; eassumption.
Qed.

(* ---- operands of an operator ---- *)

Definition lit (x : exp) : Prop :=
  match x with
  | e_num _ | e_dec _ | e_true | e_false | e_str _ | e_unit => True
  | _ => False
  end.

Lemma erase_lit : forall x, lit x -> erase x = x.
Proof. intros x H. destruct x; try contradiction; reflexivity. Qed.


Lemma bin_sig_same : forall D o A B R, bin_sig D o A B R -> B = A.
Proof. intros D o A B R H. inversion H; reflexivity. Qed.

Lemma canon_lit : forall D G v A,
  value v -> typing D G v A ->
  (A = typ_Int \/ A = typ_Float \/ A = typ_String \/ A = typ_Bool \/ exists a, A = typ_Var a) ->
  lit v.
Proof.
  intros D G v A Hv Hty Hs.
  destruct Hs as [-> | [-> | [-> | [-> | [a ->]]]]].
  - destruct (canon_base _ _ _ _ Hv Hty) as [C _]. destruct (C (teq_refl _)) as [n ->]. exact I.
  - destruct (canon_base _ _ _ _ Hv Hty) as [_ [C _]].
    destruct (C (teq_refl _)) as [[n ->] | [d1 ->]]; exact I.
  - destruct (canon_base _ _ _ _ Hv Hty) as [_ [_ [C _]]]. destruct (C (teq_refl _)) as [q ->]. exact I.
  - destruct (canon_base _ _ _ _ Hv Hty) as [_ [_ [_ C]]]. destruct (C (teq_refl _)) as [-> | ->]; exact I.
  - destruct (canon_var _ _ _ _ _ Hv Hty (teq_refl _)) as [n ->]. exact I.
Qed.

(* An operand of a binary operator is a literal, or a record when the operator
   is a record's division. *)
Ltac base_type :=
  first [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
        | right; right; right; left; reflexivity
        | right; right; right; right; eexists; reflexivity ].

Lemma bin_operand : forall D G o A B R v,
  bin_sig D o A B R -> kind o <> k_cmp -> value v -> typing D G v A ->
  (exists gs, v = e_rec gs /\ rec_value gs) \/ lit v.
Proof.
  intros D G o A B R v Hs Hnk Hv Hty.
  assert (Hnum : forall A0, sat D k_Numeric A0 -> typing D G v A0 ->
            (exists gs, v = e_rec gs /\ rec_value gs) \/ lit v).
  { intros A0 Hsat Ht. destruct A0; simpl in Hsat; try discriminate Hsat;
      try (destruct Hsat as [Hsat | Hsat]; discriminate Hsat); try contradiction.
    - right. eapply canon_lit; [ eassumption | eassumption | base_type ].
    - right. eapply canon_lit; [ eassumption | eassumption | base_type ].
    - left. destruct (canon_record _ _ _ _ Hv Ht) as [gs [Rx [-> [Hrv _]]]]. eauto.
    - right. eapply canon_lit; [ eassumption | eassumption | base_type ]. }
  inversion Hs; subst.
  - eapply Hnum; eassumption.
  - right. eapply canon_lit; [ eassumption | eassumption | base_type ].
  - eapply Hnum; eassumption.
  - left. destruct (canon_record _ _ _ _ Hv Hty) as [gs [Rx [-> [Hrv _]]]]. eauto.
  - exfalso. congruence.
Qed.

(* ---- a comparison of erased values is a comparison of the values ---- *)

Lemma lookup_erase : forall l fs v,
  lookup_first l (erase_fields fs) = Some v ->
  exists w, lookup_first l fs = Some w /\ erase w = v.
Proof.
  intros l fs v H. rewrite erase_lookup_first in H.
  destruct (lookup_first l fs) as [w|]; cbn [option_map] in H; [ | discriminate H ].
  inversion H; subst. exists w. split; reflexivity.
Qed.

Lemma cr_fields_unerase : forall labs fs1' fs2' c, cr_fields labs fs1' fs2' c ->
  forall fs1 fs2, fs1' = erase_fields fs1 -> fs2' = erase_fields fs2 ->
  (forall l w1 w2, In l labs -> lookup_first l fs1 = Some w1 -> lookup_first l fs2 = Some w2 ->
     forall c', cmp_rel (erase w1) (erase w2) c' -> cmp_rel w1 w2 c') ->
  cr_fields labs fs1 fs2 c.
Proof.
  intros labs fs1' fs2' c H. induction H as [ fa fb | l ls fs1' fs2' v1 v2 c E1 E2 Hr Hf IH | l ls fs1' fs2' v1 v2 c E1 E2 Hr Hn ];
    intros fs1 fs2 -> -> Hall.
  - apply cf_nil.
  - destruct (lookup_erase _ _ _ E1) as [w1 [F1 <-]]. destruct (lookup_erase _ _ _ E2) as [w2 [F2 <-]].
    eapply cf_eq; [ exact F1 | exact F2 | | ].
    + eapply Hall; [ left; reflexivity | exact F1 | exact F2 | exact Hr ].
    + eapply IH; [ reflexivity | reflexivity | ].
      intros l' w1' w2' Hin. eapply Hall. right. exact Hin.
  - destruct (lookup_erase _ _ _ E1) as [w1 [F1 <-]]. destruct (lookup_erase _ _ _ E2) as [w2 [F2 <-]].
    eapply cf_ne; [ exact F1 | exact F2 | | exact Hn ].
    eapply Hall; [ left; reflexivity | exact F1 | exact F2 | exact Hr ].
Qed.

Lemma lit_unerase : forall v1 v2 c, lit v1 -> lit v2 ->
  cmp_rel (erase v1) (erase v2) c -> cmp_rel v1 v2 c.
Proof. intros v1 v2 c L1 L2 H. rewrite (erase_lit _ L1), (erase_lit _ L2) in H. exact H. Qed.

(* Comparing erased values is comparing the values: the induction is on the
   size of the first value, as for totality, because a tag group's recursive
   slot and a [mu] body do not shrink the type. *)
Lemma cmp_unerase_size : forall n D G T v1 v2,
  vsize v1 < n -> sat D k_Eq T -> value v1 -> value v2 ->
  typing D G v1 T -> typing D G v2 T ->
  forall c, cmp_rel (erase v1) (erase v2) c -> cmp_rel v1 v2 c.
Proof.
  induction n as [ | n IH ]; intros D G T v1 v2 Hn; [ lia | ].
  intros Hs Hv1 Hv2 H1 H2 c Hc.
  destruct T as [ | | | | | T1 T2 | R | a | i | B | w A ].
  - refine (lit_unerase _ _ _ _ _ Hc); (eapply canon_lit; [ eassumption | eassumption | base_type ]).
  - refine (lit_unerase _ _ _ _ _ Hc); (eapply canon_lit; [ eassumption | eassumption | base_type ]).
  - refine (lit_unerase _ _ _ _ _ Hc); (eapply canon_lit; [ eassumption | eassumption | base_type ]).
  - pose proof (canon_unit _ _ _ _ Hv1 H1 (teq_refl _)) as E1.
    pose proof (canon_unit _ _ _ _ Hv2 H2 (teq_refl _)) as E2. subst v1 v2.
    refine (lit_unerase _ _ _ _ _ Hc); exact I.
  - refine (lit_unerase _ _ _ _ _ Hc); (eapply canon_lit; [ eassumption | eassumption | base_type ]).
  - discriminate Hs.
  - (* Record *)
    destruct (canon_record _ _ _ _ Hv1 H1) as [fs1 [Rf1 [-> [Hr1 [Hf1 Hq1]]]]].
    destruct (canon_record _ _ _ _ Hv2 H2) as [fs2 [Rf2 [-> [Hr2 [Hf2 Hq2]]]]].
    cbn [erase] in Hc. apply cmp_rel_rec_inv in Hc. rewrite erase_rec_labels in Hc.
    apply cr_rec.
    eapply cr_fields_unerase; [ exact Hc | reflexivity | reflexivity | ].
    intros l w1 w2 Hl E1 E2 c' Hc'.
    pose proof (lookup_first_vsize _ _ _ E1) as Hsz. simpl in Hn.
    destruct (rec_align _ _ _ _ _ _ _ Hr1 Hr2 Hf1 Hf2 Hq1 Hq2 l Hl)
      as [T' [R'' [w1' [w2' [Hrm [E1' [E2' [Hw1 [Hw2 [Ht1 Ht2]]]]]]]]]].
    rewrite E1 in E1'. rewrite E2 in E2'. inversion E1'; inversion E2'; subst.
    assert (Hs' : rsat D k_Eq (nfR D R)) by (apply rsat_nf; exact Hs).
    destruct (rm_sat D k_Eq _ _ _ _ Hrm Hs') as [Hst _].
    refine (IH D G T' _ _ _ Hst Hw1 Hw2 Ht1 Ht2 c' Hc'). lia.
  - refine (lit_unerase _ _ _ _ _ Hc); (eapply canon_lit; [ eassumption | eassumption | base_type ]).
  - exfalso. exact (canon_bvar _ _ _ _ Hv1 H1 eq_refl).
  - (* Mu *)
    destruct (canon_mu _ _ _ _ _ Hv1 H1 (teq_refl _)) as [u1 [-> [Hu1 Hy1]]].
    destruct (canon_mu _ _ _ _ _ Hv2 H2 (teq_refl _)) as [u2 [-> [Hu2 Hy2]]].
    cbn [erase] in Hc. simpl in Hn.
    apply cr_fold.
    exact (IH D G _ u1 u2 ltac:(lia) (sat_eq_unroll _ _ Hs) Hu1 Hu2 Hy1 Hy2 c Hc).
  - (* Grp *)
    destruct (canon_grp _ _ _ _ _ Hv1 H1) as [tg1 [u1 [Ts1 [-> [Hu1 [Hl1 [Hq1 Hy1]]]]]]].
    destruct (canon_grp _ _ _ _ _ Hv2 H2) as [tg2 [u2 [Ts2 [-> [Hu2 [Hl2 [Hq2 Hy2]]]]]]].
    destruct (teq_spine_exists _ _ Hq1) as [As [-> Hf1]].
    destruct (teq_spine_exists _ _ Hq2) as [As2 [Es Hf2]].
    apply spine_inj in Es. subst As2.
    assert (Hg : sat D k_Eq (typ_Grp w (spine As))) by exact Hs.
    cbn [erase] in Hc. simpl in Hn.
    destruct (cmp_rel_con_inv _ _ _ _ _ _ Hc) as [[Heq Hc'] | [[Hlt ->] | [Hgt ->]]];
      [ | apply cr_con_lt; exact Hlt | apply cr_con_gt; exact Hgt ].
    subst tg1. apply cr_con_eq.
    assert (Hy1' : typing D G u1 (tag_payload w As tg2))
      by (eapply T_Conv; [ exact Hy1 | apply teq_sym; apply teq_tag_payload; exact Hf1 ]).
    assert (Hy2' : typing D G u2 (tag_payload w As tg2))
      by (eapply T_Conv; [ exact Hy2 | apply teq_sym; apply teq_tag_payload; exact Hf2 ]).
    exact (IH D G _ u1 u2 ltac:(lia) (sat_tag_payload _ _ _ _ Hg Hl2) Hu1 Hu2 Hy1' Hy2' _ Hc').
Qed.

Lemma cmp_unerase : forall D G A v1 v2,
  sat D k_Eq A -> value v1 -> value v2 -> typing D G v1 A -> typing D G v2 A ->
  forall c, cmp_rel (erase v1) (erase v2) c -> cmp_rel v1 v2 c.
Proof.
  intros D G A v1 v2 Hs Hv1 Hv2 H1 H2 c.
  exact (cmp_unerase_size (S (vsize v1)) D G A v1 v2 (Nat.lt_succ_diag_r _) Hs Hv1 Hv2 H1 H2 c).
Qed.

Lemma cmp_holds_any : forall o b, kind o = k_cmp -> exists c, cmp_holds o c = b.
Proof.
  intros o b H. destruct o; try (simpl in H; discriminate H);
    destruct b; first [ (exists Lt; reflexivity) | (exists Eq; reflexivity) | (exists Gt; reflexivity) ].
Qed.

(* A step of two erased operands is a comparison, whatever the operands, or an
   arithmetic step on literals. *)
Lemma bin_step_cmp_or_lit : forall o a b v, bin_step o a b v ->
  (exists c, kind o = k_cmp /\ cmp_rel a b c /\ v = of_bool (cmp_holds o c)) \/
  (kind o <> k_cmp /\ lit a /\ lit b).
Proof.
  intros o a b v H. inversion H; subst.
  - right. refine (conj _ (conj I I)); intros Hk; congruence.
  - right. refine (conj _ (conj I I)); intros Hk; congruence.
  - match goal with Hp : fl_pair _ _ |- _ =>
      inversion Hp; subst; right; refine (conj _ (conj I I));
      intros Hk; match goal with Hd : _ \/ _ |- _ => destruct Hd end; congruence end.
  - match goal with Hp : fl_pair _ _ |- _ =>
      inversion Hp; subst; right; refine (conj _ (conj I I)); intros Hk; congruence end.
  - right. refine (conj _ (conj I I)); intros Hk; congruence.
  - match goal with Hk : kind ?o' = k_cmp, Hp : fl_pair ?x ?y, Hb : bin_step _ _ _ (of_bool ?bb) |- _ =>
      left; destruct (cmp_holds_any o' bb Hk) as [c' Hc']; exists c'; repeat split;
      [ exact Hk | apply cr_float; exact Hp | now rewrite Hc' ] end.
  - left. eexists. refine (conj _ (conj _ eq_refl)); eassumption.
Qed.

Lemma bin_step_lit_result : forall o a b v, bin_step o a b v -> lit v.
Proof.
  intros o a b v H. inversion H; subst;
    first [ exact I | (unfold of_bool; destruct (cmp_holds o _); exact I)
          | (unfold of_bool; destruct c; exact I) ].
Qed.

Lemma bin_sig_cmp_sat : forall D o A B R,
  bin_sig D o A B R -> kind o = k_cmp -> sat D k_Eq A.
Proof.
  intros D o A B R H Hk. inversion H; subst; try assumption; exfalso;
    first [ congruence | (simpl in Hk; discriminate Hk) ].
Qed.

(* ---- a term whose erasure is a value reaches a value ---- *)

Lemma value_reach_mut :
  (forall D G e T, typing D G e T -> forall S, supp_ok D S -> G = nil ->
     value (erase e) -> exists v, multistep e v /\ value v /\ erase v = erase e) /\
  (forall D G fs R, field_typing D G fs R -> forall S, supp_ok D S -> G = nil ->
     rec_value (erase_fields fs) ->
     exists fs', msf fs fs' /\ rec_value fs' /\ erase_fields fs' = erase_fields fs).
Proof.
  apply typing_field_mutind.
  - intros D G x s T Hu Hb Hi S HS HG Hv. subst. inversion Hb.
  - intros D G n T Hu Hs S HS HG Hv. exists (e_num n). auto using ms_refl.
  - intros D G d Hu S HS HG Hv. exists (e_dec d). auto using ms_refl.
  - intros D G Hu S HS HG Hv. exists e_true. auto using ms_refl.
  - intros D G Hu S HS HG Hv. exists e_false. auto using ms_refl.
  - intros L D G e T1 T2 Hb IH S HS HG Hv. exists (e_abs e). auto using ms_refl.
  - intros D G e1 e2 T1 T2 H1 IH1 H2 IH2 S HS HG Hv. cbn [erase] in Hv. inversion Hv.
  - intros L D G e1 e2 T1 T2 kf rkf Tm Hgv Hlp H1 IH1 Hb IH2 S HS HG Hv. cbn [erase] in Hv. inversion Hv.
  - intros L D G e1 e2 T1 T2 H1 IH1 Hb IH2 S HS HG Hv. cbn [erase] in Hv. inversion Hv.
  - intros L D G fs e2 R T kf rkf Hfg Hfs IHfs Hb IH2 S HS HG Hv. cbn [erase] in Hv. inversion Hv.
  - intros D G fs R Hft IH Hnm S HS HG Hv. cbn [erase] in Hv. inversion Hv; subst.
    destruct (IH S HS eq_refl H0) as [fs' [Hms [Hrv Her]]].
    exists (e_rec fs'). repeat split.
    + apply msf_rec. exact Hms.
    + apply v_rec. exact Hrv.
    + cbn [erase]. rewrite Her. reflexivity.
  - intros D G fs R Rt Hft IH Hms0 S HS HG Hv. cbn [erase] in Hv. inversion Hv; subst.
    destruct (IH S HS eq_refl H0) as [fs' [Hms [Hrv Her]]].
    exists (e_rec fs'). repeat split.
    + apply msf_rec. exact Hms.
    + apply v_rec. exact Hrv.
    + cbn [erase]. rewrite Her. reflexivity.
  - intros D G e l T R Hty IH S HS HG Hv. cbn [erase] in Hv. inversion Hv.
  - intros D G e T T' Hty IH Hteq S HS HG Hv. exact (IH S HS HG Hv).
  - intros D G Hu S HS HG Hv. exists e_unit. auto using ms_refl.
  - intros D G q Hu S HS HG Hv. exists (e_str q). auto using ms_refl.
  - intros D G e1 e2 e3 T H1 IH1 H2 IH2 H3 IH3 S HS HG Hv. cbn [erase] in Hv. inversion Hv.
  - intros D G e A Ht IH Hsat S HS HG Hv. cbn [erase] in Hv. inversion Hv.
  - intros D G e1 o e2 A B R H1 IH1 H2 IH2 Hs S HS HG Hv. cbn [erase] in Hv. inversion Hv.
  - intros D G e1 l e2 P T R H1 IH1 H2 IH2 S HS HG Hv. cbn [erase] in Hv. inversion Hv.
  - intros D G e1 l e2 T R H1 IH1 Hl H2 IH2 S HS HG Hv. cbn [erase] in Hv. inversion Hv.
  - intros D G e l R0 T R Ht IH Hrm S HS HG Hv. cbn [erase] in Hv. inversion Hv.
  - (* fold *) intros D G e B Hlc Hg Ht IH S HS HG Hv. cbn [erase] in Hv.
    destruct (IH S HS HG Hv) as [v [Hms [Hvv Her]]].
    exists (e_fold v). repeat split.
    + apply (multistep_ctx e_fold st_fold1). exact Hms.
    + apply v_fold. exact Hvv.
    + cbn [erase]. exact Her.
  - (* unfold *) intros D G e B Hlc Hg Ht IH S HS HG Hv. cbn [erase] in Hv. subst G.
    destruct (IH S HS eq_refl Hv) as [v [Hms [Hvv Her]]].
    destruct (canon_mu D nil v B (typ_Mu B) Hvv
                (preservation_multi _ _ _ _ _ HS Ht Hms) (teq_refl _)) as [v' [-> [Hv' _]]].
    exists v'. repeat split; [ | exact Hv' | ].
    + eapply multistep_trans; [ apply (multistep_ctx e_unfold st_unfold1); exact Hms | ].
      eapply ms_step; [ apply st_unfold_fold; exact Hv' | apply ms_refl ].
    + cbn [erase]. cbn [erase] in Her. exact Her.
  - (* con *) intros D G w tg e Ts Hlt Ht IH S HS HG Hv. cbn [erase] in Hv. inversion Hv; subst.
    destruct (IH S HS eq_refl H0) as [v [Hms [Hvv Her]]].
    exists (e_con w tg v). repeat split.
    + apply (multistep_ctx (e_con w tg) (st_con1 w tg)). exact Hms.
    + apply v_con. exact Hvv.
    + cbn [erase]. rewrite Her. reflexivity.
  - intros L D G w Ts e ars T Ht IHe Hwf Harm IHarm Hdef IHdef S HS HG Hv.
    cbn [erase] in Hv. inversion Hv.
  - intros D G Hu S HS HG Hv. exists fs_nil. auto using msf_refl.
  - intros D G l e T fs R Hty IH1 Hft IH2 S HS HG Hv. cbn [erase_fields] in Hv. inversion Hv as [ | l0 v0 fs0 Hv0 Hrv0 | l0 v0 fs0 Hv0 Hrv0 ]; subst.
    destruct (IH1 S HS eq_refl Hv0) as [v [Hms [Hvv Her]]].
    destruct (IH2 S HS eq_refl Hrv0) as [fs' [Hmf [Hrv Hef]]].
    exists (fs_cons l v fs'). repeat split.
    + eapply msf_trans; [ apply msf_here; exact Hms | apply msf_cons; assumption ].
    + constructor; assumption.
    + cbn [erase_fields]. rewrite Her, Hef. reflexivity.
  - intros D G l e T fs R Hty IH1 Hft IH2 S HS HG Hv. cbn [erase_fields] in Hv. inversion Hv as [ | l0 v0 fs0 Hv0 Hrv0 | l0 v0 fs0 Hv0 Hrv0 ]; subst.
    destruct (IH1 S HS eq_refl Hv0) as [v [Hms [Hvv Her]]].
    destruct (IH2 S HS eq_refl Hrv0) as [fs' [Hmf [Hrv Hef]]].
    exists (fs_meth l v fs'). repeat split.
    + eapply msf_trans; [ apply msf_here_meth; exact Hms | apply msf_meth; assumption ].
    + constructor; assumption.
    + cbn [erase_fields]. rewrite Her, Hef. reflexivity.
Qed.

Theorem value_reach : forall D S e T,
  supp_ok D S -> typing D nil e T -> value (erase e) ->
  exists v, multistep e v /\ value v /\ erase v = erase e.
Proof. intros D S e T HS Ht Hv. exact (proj1 value_reach_mut D nil e T Ht S HS eq_refl Hv). Qed.

(* ---- the steps of an erased term ---- *)

Lemma ms_app1 : forall e1 e1' e2, multistep e1 e1' -> multistep (e_app e1 e2) (e_app e1' e2).
Proof. intros. apply (multistep_ctx (fun x => e_app x e2)); [ intros; apply st_app1; assumption | assumption ]. Qed.

Lemma ms_app2 : forall v e2 e2', value v -> multistep e2 e2' -> multistep (e_app v e2) (e_app v e2').
Proof. intros. apply (multistep_ctx (fun x => e_app v x)); [ intros; apply st_app2; assumption | assumption ]. Qed.

Lemma ms_let1 : forall e1 e1' e2, multistep e1 e1' -> multistep (e_let e1 e2) (e_let e1' e2).
Proof. intros. apply (multistep_ctx (fun x => e_let x e2)); [ intros; apply st_let1; assumption | assumption ]. Qed.

Lemma ms_proj : forall e e' l, multistep e e' -> multistep (e_proj e l) (e_proj e' l).
Proof. intros. apply (multistep_ctx (fun x => e_proj x l)); [ intros; apply st_proj; assumption | assumption ]. Qed.

Lemma ms_ite1 : forall e1 e1' e2 e3, multistep e1 e1' -> multistep (e_ite e1 e2 e3) (e_ite e1' e2 e3).
Proof. intros. apply (multistep_ctx (fun x => e_ite x e2 e3)); [ intros; apply st_ite1; assumption | assumption ]. Qed.

Lemma ms_bin1 : forall e1 e1' o e2, multistep e1 e1' -> multistep (e_bin e1 o e2) (e_bin e1' o e2).
Proof. intros. apply (multistep_ctx (fun x => e_bin x o e2)); [ intros; apply st_bin1; assumption | assumption ]. Qed.

Lemma ms_bin2 : forall v o e2 e2', value v -> multistep e2 e2' -> multistep (e_bin v o e2) (e_bin v o e2').
Proof. intros. apply (multistep_ctx (fun x => e_bin v o x)); [ intros; apply st_bin2; assumption | assumption ]. Qed.

Lemma ms_tofloat : forall e e', multistep e e' -> multistep (e_tofloat e) (e_tofloat e').
Proof. intros. apply (multistep_ctx e_tofloat); [ intros; apply st_tofloat1; assumption | assumption ]. Qed.

Lemma ms_spread1 : forall e1 e1' l e2, multistep e1 e1' -> multistep (e_spread e1 l e2) (e_spread e1' l e2).
Proof. intros. apply (multistep_ctx (fun x => e_spread x l e2)); [ intros; apply st_spread1; assumption | assumption ]. Qed.

Lemma ms_spread2 : forall v l e2 e2', value v -> multistep e2 e2' -> multistep (e_spread v l e2) (e_spread v l e2').
Proof. intros. apply (multistep_ctx (fun x => e_spread v l x)); [ intros; apply st_spread2; assumption | assumption ]. Qed.

Lemma ms_restrict : forall e e' l, multistep e e' -> multistep (e_restrict e l) (e_restrict e' l).
Proof. intros. apply (multistep_ctx (fun x => e_restrict x l)); [ intros; apply st_restrict1; assumption | assumption ]. Qed.

Lemma ms_fold : forall e e', multistep e e' -> multistep (e_fold e) (e_fold e').
Proof. intros. apply (multistep_ctx e_fold); [ intros; apply st_fold1; assumption | assumption ]. Qed.

Lemma ms_unfold : forall e e', multistep e e' -> multistep (e_unfold e) (e_unfold e').
Proof. intros. apply (multistep_ctx e_unfold); [ intros; apply st_unfold1; assumption | assumption ]. Qed.

Lemma ms_con : forall w tg e e', multistep e e' -> multistep (e_con w tg e) (e_con w tg e').
Proof. intros. apply (multistep_ctx (e_con w tg)); [ intros; apply st_con1; assumption | assumption ]. Qed.

Lemma ms_match : forall w e e' ars, multistep e e' -> multistep (e_match w e ars) (e_match w e' ars).
Proof. intros. apply (multistep_ctx (fun x => e_match w x ars)); [ intros; apply st_match1; assumption | assumption ]. Qed.

(* ---- a term whose erasure has a known shape reaches that shape ---- *)

Lemma reach_abs : forall D S e T1 T2 e0, supp_ok D S ->
  typing D nil e (typ_Arrow T1 T2) -> erase e = e_abs e0 ->
  exists b, multistep e (e_abs b) /\ erase b = e0.
Proof.
  intros D S e T1 T2 e0 HS Ht He.
  destruct (value_reach D S e _ HS Ht (ltac:(rewrite He; apply v_abs))) as [v [Hm [Hv Hev]]].
  destruct (canon_arrow _ _ _ _ _ Hv (preservation_multi _ _ _ _ _ HS Ht Hm)) as [b ->].
  exists b. split; [ exact Hm | ]. rewrite He in Hev. cbn [erase] in Hev. congruence.
Qed.

Lemma reach_rec : forall D S e R fs0, supp_ok D S ->
  typing D nil e (typ_Record R) -> erase e = e_rec fs0 -> rec_value fs0 ->
  exists gs, multistep e (e_rec gs) /\ rec_value gs /\ erase_fields gs = fs0.
Proof.
  intros D S e R fs0 HS Ht He Hrv.
  destruct (value_reach D S e _ HS Ht (ltac:(rewrite He; apply v_rec; exact Hrv))) as [v [Hm [Hv Hev]]].
  destruct (canon_record _ _ _ _ Hv (preservation_multi _ _ _ _ _ HS Ht Hm))
    as [gs [R0 [-> [Hrg _]]]].
  exists gs. repeat split; [ exact Hm | exact Hrg | ]. rewrite He in Hev. cbn [erase] in Hev. congruence.
Qed.

Lemma reach_con : forall D S e w Ts w' tg v, supp_ok D S ->
  typing D nil e (typ_Grp w (spine Ts)) -> erase e = e_con w' tg v -> value v ->
  exists v1, multistep e (e_con w' tg v1) /\ value v1 /\ erase v1 = v.
Proof.
  intros D S e w Ts w' tg v HS Ht He Hv0.
  destruct (value_reach D S e _ HS Ht (ltac:(rewrite He; apply v_con; exact Hv0))) as [v1 [Hm [Hv Hev]]].
  destruct (canon_grp_spine _ _ _ _ _ Hv (preservation_multi _ _ _ _ _ HS Ht Hm))
    as [tg1 [v1' [-> [Hv1' _]]]].
  rewrite He in Hev. cbn [erase] in Hev. injection Hev as <- <- Ev.
  exists v1'. repeat split; assumption.
Qed.

Lemma reach_lit : forall D S e T x, supp_ok D S -> typing D nil e T -> lit x -> erase e = x ->
  (forall v, value v -> typing D nil v T -> lit v) -> multistep e x.
Proof.
  intros D S e T x HS Ht Hl He Hc.
  destruct (value_reach D S e _ HS Ht (ltac:(rewrite He; destruct x; try contradiction; constructor)))
    as [v [Hm [Hv Hev]]].
  assert (Hlv : lit v) by (apply Hc; [ exact Hv | eapply preservation_multi; eassumption ]).
  rewrite (erase_lit _ Hlv), He in Hev. rewrite <- Hev. exact Hm.
Qed.

Lemma reach_operand : forall D S e o A B R, supp_ok D S ->
  bin_sig D o A B R -> kind o <> k_cmp -> typing D nil e A -> value (erase e) ->
  exists v, multistep e v /\ erase v = erase e /\
    ((exists gs, v = e_rec gs /\ rec_value gs) \/ lit v).
Proof.
  intros D S e o A B R HS Hs Hnk Ht Hv.
  destruct (value_reach D S e _ HS Ht Hv) as [v [Hm [Hvv Hev]]].
  exists v. repeat split; [ exact Hm | exact Hev | ].
  eapply bin_operand; [ exact Hs | exact Hnk | exact Hvv | eapply preservation_multi; eassumption ].
Qed.

Lemma rec_zip_unerase : forall o fs1' fs2' fs, rec_zip o fs1' fs2' fs ->
  forall gs1 gs2, fs_plain (erase_fields gs1) = fs1' -> fs_plain (erase_fields gs2) = fs2' ->
  exists gs, rec_zip o (fs_plain gs1) (fs_plain gs2) gs /\ erase_fields gs = fs.
Proof.
  intros o fs1' fs2' fs H. induction H; intros gs1 gs2 E1 E2.
  - destruct gs1; cbn [erase_fields fs_plain] in E1; try discriminate.
    exists fs_nil. split; [ constructor | reflexivity ].
  - assert (Hg1 : exists w1 g1, fs_plain gs1 = fs_cons l w1 (fs_plain g1) /\
                    erase w1 = v1 /\ fs_plain (erase_fields g1) = r1).
    { destruct gs1 as [ | l1 w1 g1 | l1 w1 g1]; cbn [erase_fields fs_plain] in E1; try discriminate;
        injection E1 as El Ew Eg; subst l1; exists w1, g1; repeat split; auto. }
    destruct Hg1 as [w1 [g1 [Hp [Ew Eg]]]].
    rewrite <- E2, lookup_first_plain, erase_lookup_first in H.
    destruct (lookup_first l gs2) as [w2 | ] eqn:Hl; cbn [option_map] in H; try discriminate.
    injection H as Ew2.
    destruct (IHrec_zip g1 (fs_drop l gs2)) as [gs [Hz Hg]].
    + exact Eg.
    + rewrite erase_fs_drop, fs_plain_drop, E2. reflexivity.
    + exists (fs_cons l (e_bin w1 o w2) gs). split.
      * rewrite Hp. eapply rz_cons; [ rewrite lookup_first_plain; exact Hl | rewrite <- fs_plain_drop; exact Hz ].
      * cbn [erase_fields erase]. rewrite Hg, Ew, Ew2. reflexivity.
Qed.

Lemma let_converse : forall e1 e2 r,
  (value (erase e1) -> exists v, multistep e1 v /\ value v /\ erase v = erase e1) ->
  (forall r1, step (erase e1) r1 -> exists e'', multistep e1 e'' /\ erase e'' = r1) ->
  step (erase (e_let e1 e2)) r -> exists e'', multistep (e_let e1 e2) e'' /\ erase e'' = r.
Proof.
  intros e1 e2 r Hv Hs H. cbn [erase] in H. inversion H; subst.
  - assert (Hx : value (erase e1)) by assumption. destruct (Hv Hx) as [v1 [Hm [Hvv Hev]]].
    exists (open_exp_wrt_exp e2 v1). split.
    + eapply multistep_trans; [ apply ms_let1; exact Hm | ].
      eapply ms_step; [ apply st_letv; exact Hvv | apply ms_refl ].
    + rewrite erase_open, Hev. reflexivity.
  - match goal with Hx : step (erase e1) _ |- _ => destruct (Hs _ Hx) as [e'' [Hm Hr]] end.
    exists (e_let e'' e2). split; [ apply ms_let1; exact Hm | cbn [erase]; rewrite Hr; reflexivity ].
Qed.

Lemma lit_value : forall x, lit x -> value x.
Proof. intros x H. destruct x; try contradiction; constructor. Qed.

(* A term that erases to a literal and is a value is that literal; the
   operand of a binary operator is one. *)
Lemma operand_lit : forall v x,
  ((exists gs, v = e_rec gs /\ rec_value gs) \/ lit v) -> erase v = x -> lit x -> v = x.
Proof.
  intros v x [[gs [-> _]] | Lv] Hev Lx.
  - rewrite <- Hev in Lx. cbn [erase] in Lx. contradiction.
  - rewrite <- Hev. symmetry. apply erase_lit. exact Lv.
Qed.

(* [inversion] states the shape equation of an erased subterm backwards. *)
Ltac flip_erased :=
  repeat match goal with
         | H : ?x = erase ?e |- _ =>
             lazymatch x with erase _ => fail | _ => symmetry in H end
         end.

Lemma erase_converse_mut :
  (forall D G e T, typing D G e T -> forall S, supp_ok D S -> G = nil ->
     forall r, step (erase e) r -> exists e'', multistep e e'' /\ erase e'' = r) /\
  (forall D G fs R, field_typing D G fs R -> forall S, supp_ok D S -> G = nil ->
     forall fs'', step_fields (erase_fields fs) fs'' ->
     exists fs', msf fs fs' /\ erase_fields fs' = fs'').
Proof.
  apply typing_field_mutind.
  - intros D G x s T Hu Hb Hi S HS HG r Hs. subst. inversion Hb.
  - intros D G n T Hu Hs0 S HS HG r Hs. cbn [erase] in Hs. inversion Hs.
  - intros D G d Hu S HS HG r Hs. cbn [erase] in Hs. inversion Hs.
  - intros D G Hu S HS HG r Hs. cbn [erase] in Hs. inversion Hs.
  - intros D G Hu S HS HG r Hs. cbn [erase] in Hs. inversion Hs.
  - intros L D G e T1 T2 Hb IH S HS HG r Hs. cbn [erase] in Hs. inversion Hs.
  - (* app *) intros D G e1 e2 T1 T2 H1 IH1 H2 IH2 S HS HG r Hs. subst G.
    cbn [erase] in Hs. inversion Hs; subst; flip_erased.
    + lazymatch goal with Ha : erase e1 = e_abs ?b0 |- _ =>
        destruct (reach_abs D S e1 T1 T2 b0 HS H1 Ha) as [b [Hm1 Heb]] end.
      assert (Hv2 : value (erase e2)) by assumption.
      destruct (value_reach D S e2 T1 HS H2 Hv2) as [v2 [Hm2 [Hvv2 He2]]].
      exists (open_exp_wrt_exp b v2). split.
      * eapply multistep_trans; [ apply ms_app1; exact Hm1 | ].
        eapply multistep_trans; [ apply ms_app2; [ constructor | exact Hm2 ] | ].
        eapply ms_step; [ apply st_beta; exact Hvv2 | apply ms_refl ].
      * rewrite erase_open, Heb, He2. reflexivity.
    + lazymatch goal with Hx : step (erase e1) _ |- _ =>
        destruct (IH1 S HS eq_refl _ Hx) as [e1'' [Hm He]] end.
      exists (e_app e1'' e2). split; [ apply ms_app1; exact Hm | cbn [erase]; rewrite He; reflexivity ].
    + assert (Hv1 : value (erase e1)) by assumption.
      destruct (value_reach D S e1 _ HS H1 Hv1) as [v1 [Hm1 [Hvv1 He1]]].
      lazymatch goal with Hx : step (erase e2) _ |- _ =>
        destruct (IH2 S HS eq_refl _ Hx) as [e2'' [Hm2 He2]] end.
      exists (e_app v1 e2''). split.
      * eapply multistep_trans; [ apply ms_app1; exact Hm1 | apply ms_app2; assumption ].
      * cbn [erase]. rewrite He1, He2. reflexivity.
  - (* let *) intros L D G e1 e2 T1 T2 kf rkf Tm Hgv Hlp H1 IH1 Hb IH2 S HS HG r Hs. subst G.
    eapply let_converse; [ | | exact Hs ].
    + intros Hv. exact (value_reach _ _ e1 _ (supp_ok_ext2 _ _ _ _ _ _ HS) H1 Hv).
    + intros r1 Hx. exact (IH1 _ (supp_ok_ext2 _ _ _ _ _ _ HS) eq_refl _ Hx).
  - (* letmono *) intros L D G e1 e2 T1 T2 H1 IH1 Hb IH2 S HS HG r Hs. subst G.
    eapply let_converse; [ | | exact Hs ].
    + intros Hv. exact (value_reach D S e1 _ HS H1 Hv).
    + intros r1 Hx. exact (IH1 S HS eq_refl _ Hx).
  - (* letrec *) intros L D G fs e2 R T kf rkf Hfg Hfs IHfs Hb IH2 S HS HG r Hs. subst G.
    cbn [erase] in Hs. inversion Hs; subst; flip_erased.
    exists (open_exp_wrt_exp e2 (e_rec (open_fields_wrt_exp fs (e_letrec fs (e_fvar_b 0))))). split.
    + eapply ms_step; [ apply st_letrec; exact Hfg | apply ms_refl ].
    + rewrite erase_open. cbn [erase erase_fields]. rewrite erase_open_fields.
      cbn [erase erase_fields]. reflexivity.
  - (* record *) intros D G fs R Hft IH Hnm S HS HG r Hs. subst G. cbn [erase] in Hs. inversion Hs; subst; flip_erased.
    lazymatch goal with Hx : step_fields (erase_fields fs) _ |- _ =>
      destruct (IH S HS eq_refl _ Hx) as [fsx [Hm He]] end.
    exists (e_rec fsx). split; [ apply msf_rec; exact Hm | cbn [erase]; rewrite He; reflexivity ].
  - (* record with methods *) intros D G fs R Rt Hft IH Hms0 S HS HG r Hs. subst G. cbn [erase] in Hs. inversion Hs; subst; flip_erased.
    lazymatch goal with Hx : step_fields (erase_fields fs) _ |- _ =>
      destruct (IH S HS eq_refl _ Hx) as [fsx [Hm He]] end.
    exists (e_rec fsx). split; [ apply msf_rec; exact Hm | cbn [erase]; rewrite He; reflexivity ].
  - (* proj *) intros D G e l T R Hty IH S HS HG r Hs. subst G. cbn [erase] in Hs. inversion Hs; subst; flip_erased.
    + lazymatch goal with Hx : step (erase e) _ |- _ =>
        destruct (IH S HS eq_refl _ Hx) as [e'' [Hm He]] end.
      exists (e_proj e'' l). split; [ apply ms_proj; exact Hm | cbn [erase]; rewrite He; reflexivity ].
    + lazymatch goal with Ha : erase e = e_rec ?fs0, Hrv : rec_value ?fs0 |- _ =>
        destruct (reach_rec D S e _ fs0 HS Hty Ha Hrv) as [gs [Hm [Hrg Heg]]] end.
      lazymatch goal with Hl : lookup_first l _ = Some r |- _ =>
        rewrite <- Heg, erase_lookup_first in Hl;
        destruct (lookup_first l gs) as [w | ] eqn:Hlw; cbn [option_map] in Hl; try discriminate;
        injection Hl as Hwr end.
      exists w. split.
      * eapply multistep_trans; [ apply ms_proj; exact Hm | ].
        eapply ms_step; [ apply st_projrec; eassumption | apply ms_refl ].
      * exact Hwr.
  - (* conv *) intros D G e T T' Hty IH Hteq S HS HG r Hs. exact (IH S HS HG r Hs).
  - intros D G Hu S HS HG r Hs. cbn [erase] in Hs. inversion Hs.
  - intros D G q Hu S HS HG r Hs. cbn [erase] in Hs. inversion Hs.
  - (* if *) intros D G e1 e2 e3 T H1 IH1 H2 IH2 H3 IH3 S HS HG r Hs. subst G.
    cbn [erase] in Hs. inversion Hs; subst; flip_erased.
    + lazymatch goal with Hx : step (erase e1) _ |- _ =>
        destruct (IH1 S HS eq_refl _ Hx) as [e1'' [Hm He]] end.
      exists (e_ite e1'' e2 e3). split; [ apply ms_ite1; exact Hm | cbn [erase]; rewrite He; reflexivity ].
    + lazymatch goal with Ha : erase e1 = e_true |- _ =>
        pose proof (reach_lit D S e1 typ_Bool e_true HS H1 I Ha
          (fun v Hv Ht => canon_lit D nil v typ_Bool Hv Ht ltac:(base_type))) as Hm end.
      exists e2. split; [ | reflexivity ].
      eapply multistep_trans; [ apply ms_ite1; exact Hm | ].
      eapply ms_step; [ apply st_ite_true | apply ms_refl ].
    + lazymatch goal with Ha : erase e1 = e_false |- _ =>
        pose proof (reach_lit D S e1 typ_Bool e_false HS H1 I Ha
          (fun v Hv Ht => canon_lit D nil v typ_Bool Hv Ht ltac:(base_type))) as Hm end.
      exists e3. split; [ | reflexivity ].
      eapply multistep_trans; [ apply ms_ite1; exact Hm | ].
      eapply ms_step; [ apply st_ite_false | apply ms_refl ].
  - (* tofloat *) intros D G e A Ht IH Hsat S HS HG r Hs. subst G. cbn [erase] in Hs. inversion Hs; subst; flip_erased.
    + lazymatch goal with Hx : step (erase e) _ |- _ =>
        destruct (IH S HS eq_refl _ Hx) as [e'' [Hm He]] end.
      exists (e_tofloat e''). split; [ apply ms_tofloat; exact Hm | cbn [erase]; rewrite He; reflexivity ].
    + lazymatch goal with Ha : erase e = e_num ?z |- _ =>
        pose proof (reach_lit D S e A (e_num z) HS Ht I Ha
          (fun v Hv Hty => ltac:(destruct (canon_numeric D nil v A Hv Hty Hsat) as [[n ->] | [d1 ->]]; exact I))) as Hm end.
      eexists (e_dec _). split; [ | reflexivity ].
      eapply multistep_trans; [ apply ms_tofloat; exact Hm | ].
      eapply ms_step; [ apply st_tofloat | apply ms_refl ].
    + lazymatch goal with Ha : erase e = e_dec ?d |- _ =>
        pose proof (reach_lit D S e A (e_dec d) HS Ht I Ha
          (fun v Hv Hty => ltac:(destruct (canon_numeric D nil v A Hv Hty Hsat) as [[n ->] | [d1 ->]]; exact I))) as Hm end.
      eexists (e_dec _). split; [ | reflexivity ].
      eapply multistep_trans; [ apply ms_tofloat; exact Hm | ].
      eapply ms_step; [ apply st_tofloat_dec | apply ms_refl ].
  - (* bin *) intros D G e1 o e2 A B R H1 IH1 H2 IH2 Hsig S HS HG r Hs. subst G.
    pose proof (bin_sig_same _ _ _ _ _ Hsig) as HBA. subst B.
    cbn [erase] in Hs. inversion Hs; subst; flip_erased.
    + lazymatch goal with Hx : step (erase e1) _ |- _ =>
        destruct (IH1 S HS eq_refl _ Hx) as [e1'' [Hm He]] end.
      exists (e_bin e1'' o e2). split; [ apply ms_bin1; exact Hm | cbn [erase]; rewrite He; reflexivity ].
    + assert (Hv1 : value (erase e1)) by assumption.
      destruct (value_reach D S e1 _ HS H1 Hv1) as [v1 [Hm1 [Hvv1 He1]]].
      lazymatch goal with Hx : step (erase e2) _ |- _ =>
        destruct (IH2 S HS eq_refl _ Hx) as [e2'' [Hm2 He2]] end.
      exists (e_bin v1 o e2''). split.
      * eapply multistep_trans; [ apply ms_bin1; exact Hm1 | apply ms_bin2; assumption ].
      * cbn [erase]. rewrite He1, He2. reflexivity.
    + assert (Hv1 : value (erase e1)) by assumption.
      assert (Hv2 : value (erase e2)) by assumption.
      lazymatch goal with Hbs : bin_step o (erase e1) (erase e2) r |- _ =>
        destruct (bin_step_cmp_or_lit _ _ _ _ Hbs) as [[c [Hk [Hcr ->]]] | [Hnk [La Lb]]];
        [ destruct (value_reach D S e1 _ HS H1 Hv1) as [v1 [Hm1 [Hvv1 Hev1]]];
          destruct (value_reach D S e2 _ HS H2 Hv2) as [v2 [Hm2 [Hvv2 Hev2]]];
          assert (Hcr2 : cmp_rel v1 v2 c)
            by (eapply cmp_unerase;
                [ exact (bin_sig_cmp_sat _ _ _ _ _ Hsig Hk) | exact Hvv1 | exact Hvv2
                | exact (preservation_multi _ _ _ _ _ HS H1 Hm1)
                | exact (preservation_multi _ _ _ _ _ HS H2 Hm2)
                | rewrite Hev1, Hev2; exact Hcr ]);
          exists (of_bool (cmp_holds o c)); split;
          [ eapply multistep_trans; [ apply ms_bin1; exact Hm1 | ];
            eapply multistep_trans; [ apply ms_bin2; [ exact Hvv1 | exact Hm2 ] | ];
            eapply ms_step; [ apply st_bin; [ exact Hvv1 | exact Hvv2 | apply (bs_cmp o _ _ c Hk Hcr2) ] | apply ms_refl ]
          | apply erase_of_bool ]
        | destruct (reach_operand D S e1 o A A R HS Hsig Hnk H1 Hv1) as [v1 [Hm1 [Hev1 Hk1]]];
          destruct (reach_operand D S e2 o A A R HS Hsig Hnk H2 Hv2) as [v2 [Hm2 [Hev2 Hk2]]];
          pose proof (operand_lit _ _ Hk1 Hev1 La) as E1;
          pose proof (operand_lit _ _ Hk2 Hev2 Lb) as E2;
          pose proof (erase_lit _ (bin_step_lit_result _ _ _ _ Hbs)) as Er;
          exists r; split; [ | exact Er ];
          eapply multistep_trans; [ apply ms_bin1; exact Hm1 | ];
          eapply multistep_trans; [ apply ms_bin2; [ rewrite E1; apply lit_value; exact La | exact Hm2 ] | ];
          rewrite E1, E2;
          eapply ms_step; [ apply st_bin; [ apply lit_value; exact La | apply lit_value; exact Lb | exact Hbs ] | apply ms_refl ] ]
      end.
    + lazymatch goal with
        Ha : erase e1 = e_rec ?fs1, Hb : erase e2 = e_rec ?fs2, Hz : rec_zip o (fs_plain ?fs1) (fs_plain ?fs2) ?fs |- _ =>
        assert (Hv1 : value (erase e1)) by (rewrite Ha; apply v_rec; assumption);
        assert (Hv2 : value (erase e2)) by (rewrite Hb; apply v_rec; assumption);
        destruct (reach_operand D S e1 o A A R HS Hsig ltac:(assumption) H1 Hv1) as [v1 [Hm1 [Hev1 Hk1]]];
        destruct (reach_operand D S e2 o A A R HS Hsig ltac:(assumption) H2 Hv2) as [v2 [Hm2 [Hev2 Hk2]]];
        destruct Hk1 as [[gs1 [-> Hg1]] | L1];
        [ | rewrite (erase_lit _ L1), Ha in Hev1; rewrite Hev1 in L1; cbn [lit] in L1; contradiction ];
        destruct Hk2 as [[gs2 [-> Hg2]] | L2];
        [ | rewrite (erase_lit _ L2), Hb in Hev2; rewrite Hev2 in L2; cbn [lit] in L2; contradiction ];
        cbn [erase] in Hev1, Hev2; rewrite Ha in Hev1; rewrite Hb in Hev2;
        injection Hev1 as Eg1; injection Hev2 as Eg2;
        destruct (rec_zip_unerase o _ _ _ Hz gs1 gs2 (f_equal fs_plain Eg1) (f_equal fs_plain Eg2)) as [gs [Hzz Hge]];
        exists (e_rec gs); split;
        [ eapply multistep_trans; [ apply ms_bin1; exact Hm1 | ];
          eapply multistep_trans; [ apply ms_bin2; [ apply v_rec; exact Hg1 | exact Hm2 ] | ];
          eapply ms_step; [ apply st_binrec; eassumption | apply ms_refl ]
        | cbn [erase]; rewrite Hge; reflexivity ]
      end.
  - (* spread *) intros D G e1 l e2 P T R Ht1 IH1 Ht2 IH2 S HS HG r Hs. subst G.
    cbn [erase] in Hs. inversion Hs; subst; flip_erased.
    + lazymatch goal with Hx : step (erase e1) _ |- _ =>
        destruct (IH1 S HS eq_refl _ Hx) as [e1'' [Hm He]] end.
      exists (e_spread e1'' l e2). split; [ apply ms_spread1; exact Hm | cbn [erase]; rewrite He; reflexivity ].
    + assert (Hv1 : value (erase e1)) by assumption.
      destruct (value_reach D S e1 _ HS Ht1 Hv1) as [v1 [Hm1 [Hvv1 He1]]].
      lazymatch goal with Hx : step (erase e2) _ |- _ =>
        destruct (IH2 S HS eq_refl _ Hx) as [e2'' [Hm2 He2]] end.
      exists (e_spread v1 l e2''). split.
      * eapply multistep_trans; [ apply ms_spread1; exact Hm1 | apply ms_spread2; assumption ].
      * cbn [erase]. rewrite He1, He2. reflexivity.
    + lazymatch goal with Ha : erase e1 = e_rec ?fs0, Hrv : rec_value ?fs0 |- _ =>
        destruct (reach_rec D S e1 _ fs0 HS Ht1 Ha Hrv) as [gs [Hm1 [Hrg Heg]]] end.
      assert (Hv2 : value (erase e2)) by assumption.
      destruct (value_reach D S e2 _ HS Ht2 Hv2) as [v2 [Hm2 [Hvv2 He2]]].
      exists (e_rec (fs_plain (fs_set l v2 gs))). split.
      * eapply multistep_trans; [ apply ms_spread1; exact Hm1 | ].
        eapply multistep_trans; [ apply ms_spread2; [ apply v_rec; exact Hrg | exact Hm2 ] | ].
        eapply ms_step; [ apply st_spread; assumption | apply ms_refl ].
      * cbn [erase]. rewrite erase_fs_plain, erase_fs_set, Heg, He2. reflexivity.
  - (* spread, on a base whose row lacks the label by its kind *)
    intros D G e1 l e2 T R Ht1 IH1 Hl Ht2 IH2 S HS HG r Hs. subst G.
    cbn [erase] in Hs. inversion Hs; subst; flip_erased.
    + lazymatch goal with Hx : step (erase e1) _ |- _ =>
        destruct (IH1 S HS eq_refl _ Hx) as [e1'' [Hm He]] end.
      exists (e_spread e1'' l e2). split; [ apply ms_spread1; exact Hm | cbn [erase]; rewrite He; reflexivity ].
    + assert (Hv1 : value (erase e1)) by assumption.
      destruct (value_reach D S e1 _ HS Ht1 Hv1) as [v1 [Hm1 [Hvv1 He1]]].
      lazymatch goal with Hx : step (erase e2) _ |- _ =>
        destruct (IH2 S HS eq_refl _ Hx) as [e2'' [Hm2 He2]] end.
      exists (e_spread v1 l e2''). split.
      * eapply multistep_trans; [ apply ms_spread1; exact Hm1 | apply ms_spread2; assumption ].
      * cbn [erase]. rewrite He1, He2. reflexivity.
    + lazymatch goal with Ha : erase e1 = e_rec ?fs0, Hrv : rec_value ?fs0 |- _ =>
        destruct (reach_rec D S e1 _ fs0 HS Ht1 Ha Hrv) as [gs [Hm1 [Hrg Heg]]] end.
      assert (Hv2 : value (erase e2)) by assumption.
      destruct (value_reach D S e2 _ HS Ht2 Hv2) as [v2 [Hm2 [Hvv2 He2]]].
      exists (e_rec (fs_plain (fs_set l v2 gs))). split.
      * eapply multistep_trans; [ apply ms_spread1; exact Hm1 | ].
        eapply multistep_trans; [ apply ms_spread2; [ apply v_rec; exact Hrg | exact Hm2 ] | ].
        eapply ms_step; [ apply st_spread; assumption | apply ms_refl ].
      * cbn [erase]. rewrite erase_fs_plain, erase_fs_set, Heg, He2. reflexivity.
  - (* restrict *) intros D G e l R0 T R Ht IH Hrm S HS HG r Hs. subst G.
    cbn [erase] in Hs. inversion Hs; subst; flip_erased.
    + lazymatch goal with Hx : step (erase e) _ |- _ =>
        destruct (IH S HS eq_refl _ Hx) as [e'' [Hm He]] end.
      exists (e_restrict e'' l). split; [ apply ms_restrict; exact Hm | cbn [erase]; rewrite He; reflexivity ].
    + lazymatch goal with Ha : erase e = e_rec ?fs0, Hrv : rec_value ?fs0 |- _ =>
        destruct (reach_rec D S e _ fs0 HS Ht Ha Hrv) as [gs [Hm [Hrg Heg]]] end.
      exists (e_rec (fs_plain (fs_drop l gs))). split.
      * eapply multistep_trans; [ apply ms_restrict; exact Hm | ].
        eapply ms_step; [ apply st_restrict; exact Hrg | apply ms_refl ].
      * cbn [erase]. rewrite erase_fs_plain, erase_fs_drop, Heg. reflexivity.
  - (* fold *) intros D G e B Hlc Hg Ht IH S HS HG r Hs. cbn [erase] in Hs.
    destruct (IH S HS HG r Hs) as [e'' [Hm He]].
    exists (e_fold e''). split; [ apply ms_fold; exact Hm | cbn [erase]; exact He ].
  - (* unfold *) intros D G e B Hlc Hg Ht IH S HS HG r Hs. cbn [erase] in Hs.
    destruct (IH S HS HG r Hs) as [e'' [Hm He]].
    exists (e_unfold e''). split; [ apply ms_unfold; exact Hm | cbn [erase]; exact He ].
  - (* con *) intros D G w tg e Ts Hlt Ht IH S HS HG r Hs. subst G.
    cbn [erase] in Hs. inversion Hs; subst; flip_erased.
    lazymatch goal with Hx : step (erase e) _ |- _ =>
      destruct (IH S HS eq_refl _ Hx) as [e'' [Hm He]] end.
    exists (e_con w tg e''). split; [ apply ms_con; exact Hm | cbn [erase]; rewrite He; reflexivity ].
  - (* match *) intros L D G w Ts e ars T Ht IHe Hwf Harm IHarm Hdef IHdef S HS HG r Hs. subst G.
    cbn [erase] in Hs. inversion Hs; subst; flip_erased.
    + lazymatch goal with Hx : step (erase e) _ |- _ =>
        destruct (IHe S HS eq_refl _ Hx) as [e'' [Hm He]] end.
      exists (e_match w e'' ars). split; [ apply ms_match; exact Hm | cbn [erase]; rewrite He; reflexivity ].
    + lazymatch goal with Ha : erase e = e_con ?w' ?tg ?v, Hv0 : value ?v,
          Hf : arms_find ?tg (erase_arms ars) = Some ?body |- _ =>
        destruct (reach_con D S e w Ts w' tg v HS Ht Ha Hv0) as [v1 [Hm [Hv1 Hev1]]];
        rewrite erase_arms_find in Hf;
        destruct (arms_find tg ars) as [b0 | ] eqn:Hb0; cbn [option_map] in Hf; try discriminate;
        injection Hf as Hbody;
        exists (open_exp_wrt_exp b0 v1); split;
        [ eapply multistep_trans; [ apply ms_match; exact Hm | ];
          eapply ms_step; [ apply st_match_arm; eassumption | apply ms_refl ]
        | rewrite erase_open, Hev1, Hbody; reflexivity ]
      end.
    + lazymatch goal with Ha : erase e = e_con ?w' ?tg ?v, Hv0 : value ?v,
          Hf : arms_find ?tg (erase_arms ars) = None,
          Hd : arms_default (erase_arms ars) = Some ?e0 |- _ =>
        destruct (reach_con D S e w Ts w' tg v HS Ht Ha Hv0) as [v1 [Hm [Hv1 Hev1]]];
        rewrite erase_arms_find in Hf;
        destruct (arms_find tg ars) as [b0 | ] eqn:Hb0; cbn [option_map] in Hf; try discriminate;
        rewrite erase_arms_default in Hd;
        destruct (arms_default ars) as [d0 | ] eqn:Hd0; cbn [option_map] in Hd; try discriminate;
        injection Hd as Hde;
        exists d0; split;
        [ eapply multistep_trans; [ apply ms_match; exact Hm | ];
          eapply ms_step; [ apply st_match_else; eassumption | apply ms_refl ]
        | exact Hde ]
      end.
  - intros D G Hu S HS HG fs'' Hs. cbn [erase_fields] in Hs. inversion Hs.
  - intros D G l e T fs R Hty IH1 Hft IH2 S HS HG fs'' Hs. subst G.
    cbn [erase_fields] in Hs. inversion Hs; subst.
    + lazymatch goal with Hx : step (erase e) _ |- _ =>
        destruct (IH1 S HS eq_refl _ Hx) as [e'' [Hm He]] end.
      exists (fs_cons l e'' fs). split;
        [ apply msf_here; exact Hm | cbn [erase_fields]; rewrite He; reflexivity ].
    + assert (Hv : value (erase e)) by assumption.
      destruct (value_reach D S e _ HS Hty Hv) as [v [Hm [Hvv He]]].
      lazymatch goal with Hx : step_fields (erase_fields fs) _ |- _ =>
        destruct (IH2 S HS eq_refl _ Hx) as [fsx [Hmf Hef]] end.
      exists (fs_cons l v fsx). split.
      * eapply msf_trans; [ apply msf_here; exact Hm | apply msf_cons; assumption ].
      * cbn [erase_fields]. rewrite He, Hef. reflexivity.
  - intros D G l e T fs R Hty IH1 Hft IH2 S HS HG fs'' Hs. subst G.
    cbn [erase_fields] in Hs. inversion Hs; subst.
    + lazymatch goal with Hx : step (erase e) _ |- _ =>
        destruct (IH1 S HS eq_refl _ Hx) as [e'' [Hm He]] end.
      exists (fs_meth l e'' fs). split;
        [ apply msf_here_meth; exact Hm | cbn [erase_fields]; rewrite He; reflexivity ].
    + assert (Hv : value (erase e)) by assumption.
      destruct (value_reach D S e _ HS Hty Hv) as [v [Hm [Hvv He]]].
      lazymatch goal with Hx : step_fields (erase_fields fs) _ |- _ =>
        destruct (IH2 S HS eq_refl _ Hx) as [fsx [Hmf Hef]] end.
      exists (fs_meth l v fsx). split.
      * eapply msf_trans; [ apply msf_here_meth; exact Hm | apply msf_meth; assumption ].
      * cbn [erase_fields]. rewrite He, Hef. reflexivity.
Qed.

(* A step of the erased term is matched by the elaborated term, up to
   [unfold (fold v) --> v]. *)
Theorem erase_converse : forall D S e T r,
  supp_ok D S -> typing D nil e T -> step (erase e) r ->
  exists e'', multistep e e'' /\ erase e'' = r.
Proof. intros D S e T r HS Ht Hs. exact (proj1 erase_converse_mut D nil e T Ht S HS eq_refl r Hs). Qed.

(* ... and a run of the erased term by a run of the elaborated one. *)
Theorem erase_converse_multistep : forall D S e T r,
  supp_ok D S -> typing D nil e T -> multistep (erase e) r ->
  exists e'', multistep e e'' /\ erase e'' = r.
Proof.
  intros D S e T r HS Ht H. remember (erase e) as x eqn:Hx.
  revert e T Ht Hx. induction H as [x | x y z Hxy Hyz IH]; intros e T Ht Hx.
  - exists e. split; [ apply ms_refl | symmetry; exact Hx ].
  - subst x. destruct (erase_converse D S e T y HS Ht Hxy) as [e1 [Hm1 He1]].
    destruct (IH e1 T (preservation_multi _ _ _ _ _ HS Ht Hm1) (eq_sym He1)) as [e2 [Hm2 He2]].
    exists e2. split; [ eapply multistep_trans; eassumption | exact He2 ].
Qed.

(* The same, for a closed program in the empty kinding environment, which is
   where the elaborated programs of [infer_elab] live. *)
Corollary erase_converse_closed : forall e T r,
  typing d_any nil e T -> step (erase e) r ->
  exists e'', multistep e e'' /\ erase e'' = r.
Proof. intros e T r Ht Hs. apply (erase_converse d_any {} e T r); [ | exact Ht | exact Hs ]. intros a _. split; reflexivity. Qed.
