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
Require Import Goat.GoatMu.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatElab.
Require Import Stdlib.Lists.List.
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

Lemma bin_step_lit : forall o a b v, bin_step o a b v -> lit a /\ lit b.
Proof.
  intros o a b v H. inversion H; subst;
    repeat match goal with
           | Hp : fl_pair ?x ?y |- _ => inversion Hp; subst; clear Hp
           | Hc : cmp_rel ?x ?y _ |- _ => inversion Hc; subst; clear Hc
           | Hv : val_bool ?x = Some _ |- _ => destruct x; cbn in Hv; try discriminate; clear Hv
           end;
    split; exact I.
Qed.

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
  bin_sig D o A B R -> value v -> typing D G v A ->
  (exists gs, v = e_rec gs /\ rec_value gs) \/ lit v.
Proof.
  intros D G o A B R v Hs Hv Hty.
  assert (Hnum : forall A0, sat D k_Numeric A0 -> typing D G v A0 ->
            (exists gs, v = e_rec gs /\ rec_value gs) \/ lit v).
  { intros A0 Hsat Ht. destruct A0; simpl in Hsat; try discriminate Hsat;
      try (destruct Hsat as [Hsat | Hsat]; discriminate Hsat).
    - right. eapply canon_lit; [ eassumption | eassumption | base_type ].
    - right. eapply canon_lit; [ eassumption | eassumption | base_type ].
    - left. destruct (canon_record _ _ _ _ Hv Ht) as [gs [Rx [-> [Hrv _]]]]. eauto.
    - right. eapply canon_lit; [ eassumption | eassumption | base_type ]. }
  inversion Hs; subst.
  - eapply Hnum; eassumption.
  - right. eapply canon_lit; [ eassumption | eassumption | base_type ].
  - eapply Hnum; eassumption.
  - left. destruct (canon_record _ _ _ _ Hv Hty) as [gs [Rx [-> [Hrv _]]]]. eauto.
  - match goal with Hs0 : sat D k_Eq ?X |- _ => destruct X; simpl in Hs0;
      try (destruct Hs0 as [Hs0 | Hs0]; discriminate Hs0); try discriminate Hs0 end.
    + right. eapply canon_lit; [ eassumption | eassumption | base_type ].
    + right. eapply canon_lit; [ eassumption | eassumption | base_type ].
    + right. eapply canon_lit; [ eassumption | eassumption | base_type ].
    + right. rewrite (canon_unit _ _ _ _ Hv Hty (teq_refl _)). exact I.
    + right. eapply canon_lit; [ eassumption | eassumption | base_type ].
    + left. destruct (canon_record _ _ _ _ Hv Hty) as [gs [Rx [-> [Hrv _]]]]. eauto.
    + right. eapply canon_lit; [ eassumption | eassumption | base_type ].
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
  - intros L D G e1 e2 T1 T2 kf Tm Hgv H1 IH1 Hb IH2 S HS HG Hv. cbn [erase] in Hv. inversion Hv.
  - intros L D G e1 e2 T1 T2 H1 IH1 Hb IH2 S HS HG Hv. cbn [erase] in Hv. inversion Hv.
  - intros L D G fs e2 R T kf Hfg Hfs IHfs Hb IH2 S HS HG Hv. cbn [erase] in Hv. inversion Hv.
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
  bin_sig D o A B R -> typing D nil e A -> value (erase e) ->
  exists v, multistep e v /\ erase v = erase e /\
    ((exists gs, v = e_rec gs /\ rec_value gs) \/ lit v).
Proof.
  intros D S e o A B R HS Hs Ht Hv.
  destruct (value_reach D S e _ HS Ht Hv) as [v [Hm [Hvv Hev]]].
  exists v. repeat split; [ exact Hm | exact Hev | ].
  eapply bin_operand; [ exact Hs | exact Hvv | eapply preservation_multi; eassumption ].
Qed.

Lemma rec_value_lookup : forall l fs w, rec_value fs -> lookup_first l fs = Some w -> value w.
Proof.
  intros l fs w H. induction H; cbn [lookup_first]; intros Hl; [ discriminate | | ];
    destruct (Nat.eqb l l0); first [ injection Hl as <-; assumption | auto ].
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
  - (* let *) intros L D G e1 e2 T1 T2 kf Tm Hgv H1 IH1 Hb IH2 S HS HG r Hs. subst G.
    eapply let_converse; [ | | exact Hs ].
    + intros Hv. exact (value_reach _ _ e1 _ (supp_ok_ext _ _ _ _ HS) H1 Hv).
    + intros r1 Hx. exact (IH1 _ (supp_ok_ext _ _ _ _ HS) eq_refl _ Hx).
  - (* letmono *) intros L D G e1 e2 T1 T2 H1 IH1 Hb IH2 S HS HG r Hs. subst G.
    eapply let_converse; [ | | exact Hs ].
    + intros Hv. exact (value_reach D S e1 _ HS H1 Hv).
    + intros r1 Hx. exact (IH1 S HS eq_refl _ Hx).
  - (* letrec *) intros L D G fs e2 R T kf Hfg Hfs IHfs Hb IH2 S HS HG r Hs. subst G.
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
        destruct (bin_step_lit _ _ _ _ Hbs) as [La Lb];
        destruct (reach_operand D S e1 o A A R HS Hsig H1 Hv1) as [v1 [Hm1 [Hev1 Hk1]]];
        destruct (reach_operand D S e2 o A A R HS Hsig H2 Hv2) as [v2 [Hm2 [Hev2 Hk2]]];
        pose proof (operand_lit _ _ Hk1 Hev1 La) as E1;
        pose proof (operand_lit _ _ Hk2 Hev2 Lb) as E2;
        destruct (erase_bin_step _ _ _ _ Hbs) as [_ [_ Er]];
        exists r; split; [ | exact Er ];
        eapply multistep_trans; [ apply ms_bin1; exact Hm1 | ];
        eapply multistep_trans; [ apply ms_bin2; [ rewrite E1; apply lit_value; exact La | exact Hm2 ] | ];
        rewrite E1, E2;
        eapply ms_step; [ apply st_bin; [ apply lit_value; exact La | apply lit_value; exact Lb | exact Hbs ] | apply ms_refl ]
      end.
    + lazymatch goal with
        Ha : erase e1 = e_rec ?fs1, Hb : erase e2 = e_rec ?fs2, Hz : rec_zip o (fs_plain ?fs1) (fs_plain ?fs2) ?fs |- _ =>
        assert (Hv1 : value (erase e1)) by (rewrite Ha; apply v_rec; assumption);
        assert (Hv2 : value (erase e2)) by (rewrite Hb; apply v_rec; assumption);
        destruct (reach_operand D S e1 o A A R HS Hsig H1 Hv1) as [v1 [Hm1 [Hev1 Hk1]]];
        destruct (reach_operand D S e2 o A A R HS Hsig H2 Hv2) as [v2 [Hm2 [Hev2 Hk2]]];
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
    + lazymatch goal with
        Ha : erase e1 = e_rec ?fs1, Hb : erase e2 = e_rec ?fs2, Hk : kind o = k_cmp |- _ =>
        assert (Hv1 : value (erase e1)) by (rewrite Ha; apply v_rec; assumption);
        assert (Hv2 : value (erase e2)) by (rewrite Hb; apply v_rec; assumption);
        destruct (reach_operand D S e1 o A A R HS Hsig H1 Hv1) as [v1 [Hm1 [Hev1 Hk1]]];
        destruct (reach_operand D S e2 o A A R HS Hsig H2 Hv2) as [v2 [Hm2 [Hev2 Hk2]]];
        destruct Hk1 as [[gs1 [-> Hg1]] | L1];
        [ | rewrite (erase_lit _ L1), Ha in Hev1; rewrite Hev1 in L1; cbn [lit] in L1; contradiction ];
        destruct Hk2 as [[gs2 [-> Hg2]] | L2];
        [ | rewrite (erase_lit _ L2), Hb in Hev2; rewrite Hev2 in L2; cbn [lit] in L2; contradiction ];
        match goal with |- context [of_bool (cmp_holds o ?c)] =>
          exists (of_bool (cmp_holds o c)); split;
          [ eapply multistep_trans; [ apply ms_bin1; exact Hm1 | ];
            eapply multistep_trans; [ apply ms_bin2; [ apply v_rec; exact Hg1 | exact Hm2 ] | ];
            eapply ms_step; [ apply st_cmprec; assumption | apply ms_refl ]
          | apply erase_of_bool ] end
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
Proof. intros e T r Ht Hs. apply (erase_converse d_any {} e T r); [ | exact Ht | exact Hs ]. intros a _. reflexivity. Qed.
