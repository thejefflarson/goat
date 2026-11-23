(* Completeness of algorithm W, stage 7.5, part L1: the instance order on
   schemes and contexts (docs/design/phase7-proof-plan.md).

   [sch_le D s s'] says [s] is an instance of [s']: every instance of [s] (a
   type [inst] accepts, under the sorts [s] records for its quantified
   variables) is an instance of [s'], and the free variables of [s'] are free
   in [s].  The free variables of [s] keep their sorts and kinds from [D]; an
   environment that agrees with [D] on them gives the same answer, which is
   what lets a [let] extend [D] on the variables it generalizes ([ext],
   [extr]) without disturbing the context.

   [ctx_le D G G'] is the pointwise order on two contexts of the same names.
   [typing_ctx_le]: a derivation under the context of instances is a
   derivation under the more general one, in the same environment.  A [let]
   under the more general context may generalize fewer variables, since the
   context may mention variables the instances' does not; [ctx_le] therefore
   records that the more general context's free variables are free in the
   other, which is what the [T_Let] and [T_Letrec] cases use.

   The existing [sch_more_gen] (GoatSubst.v), which quantifies more over the
   same body, is the special case that [typing_ftv_mono] covers; [sch_more_gen_le]
   embeds it, and [typing_ctx_le] is the same proof with the instance order in
   its place. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- schemes ---- *)

Definition sch_le (D : denv) (s s' : scheme) : Prop :=
  ftv_sch s' [<=] ftv_sch s /\ frv_sch s' [<=] frv_sch s /\
  forall D' : denv, (forall a, a `in` ftv_sch s -> D' a = D a) ->
             (forall r, r `in` frv_sch s -> drk D' r = drk D r) ->
             forall T, inst D' T s -> inst D' T s'.

Lemma sch_le_refl : forall D s, sch_le D s s.
Proof. intros D s. split; [ fsetdec | split; [ fsetdec | intros; assumption ] ]. Qed.

Lemma sch_le_trans : forall D s1 s2 s3, sch_le D s1 s2 -> sch_le D s2 s3 -> sch_le D s1 s3.
Proof.
  intros D s1 s2 s3 (A1 & B1 & C1) (A2 & B2 & C2).
  split; [ fsetdec | split; [ fsetdec | ] ].
  intros D' Hd Hr T H. apply (C2 D'); [ | | apply (C1 D' Hd Hr T H) ].
  - intros a Ha. apply Hd. apply A1. exact Ha.
  - intros r Hrr. apply Hr. apply B1. exact Hrr.
Qed.

Lemma sch_le_inst : forall D s s' T, sch_le D s s' -> inst D T s -> inst D T s'.
Proof. intros D s s' T (_ & _ & H) Hi. exact (H D (fun _ _ => eq_refl) (fun _ _ => eq_refl) T Hi). Qed.

Lemma sch_le_env : forall (D D2 : denv) s s',
  (forall a, a `in` ftv_sch s -> D2 a = D a) ->
  (forall r, r `in` frv_sch s -> drk D2 r = drk D r) ->
  sch_le D s s' -> sch_le D2 s s'.
Proof.
  intros D D2 s s' Hv Hr (A & B & C). split; [ exact A | split; [ exact B | ] ].
  intros D' Hd Hdr T H. apply (C D'); [ | | exact H ].
  - intros a Ha. rewrite (Hd a Ha). apply Hv. exact Ha.
  - intros r Hrr. rewrite (Hdr r Hrr). apply Hr. exact Hrr.
Qed.

Lemma sch_le_ext : forall D V k s s',
  (forall a, a `in` ftv_sch s -> a `notin` V) ->
  sch_le D s s' -> sch_le (ext D V k) s s'.
Proof.
  intros D V k s s' Hv H. eapply sch_le_env; [ | | exact H ].
  - intros a Ha. apply ext_out. apply Hv. exact Ha.
  - intros r Hr. reflexivity.
Qed.

Lemma sch_le_extr : forall D V rk s s',
  (forall r, r `in` frv_sch s -> r `notin` V) ->
  sch_le D s s' -> sch_le (extr D V rk) s s'.
Proof.
  intros D V rk s s' Hv H. eapply sch_le_env; [ | | exact H ].
  - intros a Ha. reflexivity.
  - intros r Hr. unfold extr; simpl.
    destruct (AtomSetImpl.mem r V) eqn:Em; [ | reflexivity ].
    apply AtomSetFacts.mem_iff in Em. exfalso. apply (Hv r Hr). exact Em.
Qed.

(* The scheme that quantifies more over the same body is more general. *)
Lemma sch_more_gen_le : forall D s s', sch_more_gen D s s' -> sch_le D s s'.
Proof.
  intros D s s' H. split; [ | split ].
  - intros a Ha. exact (sch_more_gen_ftv D s s' a H Ha).
  - intros r Hr. exact (sch_more_gen_frv D s s' r H Hr).
  - intros D' Hd Hr T Hi. eapply sch_more_gen_inst; [ | exact Hi ].
    eapply sch_more_gen_env; [ | | exact H ]; assumption.
Qed.

(* ---- contexts ---- *)

Definition ctx_le (D : denv) (G G' : ctx) : Prop :=
  Forall2 (fun b b' => fst b = fst b' /\ sch_le D (snd b) (snd b')) G G'.

Lemma ctx_le_refl : forall D G, ctx_le D G G.
Proof. induction G as [|[x s] G IH]; constructor; simpl; auto using sch_le_refl. Qed.

Lemma ctx_le_trans : forall D G1 G2 G3, ctx_le D G1 G2 -> ctx_le D G2 G3 -> ctx_le D G1 G3.
Proof.
  intros D G1 G2 G3 H. revert G3.
  induction H as [|[x s1][y s2] G1 G2 [Hk Hs] HF IH]; intros G3 H2.
  - inversion H2; subst; constructor.
  - inversion H2 as [|[y2 s2'] [z s3] G2' G3' [Hk2 Hs2'] HF2]; subst. simpl in *. subst.
    constructor; [ simpl; split; [ reflexivity | eapply sch_le_trans; eassumption ] | exact (IH _ HF2) ].
Qed.

Lemma ctx_le_cons : forall D x s s' G G',
  sch_le D s s' -> ctx_le D G G' -> ctx_le D ((x ~ s) ++ G) ((x ~ s') ++ G').
Proof. intros. constructor; simpl; auto. Qed.

Lemma ctx_le_dom : forall D G G', ctx_le D G G' -> dom G [=] dom G'.
Proof.
  induction 1 as [|[x s][y s'] G G' [Hk He] HF IH]; simpl in *; [reflexivity|].
  subst y. rewrite IH. reflexivity.
Qed.

Lemma ctx_le_uniq : forall D G G', ctx_le D G G' -> uniq G -> uniq G'.
Proof.
  induction 1 as [|[x s][y s'] G G' [Hk He] HF IH]; intros Hu; auto.
  simpl in *; subst y. inversion Hu; subst.
  constructor; auto. rewrite <- (ctx_le_dom _ _ _ HF); auto.
Qed.

Lemma ctx_le_binds : forall D G G' x s,
  ctx_le D G G' -> binds x s G ->
  exists s', binds x s' G' /\ sch_le D s s'.
Proof.
  induction 1 as [|[y sy][z sz] G G' [Hk He] HF IH]; intros Hb; [inversion Hb|].
  simpl in *; subst z. apply binds_cons_1 in Hb. destruct Hb as [[Hx Hs]|Hb].
  - subst. exists sz. split; [apply binds_cons_2; auto|auto].
  - destruct (IH Hb) as [s' [Hb' Hg']]. exists s'. split; [apply binds_cons_3; auto|auto].
Qed.

Lemma ctx_le_Ftv : forall D G G' a, ctx_le D G G' -> Ftv_ctx G' a -> Ftv_ctx G a.
Proof.
  unfold Ftv_ctx. induction 1 as [|[y sy][z sz] G G' [Hk Hg] HF IH]; simpl; intros Hin.
  - fsetdec.
  - rewrite AtomSetFacts.union_iff in Hin |- *.
    destruct Hin as [Hin|Hin];
      [ left; exact (proj1 Hg a Hin) | right; apply IH; exact Hin ].
Qed.

Lemma ctx_le_Frv : forall D G G' r, ctx_le D G G' -> Frv_ctx G' r -> Frv_ctx G r.
Proof.
  unfold Frv_ctx. induction 1 as [|[y sy][z sz] G G' [Hk Hg] HF IH]; simpl; intros Hin.
  - fsetdec.
  - rewrite AtomSetFacts.union_iff in Hin |- *.
    destruct Hin as [Hin|Hin];
      [ left; exact (proj1 (proj2 Hg) r Hin) | right; apply IH; exact Hin ].
Qed.

Lemma ctx_le_ftv : forall D G G', ctx_le D G G' -> ftv_ctx G' [<=] ftv_ctx G.
Proof. intros D G G' H a Ha. exact (ctx_le_Ftv D G G' a H Ha). Qed.

Lemma ctx_le_frv : forall D G G', ctx_le D G G' -> frv_ctx G' [<=] frv_ctx G.
Proof. intros D G G' H a Ha. exact (ctx_le_Frv D G G' a H Ha). Qed.

Lemma ctx_le_ext : forall D V k G G',
  (forall a, a `in` ftv_ctx G -> a `notin` V) ->
  ctx_le D G G' -> ctx_le (ext D V k) G G'.
Proof.
  intros D V k G G' Hv H. revert Hv.
  induction H as [|[y sy][z sz] G G' [Hk Hg] HF IH]; intros Hv; constructor.
  - simpl. split; [ exact Hk | ]. apply sch_le_ext; [ | exact Hg ].
    intros a Ha. apply Hv. simpl. fsetdec.
  - apply IH. intros a Ha. apply Hv. simpl. fsetdec.
Qed.

Lemma ctx_le_extr : forall D V rk G G',
  (forall r, r `in` frv_ctx G -> r `notin` V) ->
  ctx_le D G G' -> ctx_le (extr D V rk) G G'.
Proof.
  intros D V rk G G' Hv H. revert Hv.
  induction H as [|[y sy][z sz] G G' [Hk Hg] HF IH]; intros Hv; constructor.
  - simpl. split; [ exact Hk | ]. apply sch_le_extr; [ | exact Hg ].
    intros a Ha. apply Hv. simpl. fsetdec.
  - apply IH. intros a Ha. apply Hv. simpl. fsetdec.
Qed.

Lemma ctx_more_gen_le : forall D G G', ctx_more_gen D G G' -> ctx_le D G G'.
Proof.
  induction 1 as [|[x s][y s'] G G' [Hk He] HF IH]; constructor; simpl; auto using sch_more_gen_le.
Qed.

(* ---- typing is monotone in the instance order ---- *)

Lemma typing_ctx_le_mut :
  (forall D G e T, typing D G e T -> forall G', ctx_le D G G' -> typing D G' e T) /\
  (forall D G fs R, field_typing D G fs R -> forall G', ctx_le D G G' -> field_typing D G' fs R).
Proof.
  apply typing_field_mutind; intros.
  - (* T_Var *) destruct (ctx_le_binds _ _ _ _ _ H b) as [s' [Hb' Hg]].
    apply T_Var with (s := s'); eauto using ctx_le_uniq, sch_le_inst.
  - apply T_Num; eauto using ctx_le_uniq.
  - apply T_Dec; eauto using ctx_le_uniq.
  - apply T_True; eauto using ctx_le_uniq.
  - apply T_False; eauto using ctx_le_uniq.
  - (* T_Abs *) apply T_Abs with (L := L); intros x Hx.
    apply H; auto. apply ctx_le_cons; auto using sch_le_refl.
  - eapply T_App; eauto.
  - (* T_Let *)
    assert (HV : forall a, a `in` ftv_ctx G -> a `notin` AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G)))
      by (intros a Ha Hd; apply AtomSetFacts.diff_iff in Hd; rewrite ftv_pin_ctx in Hd; fsetdec).
    assert (HVr : forall a, a `in` frv_ctx G -> a `notin` AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G)))
      by (intros a Ha Hd; apply AtomSetFacts.diff_iff in Hd; rewrite frv_pin_ctx in Hd; fsetdec).
    assert (HF : ftv_ctx G' [<=] ftv_ctx G) by (eapply ctx_le_ftv; eauto).
    assert (HR : frv_ctx G' [<=] frv_ctx G) by (eapply ctx_le_frv; eauto).
    assert (HF' : ftv_ctx (pin_ctx Tm G') [<=] ftv_ctx (pin_ctx Tm G))
      by (rewrite !ftv_pin_ctx; fsetdec).
    assert (HR' : frv_ctx (pin_ctx Tm G') [<=] frv_ctx (pin_ctx Tm G))
      by (rewrite !frv_pin_ctx; fsetdec).
    destruct (repin Tm G G' HF HR) as [Tm' [HFe HRe]].
    set (V := AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G))).
    assert (HVe : AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm' G')) [=] V)
      by (unfold V; rewrite HFe; reflexivity).
    apply T_Let with (L := L) (T1 := T1) (Tm := Tm') (k := kup D V k)
      (rk := rkup D (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G))) rk); auto.
    + eapply lit_pinned_kup; [ exact l | ]. rewrite HVe. fsetdec.
    + eapply typing_pw.
      * apply H. apply ctx_le_extr; [ exact HVr | ].
        apply ctx_le_ext; [ exact HV | exact H1 ].
      * apply denv_eq_trans with
          (D2 := extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm' G'))) (kup D V k))
                 (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G))) rk).
        -- apply extr_pw. apply ext_kup_d. rewrite HVe. fsetdec.
        -- apply extr_rkup; [ intros; reflexivity | ].
           intros b Hb. apply AtomSetFacts.diff_iff in Hb as [Hb Hc].
           apply AtomSetFacts.diff_iff. split; [ exact Hb | intro Hd; apply Hc; apply HRe; exact Hd ].
    + intros x Hx. apply H0; auto.
      apply ctx_le_cons;
        [ apply sch_more_gen_le; apply gen_more_gen; [ rewrite HFe; fsetdec | exact HRe ] | exact H1 ].
  - (* T_LetMono *) apply T_LetMono with (L := L) (T1 := T1); auto. intros x Hx.
    apply H0; auto. apply ctx_le_cons; auto using sch_le_refl.
  - (* T_Letrec *)
    assert (HV : forall a, a `in` ftv_ctx G -> a `notin` AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G))
      by (intros a Ha Hd; apply AtomSetFacts.diff_iff in Hd; tauto).
    assert (HVr : forall a, a `in` frv_ctx G -> a `notin` AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G))
      by (intros a Ha Hd; apply AtomSetFacts.diff_iff in Hd; tauto).
    assert (HF : ftv_ctx G' [<=] ftv_ctx G) by (eapply ctx_le_ftv; eauto).
    assert (HR : frv_ctx G' [<=] frv_ctx G) by (eapply ctx_le_frv; eauto).
    apply T_Letrec with (L := L) (R := R)
      (k := kup D (AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G)) k)
      (rk := rkup D (AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G)) rk); auto.
    + intros p Hp. eapply field_typing_pw.
      * apply H; auto. apply ctx_le_cons; [ apply sch_le_refl | ].
        apply ctx_le_extr; [ exact HVr | ].
        apply ctx_le_ext; [ exact HV | exact H1 ].
      * apply denv_eq_trans with
          (D2 := extr (ext D (AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G')) (kup D (AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G)) k))
                 (AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G)) rk).
        -- apply extr_pw. apply ext_kup_d. intros b Hb. apply AtomSetFacts.diff_iff in Hb as [Hb Hc].
           apply AtomSetFacts.diff_iff. split; [ exact Hb | intro Hd; apply Hc; apply HF; exact Hd ].
        -- apply extr_rkup; [ intros; reflexivity | ].
           intros b Hb. apply AtomSetFacts.diff_iff in Hb as [Hb Hc].
           apply AtomSetFacts.diff_iff. split; [ exact Hb | intro Hd; apply Hc; apply HR; exact Hd ].
    + intros p Hp. apply H0; auto.
      apply ctx_le_cons; [ apply sch_more_gen_le; apply gen_more_gen; assumption | exact H1 ].
  - apply T_Record; eauto.
  - eapply T_Obj; eauto.
  - eapply T_Proj; eauto.
  - eapply T_Conv; eauto.
  - apply T_Unit; eauto using ctx_le_uniq.
  - apply T_Str; eauto using ctx_le_uniq.
  - eapply T_If; eauto.
  - eapply T_ToFloat; eauto.
  - eapply T_Bin; eauto.
  - eapply T_Spread; eauto.
  - eapply T_SpreadL; eauto.
  - eapply T_Restrict; eauto.
  - eapply T_Fold; eauto.
  - eapply T_Unfold; eauto.
  - eapply T_Con; eauto.
  - eapply T_Match with (L := L); [ eauto | assumption | | intros e0 Hd; eauto ].
    intros tg b Hf x Hx. eapply (H0 tg b Hf x Hx).
    apply ctx_le_cons; auto using sch_le_refl.
  - apply FT_nil; eauto using ctx_le_uniq.
  - eapply FT_cons; eauto.
  - eapply FT_meth; eauto.
Qed.

Theorem typing_ctx_le : forall D G G' e T,
  typing D G e T -> ctx_le D G G' -> typing D G' e T.
Proof. intros. eapply (proj1 typing_ctx_le_mut); eauto. Qed.

(* ---- the order is not trivial ---- *)

Definition id_atom : atom := pin_name.

Definition id_sch : scheme :=
  Sch {{id_atom}} {} (typ_Arrow (typ_Var id_atom) (typ_Var id_atom)) (fun _ => k_Any) (fun _ => rk_any).

(* [Int -> Int] is an instance of the identity scheme. *)
Example int_id_le_id_sch : sch_le d_any (sch_mono (typ_Arrow typ_Int typ_Int)) id_sch.
Proof.
  split; [ | split ].
  - intros x Hx. unfold ftv_sch, id_sch in Hx. cbn [s_body s_tq] in Hx.
    apply AtomSetFacts.diff_iff in Hx as [Hx Hn]. simpl in Hx. fsetdec.
  - intros x Hx. unfold frv_sch, id_sch in Hx. cbn [s_body s_rq] in Hx.
    apply AtomSetFacts.diff_iff in Hx as [Hx Hn]. simpl in Hx. fsetdec.
  - intros D' _ _ T H. apply inst_mono_eq in H. subst T.
    exists (fun b => if Atom.eq_dec b id_atom then typ_Int else typ_Var b), idr.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + intros a Ha. destruct (Atom.eq_dec a id_atom) as [->|_]; [ exfalso; apply Ha; cbn [id_sch s_tq]; fsetdec | reflexivity ].
    + intros r _. reflexivity.
    + simpl. destruct (Atom.eq_dec id_atom id_atom) as [_|Hn]; [ reflexivity | contradiction ].
    + intros a _. apply sat_any.
    + intros r Hr. cbn [id_sch s_rq] in Hr. fsetdec.
    + split; [ intros a; destruct (Atom.eq_dec a id_atom); exact I | intros r; exact I ].
Qed.

(* ... and the identity scheme is not an instance of [Int -> Int]: an instance
   of the identity scheme at [Bool] is not an instance of the monotype. *)
Example id_sch_not_le_int_id : ~ sch_le d_any id_sch (sch_mono (typ_Arrow typ_Int typ_Int)).
Proof.
  intros (_ & _ & H).
  assert (Hi : inst d_any (typ_Arrow typ_Bool typ_Bool) id_sch).
  { exists (fun b => if Atom.eq_dec b id_atom then typ_Bool else typ_Var b), idr.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    - intros a Ha. destruct (Atom.eq_dec a id_atom) as [->|_]; [ exfalso; apply Ha; cbn [id_sch s_tq]; fsetdec | reflexivity ].
    - intros r _. reflexivity.
    - simpl. destruct (Atom.eq_dec id_atom id_atom) as [_|Hn]; [ reflexivity | contradiction ].
    - intros a _. apply sat_any.
    - intros r Hr. cbn [id_sch s_rq] in Hr. fsetdec.
    - split; [ intros a; destruct (Atom.eq_dec a id_atom); exact I | intros r; exact I ]. }
  apply (H d_any (fun _ _ => eq_refl) (fun _ _ => eq_refl)) in Hi.
  apply inst_mono_eq in Hi. discriminate Hi.
Qed.
