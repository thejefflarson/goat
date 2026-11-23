(* Renaming the variable a binder opens with.  The cofinite binder rules of
   [typing] ask for a derivation at every fresh name; the algorithm derives it
   at the one name it chose, and this lemma carries it to all the others. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatTags.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Stdlib.Lists.List.
Import ListNotations.

Lemma uniq_rename_mid : forall G2 G1 x y (sc : scheme),
  uniq (G2 ++ (x ~ sc) ++ G1) -> y `notin` dom (G2 ++ (x ~ sc) ++ G1) ->
  uniq (G2 ++ (y ~ sc) ++ G1).
Proof.
  intros G2 G1 x y sc Hu Hy.
  assert (Hu' : uniq (G2 ++ G1)) by (eapply uniq_remove_mid; exact Hu).
  rewrite !dom_app in Hy. simpl in Hy.
  apply uniq_insert_mid; [exact Hu' | fsetdec | fsetdec].
Qed.

Lemma ftv_ctx_one : forall x (sc : scheme), ftv_ctx (x ~ sc) [=] ftv_sch sc.
Proof. intros. simpl. fsetdec. Qed.

Lemma frv_ctx_one : forall x (sc : scheme), frv_ctx (x ~ sc) [=] frv_sch sc.
Proof. intros. simpl. fsetdec. Qed.

Lemma ftv_ctx_swap_mid : forall G2 G1 x y (sc : scheme),
  ftv_ctx (G2 ++ (x ~ sc) ++ G1) [=] ftv_ctx (G2 ++ (y ~ sc) ++ G1).
Proof.
  intros. rewrite !ftv_ctx_app, (ftv_ctx_one x sc), (ftv_ctx_one y sc). fsetdec.
Qed.

Lemma gen_swap_mid : forall G2 G1 x y (sc : scheme) T k,
  sch_equiv (gen (G2 ++ (x ~ sc) ++ G1) T k) (gen (G2 ++ (y ~ sc) ++ G1) T k).
Proof.
  intros G2 G1 x y sc T k. unfold sch_equiv, gen. cbn [s_tq s_rq s_body s_sk].
  rewrite !ftv_ctx_app, !frv_ctx_app, (ftv_ctx_one x sc), (ftv_ctx_one y sc), (frv_ctx_one x sc), (frv_ctx_one y sc).
  split; [|split; [|split]]; [fsetdec | fsetdec | reflexivity | intros a Ha; reflexivity].
Qed.

Lemma gen_pin_swap_mid : forall Tm G2 G1 x y (sc : scheme) T k,
  sch_equiv (gen (pin_ctx Tm (G2 ++ (x ~ sc) ++ G1)) T k)
            (gen (pin_ctx Tm (G2 ++ (y ~ sc) ++ G1)) T k).
Proof.
  intros Tm G2 G1 x y sc T k.
  exact (gen_swap_mid ((pin_name ~ sch_mono Tm) ++ G2) G1 x y sc T k).
Qed.

Lemma binds_rename_mid : forall G2 G1 x y z (sc s : scheme),
  binds z s (G2 ++ (x ~ sc) ++ G1) -> uniq (G2 ++ (x ~ sc) ++ G1) ->
  (z = x /\ s = sc /\ binds y sc (G2 ++ (y ~ sc) ++ G1)) \/
  (z <> x /\ binds z s (G2 ++ (y ~ sc) ++ G1)).
Proof.
  intros G2 G1 x y z sc s Hb Hu.
  destruct (Atom.eq_dec z x) as [->|Hne].
  - left. split; [reflexivity|]. split.
    + eapply binds_mid_eq; eauto.
    + apply binds_app_3. apply binds_cons_2; reflexivity.
  - right. split; [exact Hne|].
    apply binds_weaken. eapply binds_remove_mid; eauto.
Qed.

Lemma lc_fvar_f : forall y, lc (e_fvar_f y).
Proof. intros; exact I. Qed.

Lemma typing_rename_var_mut : forall x y sc G1,
  (forall D Gm e T, typing D Gm e T -> forall G2,
     Gm = G2 ++ (x ~ sc) ++ G1 -> y `notin` dom Gm ->
     typing D (G2 ++ (y ~ sc) ++ G1) (subst_exp (e_fvar_f y) x e) T) /\
  (forall D Gm fs R, field_typing D Gm fs R -> forall G2,
     Gm = G2 ++ (x ~ sc) ++ G1 -> y `notin` dom Gm ->
     field_typing D (G2 ++ (y ~ sc) ++ G1) (subst_fields (e_fvar_f y) x fs) R).
Proof.
  intros x y sc G1.
  apply typing_field_mutind.
  - (* T_Var *)
    intros D G z s T Hu Hb Hi G2 Hg Hy. subst G.
    destruct (binds_rename_mid G2 G1 x y z sc s Hb Hu) as [[-> [-> Hb']]|[Hne Hb']].
    + rewrite subst_self. eapply T_Var; [ eapply uniq_rename_mid; eauto | exact Hb' | exact Hi ].
    + rewrite subst_neq by congruence.
      eapply T_Var; [ eapply uniq_rename_mid; eauto | exact Hb' | exact Hi ].
  - intros D G n T Hu Hs G2 Hg Hy. subst G. cbn [subst_exp]. apply T_Num; [ eapply uniq_rename_mid; eauto | exact Hs ].
  - intros D G d Hu G2 Hg Hy. subst G. cbn [subst_exp]. apply T_Dec. eapply uniq_rename_mid; eauto.
  - intros D G Hu G2 Hg Hy. subst G. cbn [subst_exp]. apply T_True. eapply uniq_rename_mid; eauto.
  - intros D G Hu G2 Hg Hy. subst G. cbn [subst_exp]. apply T_False. eapply uniq_rename_mid; eauto.
  - (* T_Abs *)
    intros L D G e T1 T2 Hb IH G2 Hg Hy. subst G. cbn [subst_exp].
    apply T_Abs with (L := L `union` {{x}} `union` {{y}}).
    intros z Hz.
    assert (Hzx : z <> x) by fsetdec.
    assert (HzL : z `notin` L) by fsetdec.
    assert (Hshape : (z ~ sch_mono T1) ++ G2 ++ (x ~ sc) ++ G1
                     = ((z ~ sch_mono T1) ++ G2) ++ (x ~ sc) ++ G1)
      by (rewrite <- app_assoc; reflexivity).
    assert (Hydom : y `notin` dom ((z ~ sch_mono T1) ++ G2 ++ (x ~ sc) ++ G1))
      by (simpl in *; fsetdec).
    pose proof (IH z HzL ((z ~ sch_mono T1) ++ G2) Hshape Hydom) as IH'.
    rewrite (subst_open_var e (e_fvar_f y) x z Hzx (lc_fvar_f y)) in IH'.
    rewrite <- app_assoc in IH'. exact IH'.
  - (* T_App *)
    intros D G e1 e2 T1 T2 H1 IH1 H2 IH2 G2 Hg Hy. subst G. cbn [subst_exp].
    eapply T_App; [ eapply IH1 | eapply IH2 ]; eauto.
  - (* T_Let *)
    intros L D G e1 e2 T1 T2 k Tm Hgv Hlp H1 IH1 Hb IH2 G2 Hg Hy. subst G. cbn [subst_exp].
    apply T_Let with (L := L `union` {{x}} `union` {{y}}) (T1 := T1) (k := k) (Tm := Tm).
    + apply is_gen_subst; [ reflexivity | exact Hgv ].
    + pose proof (ftv_ctx_swap_mid G2 G1 x y sc) as Hsw.
      intros Hc a Ha. apply (Hlp (let_open_subst _ _ _ Hc) a).
      rewrite !ftv_pin_ctx in *. fsetdec.
    + eapply typing_pw; [ eapply IH1; eauto | ].
      intros a. apply ext_set_eq. rewrite !ftv_pin_ctx, (ftv_ctx_swap_mid G2 G1 x y sc). reflexivity.
    + intros z Hz.
      assert (Hzx : z <> x) by fsetdec.
      assert (HzL : z `notin` L) by fsetdec.
      assert (Hshape : (z ~ gen (pin_ctx Tm (G2 ++ (x ~ sc) ++ G1)) T1 k) ++ G2 ++ (x ~ sc) ++ G1
                       = ((z ~ gen (pin_ctx Tm (G2 ++ (x ~ sc) ++ G1)) T1 k) ++ G2) ++ (x ~ sc) ++ G1)
        by (rewrite <- app_assoc; reflexivity).
      assert (Hydom : y `notin` dom ((z ~ gen (pin_ctx Tm (G2 ++ (x ~ sc) ++ G1)) T1 k) ++ G2 ++ (x ~ sc) ++ G1))
        by (simpl in *; fsetdec).
      pose proof (IH2 z HzL ((z ~ gen (pin_ctx Tm (G2 ++ (x ~ sc) ++ G1)) T1 k) ++ G2) Hshape Hydom) as IH'.
      rewrite (subst_open_var e2 (e_fvar_f y) x z Hzx (lc_fvar_f y)) in IH'.
      rewrite <- app_assoc in IH'.
      eapply typing_sch_equiv_ctx; [ exact IH' | ].
      apply ctx_equiv_cons; [ apply gen_pin_swap_mid | apply ctx_equiv_refl ].
  - (* T_LetMono *)
    intros L D G e1 e2 T1 T2 H1 IH1 Hb IH2 G2 Hg Hy. subst G. cbn [subst_exp].
    apply T_LetMono with (L := L `union` {{x}} `union` {{y}}) (T1 := T1).
    + eapply IH1; eauto.
    + intros z Hz.
      assert (Hzx : z <> x) by fsetdec.
      assert (HzL : z `notin` L) by fsetdec.
      assert (Hshape : (z ~ sch_mono T1) ++ G2 ++ (x ~ sc) ++ G1
                       = ((z ~ sch_mono T1) ++ G2) ++ (x ~ sc) ++ G1)
        by (rewrite <- app_assoc; reflexivity).
      assert (Hydom : y `notin` dom ((z ~ sch_mono T1) ++ G2 ++ (x ~ sc) ++ G1))
        by (simpl in *; fsetdec).
      pose proof (IH2 z HzL ((z ~ sch_mono T1) ++ G2) Hshape Hydom) as IH'.
      rewrite (subst_open_var e2 (e_fvar_f y) x z Hzx (lc_fvar_f y)) in IH'.
      rewrite <- app_assoc in IH'. exact IH'.
  - (* T_Letrec *)
    intros L D G fs e2 R T k Hfg Hf IHf Hb IH2 G2 Hg Hy. subst G. cbn [subst_exp].
    apply T_Letrec with (L := L `union` {{x}} `union` {{y}}) (R := R) (k := k).
    + apply fn_group_subst; exact Hfg.
    + intros z Hz.
      assert (Hzx : z <> x) by fsetdec.
      assert (HzL : z `notin` L) by fsetdec.
      assert (Hshape : (z ~ sch_mono (typ_Record R)) ++ G2 ++ (x ~ sc) ++ G1
                       = ((z ~ sch_mono (typ_Record R)) ++ G2) ++ (x ~ sc) ++ G1)
        by (rewrite <- app_assoc; reflexivity).
      assert (Hydom : y `notin` dom ((z ~ sch_mono (typ_Record R)) ++ G2 ++ (x ~ sc) ++ G1))
        by (simpl in *; fsetdec).
      pose proof (IHf z HzL ((z ~ sch_mono (typ_Record R)) ++ G2) Hshape Hydom) as IH'.
      rewrite (subst_open_fields_var fs (e_fvar_f y) x z Hzx (lc_fvar_f y)) in IH'.
      rewrite <- app_assoc in IH'.
      eapply field_typing_pw; [ exact IH' | ].
      intros a. apply ext_set_eq. rewrite (ftv_ctx_swap_mid G2 G1 x y sc). reflexivity.
    + intros z Hz.
      assert (Hzx : z <> x) by fsetdec.
      assert (HzL : z `notin` L) by fsetdec.
      assert (Hshape : (z ~ gen (G2 ++ (x ~ sc) ++ G1) (typ_Record R) k) ++ G2 ++ (x ~ sc) ++ G1
                       = ((z ~ gen (G2 ++ (x ~ sc) ++ G1) (typ_Record R) k) ++ G2) ++ (x ~ sc) ++ G1)
        by (rewrite <- app_assoc; reflexivity).
      assert (Hydom : y `notin` dom ((z ~ gen (G2 ++ (x ~ sc) ++ G1) (typ_Record R) k) ++ G2 ++ (x ~ sc) ++ G1))
        by (simpl in *; fsetdec).
      pose proof (IH2 z HzL ((z ~ gen (G2 ++ (x ~ sc) ++ G1) (typ_Record R) k) ++ G2) Hshape Hydom) as IH'.
      rewrite (subst_open_var e2 (e_fvar_f y) x z Hzx (lc_fvar_f y)) in IH'.
      rewrite <- app_assoc in IH'.
      eapply typing_sch_equiv_ctx; [ exact IH' | ].
      apply ctx_equiv_cons; [ apply gen_swap_mid | apply ctx_equiv_refl ].
  - (* T_Record *)
    intros D G fs R Hf IH Hnm G2 Hg Hy. subst G. cbn [subst_exp].
    apply T_Record; [ eapply IH; eauto | rewrite (no_meth_marks _ _ (marks_subst_fields fs (e_fvar_f y) x)); exact Hnm ].
  - (* T_Obj *)
    intros D G fs R Rt Hf IH Hms G2 Hg Hy. subst G. cbn [subst_exp].
    apply T_Obj with (Rt := Rt); [ eapply IH; eauto | eapply meths_shared_marks; [ exact Hms | symmetry; apply marks_subst_fields ] ].
  - (* T_Proj *)
    intros D G e l T R Ht IH G2 Hg Hy. subst G. cbn [subst_exp].
    eapply T_Proj. eapply IH; eauto.
  - (* T_Conv *)
    intros D G e T T' Ht IH Hteq G2 Hg Hy. subst G.
    eapply T_Conv; [ eapply IH; eauto | exact Hteq ].
  - intros D G Hu G2 Hg Hy. subst G. cbn [subst_exp]. apply T_Unit. eapply uniq_rename_mid; eauto.
  - intros D G q Hu G2 Hg Hy. subst G. cbn [subst_exp]. apply T_Str. eapply uniq_rename_mid; eauto.
  - (* T_If *)
    intros D G e1 e2 e3 T Ht1 IH1 Ht2 IH2 Ht3 IH3 G2 Hg Hy. subst G. cbn [subst_exp].
    apply T_If; [ eapply IH1 | eapply IH2 | eapply IH3 ]; eauto.
  - (* T_ToFloat *)
    intros D G e A Ht IH Hs G2 Hg Hy. subst G. cbn [subst_exp].
    eapply T_ToFloat; [ eapply IH; eauto | exact Hs ].
  - (* T_Bin *)
    intros D G e1 o e2 A B R Ht1 IH1 Ht2 IH2 Hs G2 Hg Hy. subst G. cbn [subst_exp].
    eapply T_Bin; [ eapply IH1 | eapply IH2 | exact Hs ]; eauto.
  - (* T_Spread *)
    intros D G e1 l e2 P T R Ht1 IH1 Ht2 IH2 G2 Hg Hy. subst G. cbn [subst_exp].
    eapply T_Spread; [ eapply IH1 | eapply IH2 ]; eauto.
  - (* T_Restrict *)
    intros D G e l R0 T R Ht IH Hrm G2 Hg Hy. subst G. cbn [subst_exp].
    eapply T_Restrict; [ eapply IH; eauto | exact Hrm ].
  - (* T_Fold *)
    intros D G e B Hlc Hgd Ht IH G2 Hg Hy. subst G. cbn [subst_exp].
    eapply T_Fold; [ exact Hlc | exact Hgd | eapply IH; eauto ].
  - (* T_Unfold *)
    intros D G e B Hlc Hgd Ht IH G2 Hg Hy. subst G. cbn [subst_exp].
    eapply T_Unfold; [ exact Hlc | exact Hgd | eapply IH; eauto ].
  - (* T_Con *)
    intros D G w tg e Ts Hlt Ht IH G2 Hg Hy. subst G. cbn [subst_exp].
    eapply T_Con; [ exact Hlt | eapply IH; eauto ].
  - (* T_Match *)
    intros L D G w Ts e ars T Ht IHe Hwf Harm IHarm Hdef IHdef G2 Hg Hy. subst G. cbn [subst_exp].
    apply T_Match with (L := L `union` {{x}} `union` {{y}}) (w := w) (Ts := Ts).
    + eapply IHe; eauto.
    + apply arms_wf_subst. exact Hwf.
    + intros tg b Hf z Hz.
      destruct (arms_find_subst_inv _ _ _ _ _ Hf) as [b0 [-> Hf0]].
      assert (Hzx : z <> x) by fsetdec.
      assert (HzL : z `notin` L) by fsetdec.
      assert (Hshape : (z ~ sch_mono (tag_payload w Ts tg)) ++ G2 ++ (x ~ sc) ++ G1
                       = ((z ~ sch_mono (tag_payload w Ts tg)) ++ G2) ++ (x ~ sc) ++ G1)
        by (rewrite <- app_assoc; reflexivity).
      assert (Hydom : y `notin` dom ((z ~ sch_mono (tag_payload w Ts tg)) ++ G2 ++ (x ~ sc) ++ G1))
        by (simpl in *; fsetdec).
      pose proof (IHarm tg b0 Hf0 z HzL ((z ~ sch_mono (tag_payload w Ts tg)) ++ G2) Hshape Hydom) as IH'.
      rewrite (subst_open_var b0 (e_fvar_f y) x z Hzx (lc_fvar_f y)) in IH'.
      rewrite <- app_assoc in IH'. exact IH'.
    + intros e0 Hd.
      destruct (arms_default_subst_inv _ _ _ _ Hd) as [e1 [-> Hd0]]. eapply IHdef; eauto.
  - intros D G Hu G2 Hg Hy. subst G. cbn [subst_fields]. apply FT_nil. eapply uniq_rename_mid; eauto.
  - intros D G l e T fs R Ht IH1 Hf IH2 G2 Hg Hy. subst G. cbn [subst_fields].
    eapply FT_cons; [ eapply IH1 | eapply IH2 ]; eauto.
  - intros D G l e T fs R Ht IH1 Hf IH2 G2 Hg Hy. subst G. cbn [subst_fields].
    eapply FT_meth; [ eapply IH1 | eapply IH2 ]; eauto.
Qed.

(* The form the algorithm uses: a derivation for the body opened at [x]
   carries over to the body opened at any other name fresh for the context. *)
Lemma typing_rename_var : forall D G x y sc e T,
  typing D ((x ~ sc) ++ G) (open_exp_wrt_exp e (e_fvar_f x)) T ->
  x `notin` fv_exp e -> y `notin` dom G -> y <> x ->
  typing D ((y ~ sc) ++ G) (open_exp_wrt_exp e (e_fvar_f y)) T.
Proof.
  intros D G x y sc e T Hty Hx Hy Hne.
  pose proof (proj1 (typing_rename_var_mut x y sc G) _ _ _ _ Hty nil eq_refl) as H.
  simpl in H. rewrite (subst_intro e x (e_fvar_f y) Hx).
  apply H. simpl. fsetdec.
Qed.
