(* Renaming the variable a binder opens with.  The cofinite binder rules of
   [typing] ask for a derivation at every fresh name; the algorithm derives it
   at the one name it chose, and this lemma carries it to all the others. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
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

Lemma gen_swap_mid : forall G2 G1 x y (sc : scheme) T,
  sch_equiv (gen (G2 ++ (x ~ sc) ++ G1) T) (gen (G2 ++ (y ~ sc) ++ G1) T).
Proof.
  intros G2 G1 x y sc T. unfold sch_equiv, gen. cbn [s_tq s_rq s_body].
  rewrite !ftv_ctx_app, !frv_ctx_app, (ftv_ctx_one x sc), (ftv_ctx_one y sc), (frv_ctx_one x sc), (frv_ctx_one y sc).
  split; [|split]; [fsetdec | fsetdec | reflexivity].
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
  (forall Gm e T, typing Gm e T -> forall G2,
     Gm = G2 ++ (x ~ sc) ++ G1 -> y `notin` dom Gm ->
     typing (G2 ++ (y ~ sc) ++ G1) (subst_exp (e_fvar_f y) x e) T) /\
  (forall Gm fs R, field_typing Gm fs R -> forall G2,
     Gm = G2 ++ (x ~ sc) ++ G1 -> y `notin` dom Gm ->
     field_typing (G2 ++ (y ~ sc) ++ G1) (subst_fields (e_fvar_f y) x fs) R).
Proof.
  intros x y sc G1.
  apply typing_field_mutind.
  - (* T_Var *)
    intros G z s T Hu Hb Hi G2 Hg Hy. subst G.
    destruct (binds_rename_mid G2 G1 x y z sc s Hb Hu) as [[-> [-> Hb']]|[Hne Hb']].
    + rewrite subst_self. eapply T_Var; [ eapply uniq_rename_mid; eauto | exact Hb' | exact Hi ].
    + rewrite subst_neq by congruence.
      eapply T_Var; [ eapply uniq_rename_mid; eauto | exact Hb' | exact Hi ].
  - intros G n Hu G2 Hg Hy. subst G. cbn [subst_exp]. apply T_Num. eapply uniq_rename_mid; eauto.
  - intros G d Hu G2 Hg Hy. subst G. cbn [subst_exp]. apply T_Dec. eapply uniq_rename_mid; eauto.
  - intros G Hu G2 Hg Hy. subst G. cbn [subst_exp]. apply T_True. eapply uniq_rename_mid; eauto.
  - intros G Hu G2 Hg Hy. subst G. cbn [subst_exp]. apply T_False. eapply uniq_rename_mid; eauto.
  - (* T_Abs *)
    intros L G e T1 T2 Hb IH G2 Hg Hy. subst G. cbn [subst_exp].
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
    intros G e1 e2 T1 T2 H1 IH1 H2 IH2 G2 Hg Hy. subst G. cbn [subst_exp].
    eapply T_App; [ eapply IH1 | eapply IH2 ]; eauto.
  - (* T_Let *)
    intros L G e1 e2 T1 T2 H1 IH1 Hb IH2 G2 Hg Hy. subst G. cbn [subst_exp].
    apply T_Let with (L := L `union` {{x}} `union` {{y}}) (T1 := T1).
    + eapply IH1; eauto.
    + intros z Hz.
      assert (Hzx : z <> x) by fsetdec.
      assert (HzL : z `notin` L) by fsetdec.
      assert (Hshape : (z ~ gen (G2 ++ (x ~ sc) ++ G1) T1) ++ G2 ++ (x ~ sc) ++ G1
                       = ((z ~ gen (G2 ++ (x ~ sc) ++ G1) T1) ++ G2) ++ (x ~ sc) ++ G1)
        by (rewrite <- app_assoc; reflexivity).
      assert (Hydom : y `notin` dom ((z ~ gen (G2 ++ (x ~ sc) ++ G1) T1) ++ G2 ++ (x ~ sc) ++ G1))
        by (simpl in *; fsetdec).
      pose proof (IH2 z HzL ((z ~ gen (G2 ++ (x ~ sc) ++ G1) T1) ++ G2) Hshape Hydom) as IH'.
      rewrite (subst_open_var e2 (e_fvar_f y) x z Hzx (lc_fvar_f y)) in IH'.
      rewrite <- app_assoc in IH'.
      eapply typing_sch_equiv_ctx; [ exact IH' | ].
      apply ctx_equiv_cons; [ apply gen_swap_mid | apply ctx_equiv_refl ].
  - (* T_Record *)
    intros G fs R Hf IH G2 Hg Hy. subst G. cbn [subst_exp].
    apply T_Record. eapply IH; eauto.
  - (* T_Proj *)
    intros G e l T R Ht IH G2 Hg Hy. subst G. cbn [subst_exp].
    eapply T_Proj. eapply IH; eauto.
  - (* T_Conv *)
    intros G e T T' Ht IH Hteq G2 Hg Hy. subst G.
    eapply T_Conv; [ eapply IH; eauto | exact Hteq ].
  - intros G Hu G2 Hg Hy. subst G. cbn [subst_exp]. apply T_Unit. eapply uniq_rename_mid; eauto.
  - intros G q Hu G2 Hg Hy. subst G. cbn [subst_exp]. apply T_Str. eapply uniq_rename_mid; eauto.
  - (* T_If *)
    intros G e1 e2 e3 T Ht1 IH1 Ht2 IH2 Ht3 IH3 G2 Hg Hy. subst G. cbn [subst_exp].
    apply T_If; [ eapply IH1 | eapply IH2 | eapply IH3 ]; eauto.
  - (* T_ToFloat *)
    intros G e Ht IH G2 Hg Hy. subst G. cbn [subst_exp].
    apply T_ToFloat. eapply IH; eauto.
  - (* T_Bin *)
    intros G e1 o e2 A B R Ht1 IH1 Ht2 IH2 Hs G2 Hg Hy. subst G. cbn [subst_exp].
    eapply T_Bin; [ eapply IH1 | eapply IH2 | exact Hs ]; eauto.
  - intros G Hu G2 Hg Hy. subst G. cbn [subst_fields]. apply FT_nil. eapply uniq_rename_mid; eauto.
  - intros G l e T fs R Ht IH1 Hf IH2 G2 Hg Hy. subst G. cbn [subst_fields].
    eapply FT_cons; [ eapply IH1 | eapply IH2 ]; eauto.
Qed.

(* The form the algorithm uses: a derivation for the body opened at [x]
   carries over to the body opened at any other name fresh for the context. *)
Lemma typing_rename_var : forall G x y sc e T,
  typing ((x ~ sc) ++ G) (open_exp_wrt_exp e (e_fvar_f x)) T ->
  x `notin` fv_exp e -> y `notin` dom G -> y <> x ->
  typing ((y ~ sc) ++ G) (open_exp_wrt_exp e (e_fvar_f y)) T.
Proof.
  intros G x y sc e T Hty Hx Hy Hne.
  pose proof (proj1 (typing_rename_var_mut x y sc G) _ _ _ Hty nil eq_refl) as H.
  simpl in H. rewrite (subst_intro e x (e_fvar_f y) Hx).
  apply H. simpl. fsetdec.
Qed.
