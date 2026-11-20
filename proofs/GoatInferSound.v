(* Soundness of algorithm W (GoatInfer.v) against the declarative [typing]:
   every type the algorithm infers is derivable (ADR 0037, decision 2).

   Read the statement of [infer_sound] first.  The algorithm threads a
   substitution [s] and returns a type [T]; the theorem says that, once [s] is
   applied to the context, the term has type [T].  The side facts [OkS s] and
   [EvT T] are the even/odd bookkeeping of GoatInferSub.v that keeps
   substitutions off the quantified variables of schemes. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferTyp.
Require Import Goat.GoatInferRen.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferGen.
Require Import Goat.GoatInferRec.
Require Import Stdlib.Lists.List.
Import ListNotations.

Lemma lookup_binds : forall x G s, lookup x G = Some s -> binds x s G.
Proof.
  intros x G. induction G as [|[y sy] G IH]; intros s H; simpl in H; [discriminate|].
  destruct (Atom.eq_dec x y) as [->|Hne].
  - inversion H; subst. apply binds_cons_2; reflexivity.
  - apply binds_cons_3. apply IH. exact H.
Qed.

Lemma fresh_var_notin_dom : forall G e, fresh_var G e `notin` dom G.
Proof.
  intros G e. unfold fresh_var. intro H.
  apply (fresh_not_in (AtomSetImpl.elements (dom G `union` fv_exp e))).
  apply In_elements. fsetdec.
Qed.

Lemma fresh_var_notin_fv : forall G e, fresh_var G e `notin` fv_exp e.
Proof.
  intros G e. unfold fresh_var. intro H.
  apply (fresh_not_in (AtomSetImpl.elements (dom G `union` fv_exp e))).
  apply In_elements. fsetdec.
Qed.

Lemma apT_sid : forall T, apT sid T = T.
Proof. intros T. unfold apT, sid; simpl. apply ap_typ_pointwise_id; reflexivity. Qed.

Lemma apC_sid : forall G, apC sid G = G.
Proof.
  induction G as [|[x sc] G IH]; simpl; [reflexivity|].
  rewrite IH. destruct sc as [q r b]. unfold apS in *. cbn [s_tq s_rq s_body].
  rewrite apT_sid. reflexivity.
Qed.

Lemma EvT_Int : EvT typ_Int.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Lemma EvT_Bool : EvT typ_Bool.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Lemma EvT_Float : EvT typ_Float.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Lemma EvT_Unit : EvT typ_Unit.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Lemma EvT_String : EvT typ_String.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Definition ground (T : typ) : Prop :=
  T = typ_Int \/ T = typ_Float \/ T = typ_String \/ T = typ_Bool.

Lemma ground_ap : forall s T, ground T -> apT s T = T.
Proof. intros s T [H|[H|[H|H]]]; subst; reflexivity. Qed.

Lemma ground_EvT : forall T, ground T -> EvT T.
Proof.
  intros T [H|[H|[H|H]]]; subst;
    first [ apply EvT_Int | apply EvT_Float | apply EvT_String | apply EvT_Bool ].
Qed.

Lemma bin_arg_ground : forall o A B T, bin_arg o A B = Some T -> ground T.
Proof.
  intros o A B T H. unfold bin_arg in H.
  destruct (kind o); try (inversion H; subst; unfold ground; auto; fail);
    destruct B; destruct A; cbn in H; inversion H; subst; unfold ground; auto.
Qed.

Lemma bin_ty_sig : forall o T R, bin_ty o T = Some R -> bin_sig d_any o T T R.
Proof.
  intros o T R H. unfold bin_ty in H.
  destruct o; cbn in H; destruct T; try discriminate H;
    inversion H; subst;
    first [ (apply sig_ring; [ reflexivity | exact I ]) | apply sig_quot
          | apply sig_whole; reflexivity | (apply sig_cmp; [ reflexivity | constructor ]) ].
Qed.

Lemma ext_any : forall V a, ext d_any V (fun _ => k_Any) a = d_any a.
Proof. intros V a. unfold ext. destruct (AtomSetImpl.mem a V); reflexivity. Qed.

Lemma bin_ty_EvT : forall o T R, bin_ty o T = Some R -> EvT R.
Proof.
  intros o T R H. unfold bin_ty in H.
  destruct (kind o); destruct T; try discriminate H;
    inversion H; subst;
    first [ apply EvT_Int | apply EvT_Float | apply EvT_Bool ].
Qed.

Lemma typing_ap_Bool : forall s G e,
  OkS s -> WfCtx G -> typing d_any G e typ_Bool -> typing d_any (apC s G) e typ_Bool.
Proof. intros s G e Hs HG H. exact (typing_ap s G e typ_Bool Hs HG H). Qed.

Lemma EvT_arrow : forall A B, EvT A -> EvT B -> EvT (typ_Arrow A B).
Proof.
  intros A B [H1 H2] [H3 H4]. split; intros a Ha; simpl in Ha;
    apply AtomSetFacts.union_iff in Ha; destruct Ha as [Ha|Ha]; auto.
Qed.

Theorem infer_sound : forall f,
  (forall G e n s T n', infer f G e n = Some (s, T, n') -> WfCtx G ->
     OkS s /\ EvT T /\ typing d_any (apC s G) e T) /\
  (forall G fs n s R n', infer_fields f G fs n = Some (s, R, n') -> WfCtx G ->
     OkS s /\ EvR R /\ field_typing d_any (apC s G) fs R).
Proof.
  induction f as [|f IH]; [ split; intros; discriminate | ].
  destruct IH as [IHe IHf]. split.
  - intros G e n s T n' H HG. cbn [infer] in H.
    destruct e as [i | x | k | d | | | b | e1 e2 | e1 e2 | fl el | fs | e1 l | | q | c0 a0 b0 | a1 o a2 | a3 | a4 | a5];
      try discriminate H.
    + (* variable *)
      destruct (lookup x G) as [sc|] eqn:Hl; [|discriminate].
      destruct (instantiate sc n) as [T0 n1] eqn:Hi. inversion H; try subst s; try subst T; try subst n'; clear H.
      pose proof (lookup_binds _ _ _ Hl) as Hb.
      destruct (instantiate_sound _ _ _ _ Hi ((proj2 HG) _ _ Hb)) as [Hinst Hev].
      split; [apply OkS_id|]. split; [exact Hev|].
      rewrite apC_sid. eapply T_Var; [ exact (proj1 HG) | exact Hb | exact Hinst ].
    + inversion H; try subst s; try subst T; try subst n'; clear H.
      split; [apply OkS_id|]. split; [apply EvT_Int|].
      apply T_Num; [ apply uniq_apC; exact (proj1 HG) | exact I ].
    + inversion H; try subst s; try subst T; try subst n'; clear H.
      split; [apply OkS_id|]. split; [apply EvT_Float|].
      apply T_Dec. apply uniq_apC. exact (proj1 HG).
    + inversion H; try subst s; try subst T; try subst n'; clear H.
      split; [apply OkS_id|]. split; [apply EvT_Bool|].
      apply T_True. apply uniq_apC. exact (proj1 HG).
    + inversion H; try subst s; try subst T; try subst n'; clear H.
      split; [apply OkS_id|]. split; [apply EvT_Bool|].
      apply T_False. apply uniq_apC. exact (proj1 HG).
    + (* abstraction *)
      destruct (infer f ((fresh_var G b ~ sch_mono (typ_Var (ea n))) ++ G)
                  (open_exp_wrt_exp b (e_fvar_f (fresh_var G b))) (S n))
        as [[[s0 T0] n0]|] eqn:Ei; [|discriminate].
      inversion H; try subst s; try subst T; try subst n'; clear H.
      assert (Hbeta : EvT (typ_Var (ea n))) by (apply EvT_var, ev_ea).
      assert (Hwf : WfCtx ((fresh_var G b ~ sch_mono (typ_Var (ea n))) ++ G))
        by (apply WfCtx_cons; [ exact HG | apply fresh_var_notin_dom | apply WfSch_mono; exact Hbeta ]).
      destruct (IHe _ _ _ _ _ _ Ei Hwf) as (Hs0 & HT0 & Hty).
      split; [exact Hs0|]. split.
      { apply EvT_arrow; [ apply EvT_ap; auto | exact HT0 ]. }
      rewrite apC_app, apC_single in Hty.
      apply T_Abs with (L := dom G `union` {{fresh_var G b}}).
      intros y Hy.
      assert (Hdom : y `notin` dom (apC s0 G)) by (rewrite dom_apC; fsetdec).
      apply (typing_rename_var d_any (apC s0 G) (fresh_var G b) y).
      * exact Hty.
      * apply fresh_var_notin_fv.
      * exact Hdom.
      * fsetdec.
    + (* application *)
      destruct (infer f G e1 n) as [[[s1 T1] n1]|] eqn:E1; [|discriminate].
      destruct (infer f (apC s1 G) e2 n1) as [[[s2 T2] n2]|] eqn:E2; [|discriminate].
      destruct (unify_t f (apT s2 T1) (typ_Arrow T2 (typ_Var (ea n2))) (S n2))
        as [[s3 n3]|] eqn:E3; [|discriminate].
      inversion H; try subst s; try subst T; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ E1 HG) as (Hs1 & HT1 & Hty1).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHe _ _ _ _ _ _ E2 HG1) as (Hs2 & HT2 & Hty2).
      pose proof (WfCtx_ap s2 _ Hs2 HG1) as HG2.
      assert (Hbeta : EvT (typ_Var (ea n2))) by (apply EvT_var, ev_ea).
      destruct ((proj1 (unify_sound f)) _ _ _ _ _ E3 (EvT_ap s2 T1 Hs2 HT1)
                  (EvT_arrow _ _ HT2 Hbeta)) as [Hs3 Hteq].
      split; [ apply OkS_comp; [exact Hs3 | apply OkS_comp; auto] | ].
      split; [ apply EvT_ap; auto | ].
      rewrite <- !apC_comp.
      eapply T_App.
      * eapply T_Conv; [ | exact Hteq ].
        apply (typing_ap s3 _ _ _ Hs3 HG2).
        apply (typing_ap s2 _ _ _ Hs2 HG1). exact Hty1.
      * apply (typing_ap s3 _ _ _ Hs3 HG2). exact Hty2.
    + (* let *)
      destruct (is_gen_value e1) eqn:Hgv.
      2: { (* a computed value: monomorphic *)
      destruct (infer f G e1 n) as [[[s1 T1] n1]|] eqn:E1; [|discriminate].
      destruct (infer f ((fresh_var (apC s1 G) e2 ~ sch_mono T1) ++ apC s1 G)
                  (open_exp_wrt_exp e2 (e_fvar_f (fresh_var (apC s1 G) e2))) n1)
        as [[[s2 T2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst T; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ E1 HG) as (Hs1 & HT1 & Hty1).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      assert (Hwf : WfCtx ((fresh_var (apC s1 G) e2 ~ sch_mono T1) ++ apC s1 G))
        by (apply WfCtx_cons; [ exact HG1 | apply fresh_var_notin_dom | apply WfSch_mono; exact HT1 ]).
      destruct (IHe _ _ _ _ _ _ E2 Hwf) as (Hs2 & HT2 & Hty2).
      split; [ apply OkS_comp; auto | ]. split; [ exact HT2 | ].
      rewrite <- apC_comp.
      rewrite apC_app, apC_single in Hty2.
      apply T_LetMono with (L := dom G `union` {{fresh_var (apC s1 G) e2}}) (T1 := apT s2 T1).
      * apply (typing_ap s2 _ _ _ Hs2 HG1). exact Hty1.
      * intros y Hy.
        assert (Hdom : y `notin` dom (apC s2 (apC s1 G)))
          by (rewrite dom_apC, dom_apC; fsetdec).
        exact (typing_rename_var d_any (apC s2 (apC s1 G)) (fresh_var (apC s1 G) e2) y
                 (apS s2 (sch_mono T1)) e2 T2 Hty2
                 (fresh_var_notin_fv _ _) Hdom ltac:(fsetdec)). }
      destruct (infer f G e1 n) as [[[s1 T1] n1]|] eqn:E1; [|discriminate].
      destruct (infer f ((fresh_var (apC s1 G) e2 ~ gen_ren (apC s1 G) T1) ++ apC s1 G)
                  (open_exp_wrt_exp e2 (e_fvar_f (fresh_var (apC s1 G) e2))) n1)
        as [[[s2 T2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst T; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ E1 HG) as (Hs1 & HT1 & Hty1).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      pose proof (gen_ren_wf (apC s1 G) T1 HT1) as Hwsc.
      assert (Hwf : WfCtx ((fresh_var (apC s1 G) e2 ~ gen_ren (apC s1 G) T1) ++ apC s1 G))
        by (apply WfCtx_cons; [ exact HG1 | apply fresh_var_notin_dom | exact Hwsc ]).
      destruct (IHe _ _ _ _ _ _ E2 Hwf) as (Hs2 & HT2 & Hty2).
      split; [ apply OkS_comp; auto | ]. split; [ exact HT2 | ].
      rewrite <- apC_comp.
      rewrite apC_app, apC_single in Hty2.
      apply T_Let with (L := dom G `union` {{fresh_var (apC s1 G) e2}})
                       (T1 := apT s2 (s_body (gen_ren (apC s1 G) T1))) (k := fun _ => k_Any).
      * exact Hgv.
      * eapply typing_pw; [ | intros a; symmetry; apply ext_any ].
        apply (typing_ap s2 _ _ _ Hs2 HG1).
        apply typing_gen_ren. exact Hty1.
      * intros y Hy.
        assert (Hdom : y `notin` dom (apC s2 (apC s1 G)))
          by (rewrite dom_apC, dom_apC; fsetdec).
        pose proof (typing_rename_var d_any (apC s2 (apC s1 G)) (fresh_var (apC s1 G) e2) y
                      (apS s2 (gen_ren (apC s1 G) T1)) e2 T2 Hty2
                      (fresh_var_notin_fv _ _) Hdom ltac:(fsetdec)) as Hren.
        eapply typing_sch_equiv_ctx; [ exact Hren | ].
        apply ctx_equiv_cons; [ | apply ctx_equiv_refl ].
        apply gen_ren_equiv; auto.
    + (* recursive group *)
      destruct (is_fn_group fl) eqn:Hfg; [|discriminate].
      set (p := fresh_var G (e_rec fl)) in *.
      set (R0 := group_row fl n) in *.
      destruct (infer_fields f ((p ~ sch_mono (typ_Record R0)) ++ G)
                  (open_fields_wrt_exp fl (e_fvar_f p)) (n + nfields fl))
        as [[[s1 R1] n1]|] eqn:E1; [|discriminate].
      destruct (unify_pw f R1 (apR s1 R0) n1) as [[s2 n2]|] eqn:E2; [|discriminate].
      set (G1 := apC (scomp s2 s1) G) in *.
      set (Rf := apR (scomp s2 s1) R0) in *.
      set (q := fresh_var G1 el) in *.
      destruct (infer f ((q ~ gen_ren G1 (typ_Record Rf)) ++ G1)
                  (open_exp_wrt_exp el (e_fvar_f q)) n2)
        as [[[s3 T3] n3]|] eqn:E3; [|discriminate].
      inversion H; try subst s; try subst T; try subst n'; clear H.
      assert (HR0 : EvR R0) by apply EvR_group_row.
      assert (Hwf0 : WfCtx ((p ~ sch_mono (typ_Record R0)) ++ G))
        by (apply WfCtx_cons; [ exact HG | apply fresh_var_notin_dom | apply WfSch_mono, EvT_Record; exact HR0 ]).
      destruct (IHf _ _ _ _ _ _ E1 Hwf0) as (Hs1 & HR1 & Hty1).
      rewrite apC_app, apC_single in Hty1.
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      pose proof (EvR_ap s1 _ Hs1 HR0) as HR0'.
      destruct (unify_pw_sound f _ _ _ _ _ E2 HR1 HR0') as [Hs2 Hpw].
      pose proof (fields_ap s2 _ _ _ _ _ Hs2 HG1 Hty1) as Hty2.
      assert (Hs21 : OkS (scomp s2 s1)) by (apply OkS_comp; assumption).
      assert (HRf : EvR Rf) by (apply EvR_ap; assumption).
      assert (HG21 : WfCtx G1) by (apply WfCtx_ap; assumption).
      assert (Hty3 : field_typing d_any ((p ~ sch_mono (typ_Record Rf)) ++ G1)
                       (open_fields_wrt_exp fl (e_fvar_f p)) Rf).
      { unfold Rf, G1. rewrite <- apR_comp. rewrite <- apC_comp.
        apply pw_conv with (R := apR s2 R1); [ | exact Hpw ].
        change (typ_Record (apR s2 (apR s1 R0))) with (apT s2 (apT s1 (typ_Record R0))) in Hty2.
        exact Hty2. }
      pose proof (gen_ren_wf G1 (typ_Record Rf) (proj2 (EvT_Record _) HRf)) as Hwsc.
      assert (Hwf1 : WfCtx ((q ~ gen_ren G1 (typ_Record Rf)) ++ G1))
        by (apply WfCtx_cons; [ exact HG21 | apply fresh_var_notin_dom | exact Hwsc ]).
      destruct (IHe _ _ _ _ _ _ E3 Hwf1) as (Hs3 & HT3 & Hty4).
      split; [ apply OkS_comp; assumption | ]. split; [ exact HT3 | ].
      rewrite <- apC_comp. fold G1.
      rewrite apC_app, apC_single in Hty4.
      pose proof (fields_gen_ren G1 p Rf _ Hty3) as Hty5.
      pose proof (fields_ap s3 _ _ _ _ _ Hs3 HG21 Hty5) as Hty6.
      apply T_Letrec with (L := dom G `union` {{p}} `union` {{q}})
        (R := apR s3 (ap_row (rename_t (gen_vars_t G1 (typ_Record Rf)))
                             (rename_r (gen_vars_r G1 (typ_Record Rf))) Rf))
        (k := fun _ => k_Any).
      * apply is_fn_group_sound. exact Hfg.
      * intros y Hy.
        assert (Hdom : y `notin` dom (apC s3 G1)) by (rewrite dom_apC; unfold G1; rewrite dom_apC; fsetdec).
        eapply field_typing_pw; [ | intros a; symmetry; apply ext_any ].
        apply (fields_rename_var (apC s3 G1) p y).
        -- exact Hty6.
        -- apply fresh_var_notin_fv.
        -- exact Hdom.
        -- fsetdec.
      * intros y Hy.
        assert (Hdom : y `notin` dom (apC s3 G1)) by (rewrite dom_apC; unfold G1; rewrite dom_apC; fsetdec).
        pose proof (typing_rename_var d_any (apC s3 G1) q y
                      (apS s3 (gen_ren G1 (typ_Record Rf))) el T3 Hty4
                      (fresh_var_notin_fv _ _) Hdom ltac:(fsetdec)) as Hren.
        eapply typing_sch_equiv_ctx; [ exact Hren | ].
        apply ctx_equiv_cons; [ | apply ctx_equiv_refl ].
        exact (gen_ren_equiv G1 (typ_Record Rf) s3 Hs3 HG21 (proj2 (EvT_Record _) HRf)).
    + (* record *)
      destruct (infer_fields f G fs n) as [[[s0 R0] n0]|] eqn:Ei; [|discriminate].
      inversion H; try subst s; try subst T; try subst n'; clear H.
      destruct (IHf _ _ _ _ _ _ Ei HG) as (Hs0 & HR0 & Hty).
      split; [exact Hs0|]. split; [ apply EvT_Record; exact HR0 | ].
      apply T_Record. exact Hty.
    + (* projection *)
      destruct (infer f G e1 n) as [[[s1 T1] n1]|] eqn:E1; [|discriminate].
      destruct (unify_t f T1 (typ_Record (row_Ext l (typ_Var (ea n1)) (row_Var (ea (S n1)))))
                  (n1 + 2)) as [[s2 n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst T; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ E1 HG) as (Hs1 & HT1 & Hty1).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      assert (Hrow : EvT (typ_Record (row_Ext l (typ_Var (ea n1)) (row_Var (ea (S n1)))))).
      { apply EvT_Record, EvR_ext; [ apply EvT_var, ev_ea | apply EvR_var, ev_ea ]. }
      destruct ((proj1 (unify_sound f)) _ _ _ _ _ E2 HT1 Hrow) as [Hs2 Hteq].
      split; [ apply OkS_comp; auto | ].
      split; [ apply EvT_ap; [exact Hs2 | apply EvT_var, ev_ea] | ].
      rewrite <- apC_comp.
      eapply T_Proj.
      eapply T_Conv; [ | exact Hteq ].
      apply (typing_ap s2 _ _ _ Hs2 HG1). exact Hty1.
    + inversion H; try subst s; try subst T; try subst n'; clear H.
      split; [apply OkS_id|]. split; [apply EvT_Unit|].
      apply T_Unit. apply uniq_apC. exact (proj1 HG).
    + inversion H; try subst s; try subst T; try subst n'; clear H.
      split; [apply OkS_id|]. split; [apply EvT_String|].
      apply T_Str. apply uniq_apC. exact (proj1 HG).
    + (* conditional *)
      destruct (infer f G c0 n) as [[[s1 T1] n1]|] eqn:E1; [|discriminate].
      destruct (unify_t f T1 typ_Bool n1) as [[s2 n2]|] eqn:E2; [|discriminate].
      destruct (infer f (apC s2 (apC s1 G)) a0 n2) as [[[s3 T2] n3]|] eqn:E3; [|discriminate].
      destruct (infer f (apC s3 (apC s2 (apC s1 G))) b0 n3) as [[[s4 T3] n4]|] eqn:E4;
        [|discriminate].
      destruct (unify_t f (apT s4 T2) T3 n4) as [[s5 n5]|] eqn:E5; [|discriminate].
      inversion H; try subst s; try subst T; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ E1 HG) as (Hs1 & HT1 & Hty1).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct ((proj1 (unify_sound f)) _ _ _ _ _ E2 HT1 EvT_Bool) as [Hs2 Hteq2].
      pose proof (WfCtx_ap s2 _ Hs2 HG1) as HG2.
      destruct (IHe _ _ _ _ _ _ E3 HG2) as (Hs3 & HT2 & Hty2).
      pose proof (WfCtx_ap s3 _ Hs3 HG2) as HG3.
      destruct (IHe _ _ _ _ _ _ E4 HG3) as (Hs4 & HT3 & Hty3).
      pose proof (WfCtx_ap s4 _ Hs4 HG3) as HG4.
      destruct ((proj1 (unify_sound f)) _ _ _ _ _ E5 (EvT_ap s4 T2 Hs4 HT2) HT3)
        as [Hs5 Hteq5].
      pose proof (WfCtx_ap s5 _ Hs5 HG4) as HG5.
      split; [ repeat (apply OkS_comp; [ assumption | ]); assumption | ].
      split; [ apply EvT_ap; auto | ].
      rewrite <- !apC_comp.
      assert (Hc : typing d_any (apC s2 (apC s1 G)) c0 typ_Bool).
      { eapply T_Conv; [ | exact Hteq2 ].
        apply (typing_ap s2 _ _ _ Hs2 HG1). exact Hty1. }
      eapply T_If.
      * exact (typing_ap_Bool s5 _ _ Hs5 HG4
                 (typing_ap_Bool s4 _ _ Hs4 HG3 (typing_ap_Bool s3 _ _ Hs3 HG2 Hc))).
      * eapply T_Conv; [ | exact Hteq5 ].
        apply (typing_ap s5 _ _ _ Hs5 HG4).
        apply (typing_ap s4 _ _ _ Hs4 HG3). exact Hty2.
      * apply (typing_ap s5 _ _ _ Hs5 HG4). exact Hty3.
    + (* binary operation *)
      destruct (infer f G a1 n) as [[[s1 T1] n1]|] eqn:E1; [|discriminate].
      destruct (infer f (apC s1 G) a2 n1) as [[[s2 T2] n2]|] eqn:E2; [|discriminate].
      destruct (bin_arg o (apT s2 T1) T2) as [Ta|] eqn:E3; [|discriminate].
      destruct (unify_t f (apT s2 T1) Ta n2) as [[s3 n3]|] eqn:E4; [|discriminate].
      destruct (unify_t f (apT s3 T2) Ta n3) as [[s4 n4]|] eqn:E5; [|discriminate].
      destruct (bin_ty o Ta) as [R|] eqn:E6; [|discriminate].
      inversion H; try subst s; try subst T; try subst n'; clear H.
      pose proof (bin_arg_ground _ _ _ _ E3) as Hg.
      pose proof (ground_EvT _ Hg) as HTa.
      destruct (IHe _ _ _ _ _ _ E1 HG) as (Hs1 & HT1 & Hty1).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHe _ _ _ _ _ _ E2 HG1) as (Hs2 & HT2 & Hty2).
      pose proof (WfCtx_ap s2 _ Hs2 HG1) as HG2.
      destruct ((proj1 (unify_sound f)) _ _ _ _ _ E4 (EvT_ap s2 T1 Hs2 HT1) HTa)
        as [Hs3 Hteq3].
      pose proof (WfCtx_ap s3 _ Hs3 HG2) as HG3.
      destruct ((proj1 (unify_sound f)) _ _ _ _ _ E5 (EvT_ap s3 T2 Hs3 HT2) HTa)
        as [Hs4 Hteq4].
      pose proof (WfCtx_ap s4 _ Hs4 HG3) as HG4.
      rewrite (ground_ap s3 _ Hg) in Hteq3.
      rewrite (ground_ap s4 _ Hg) in Hteq4.
      split; [ repeat (apply OkS_comp; [ assumption | ]); assumption | ].
      split; [ exact (bin_ty_EvT _ _ _ E6) | ].
      rewrite <- !apC_comp.
      eapply T_Bin; [ | | exact (bin_ty_sig _ _ _ E6) ].
      * pose proof (teq_apT s4 _ _ Hteq3) as Hteq3'.
        rewrite (ground_ap s4 _ Hg) in Hteq3'.
        eapply T_Conv; [ | exact Hteq3' ].
        apply (typing_ap s4 _ _ _ Hs4 HG3).
        apply (typing_ap s3 _ _ _ Hs3 HG2).
        apply (typing_ap s2 _ _ _ Hs2 HG1). exact Hty1.
      * eapply T_Conv; [ | exact Hteq4 ].
        apply (typing_ap s4 _ _ _ Hs4 HG3).
        apply (typing_ap s3 _ _ _ Hs3 HG2). exact Hty2.
    + (* Int-to-Float coercion *)
      destruct (infer f G a3 n) as [[[s1 T1] n1]|] eqn:E1; [|discriminate].
      destruct (unify_t f T1 typ_Int n1) as [[s2 n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst T; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ E1 HG) as (Hs1 & HT1 & Hty1).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct ((proj1 (unify_sound f)) _ _ _ _ _ E2 HT1 EvT_Int) as [Hs2 Hteq].
      split; [ apply OkS_comp; auto | ]. split; [ apply EvT_Float | ].
      rewrite <- apC_comp.
      apply T_ToFloat with (A := typ_Int); [ | exact I ].
      eapply T_Conv; [ | exact Hteq ].
      apply (typing_ap s2 _ _ _ Hs2 HG1). exact Hty1.
  - intros G fs n s R n' H HG. cbn [infer_fields] in H.
    destruct fs as [| l e rest]; try discriminate H.
    + inversion H; try subst s; try subst R; try subst n'; clear H.
      split; [apply OkS_id|]. split; [apply EvR_Empty|].
      apply FT_nil. apply uniq_apC. exact (proj1 HG).
    + destruct (infer f G e n) as [[[s1 T1] n1]|] eqn:E1; [|discriminate].
      destruct (infer_fields f (apC s1 G) rest n1) as [[[s2 R2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst R; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ E1 HG) as (Hs1 & HT1 & Hty1).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHf _ _ _ _ _ _ E2 HG1) as (Hs2 & HR2 & Hty2).
      split; [ apply OkS_comp; auto | ].
      split; [ apply EvR_ext; [ apply EvT_ap; auto | exact HR2 ] | ].
      rewrite <- apC_comp.
      eapply FT_cons.
      * apply (typing_ap s2 _ _ _ Hs2 HG1). exact Hty1.
      * exact Hty2.
Qed.

(* The statement for programs: a closed term the algorithm accepts has the
   type it returns. *)
Theorem infer_closed_sound : forall fuel e T,
  infer_closed fuel e = Some T -> typing d_any nil e T.
Proof.
  intros fuel e T H. unfold infer_closed in H.
  destruct (infer fuel nil e 0) as [[[s T0] n]|] eqn:Ei; [|discriminate].
  inversion H; try subst s; try subst T; try subst n'; clear H.
  assert (Hwf : WfCtx nil) by (split; [constructor | intros x sc Hb; inversion Hb]).
  destruct ((proj1 (infer_sound fuel)) _ _ _ _ _ _ Ei Hwf) as (_ & _ & Hty).
  exact Hty.
Qed.
