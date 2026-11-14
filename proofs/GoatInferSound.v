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

Lemma EvT_Number : EvT typ_Number.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Lemma EvT_Bool : EvT typ_Bool.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Lemma EvR_Empty : EvR row_Empty.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Lemma EvT_arrow : forall A B, EvT A -> EvT B -> EvT (typ_Arrow A B).
Proof.
  intros A B [H1 H2] [H3 H4]. split; intros a Ha; simpl in Ha;
    apply AtomSetFacts.union_iff in Ha; destruct Ha as [Ha|Ha]; auto.
Qed.

Theorem infer_sound : forall f,
  (forall G e n s T n', infer f G e n = Some (s, T, n') -> WfCtx G ->
     OkS s /\ EvT T /\ typing (apC s G) e T) /\
  (forall G fs n s R n', infer_fields f G fs n = Some (s, R, n') -> WfCtx G ->
     OkS s /\ EvR R /\ field_typing (apC s G) fs R).
Proof.
  induction f as [|f IH]; [ split; intros; discriminate | ].
  destruct IH as [IHe IHf]. split.
  - intros G e n s T n' H HG. cbn [infer] in H.
    destruct e as [i | x | k | | | b | e1 e2 | e1 e2 | fs | e1 l]; try discriminate H.
    + (* variable *)
      destruct (lookup x G) as [sc|] eqn:Hl; [|discriminate].
      destruct (instantiate sc n) as [T0 n1] eqn:Hi. inversion H; try subst s; try subst T; try subst n'; clear H.
      pose proof (lookup_binds _ _ _ Hl) as Hb.
      destruct (instantiate_sound _ _ _ _ Hi ((proj2 HG) _ _ Hb)) as [Hinst Hev].
      split; [apply OkS_id|]. split; [exact Hev|].
      rewrite apC_sid. eapply T_Var; [ exact (proj1 HG) | exact Hb | exact Hinst ].
    + inversion H; try subst s; try subst T; try subst n'; clear H.
      split; [apply OkS_id|]. split; [apply EvT_Number|].
      apply T_Num. apply uniq_apC. exact (proj1 HG).
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
      apply (typing_rename_var (apC s0 G) (fresh_var G b) y).
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
                       (T1 := apT s2 (s_body (gen_ren (apC s1 G) T1))).
      * apply (typing_ap s2 _ _ _ Hs2 HG1).
        apply typing_gen_ren. exact Hty1.
      * intros y Hy.
        assert (Hdom : y `notin` dom (apC s2 (apC s1 G)))
          by (rewrite dom_apC, dom_apC; fsetdec).
        pose proof (typing_rename_var (apC s2 (apC s1 G)) (fresh_var (apC s1 G) e2) y
                      (apS s2 (gen_ren (apC s1 G) T1)) e2 T2 Hty2
                      (fresh_var_notin_fv _ _) Hdom ltac:(fsetdec)) as Hren.
        eapply typing_sch_equiv_ctx; [ exact Hren | ].
        apply ctx_equiv_cons; [ | apply ctx_equiv_refl ].
        apply gen_ren_equiv; auto.
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
  infer_closed fuel e = Some T -> typing nil e T.
Proof.
  intros fuel e T H. unfold infer_closed in H.
  destruct (infer fuel nil e 0) as [[[s T0] n]|] eqn:Ei; [|discriminate].
  inversion H; try subst s; try subst T; try subst n'; clear H.
  assert (Hwf : WfCtx nil) by (split; [constructor | intros x sc Hb; inversion Hb]).
  destruct ((proj1 (infer_sound fuel)) _ _ _ _ _ _ Ei Hwf) as (_ & _ & Hty).
  exact Hty.
Qed.
