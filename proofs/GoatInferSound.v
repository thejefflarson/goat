(* Soundness of algorithm W (GoatInfer.v) against the declarative [typing]:
   every type the algorithm infers is derivable (ADR 0037, decision 2).

   Read the statement of [infer_sound] first.  The algorithm threads a
   substitution [s], a kinding environment [D'] and a type [T]; the theorem
   says that, once [s] is applied to the context, the term has type [T] in
   [D'].  The side facts [OkS s] and [EvT T] are the even/odd bookkeeping of
   GoatInferSub.v that keeps substitutions off the quantified variables of
   schemes; [DOk] (GoatInferSort.v) says the environment is [Any] on the atoms
   the algorithm has not used, and [Good] bundles what each step of the
   algorithm preserves. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferTyp.
Require Import Goat.GoatInferRen.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferGen.
Require Import Goat.GoatInferRec.
Require Import Stdlib.Lists.List.
From Stdlib Require Import Lia.
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

Lemma cmp_ty_ground : forall A, cmp_ty A = true -> ground A.
Proof. intros A H. destruct A; simpl in H; try discriminate; unfold ground; auto. Qed.

Lemma bin_arg_ground : forall D o A B T, bin_arg D o A B = Some T -> ground T.
Proof.
  intros D o A B T H. unfold bin_arg in H.
  destruct (kind o).
  - discriminate.
  - inversion H; subst; unfold ground; auto.
  - inversion H; subst; unfold ground; auto.
  - destruct (cmp_ty B) eqn:EB; [ inversion H; subst; exact (cmp_ty_ground _ EB) | ].
    destruct (cmp_ty A) eqn:EA; [ inversion H; subst; exact (cmp_ty_ground _ EA) | ].
    destruct (orb (is_literal D A) (is_literal D B)); inversion H; subst; unfold ground; auto.
Qed.

Lemma bin_ty_sig : forall D o T R, bin_ty o T = Some R -> bin_sig D o T T R.
Proof.
  intros D o T R H. unfold bin_ty in H.
  destruct o; cbn in H; destruct T; try discriminate H;
    inversion H; subst;
    first [ (apply sig_ring; [ reflexivity | exact I ]) | apply sig_quot
          | apply sig_whole; reflexivity | (apply sig_cmp; [ reflexivity | constructor ]) ].
Qed.

Lemma bin_ty_EvT : forall o T R, bin_ty o T = Some R -> EvT R.
Proof.
  intros o T R H. unfold bin_ty in H.
  destruct (kind o); destruct T; try discriminate H;
    inversion H; subst;
    first [ apply EvT_Int | apply EvT_Float | apply EvT_Bool ].
Qed.

Lemma EvT_arrow : forall A B, EvT A -> EvT B -> EvT (typ_Arrow A B).
Proof.
  intros A B [H1 H2] [H3 H4]. split; intros a Ha; simpl in Ha;
    apply AtomSetFacts.union_iff in Ha; destruct Ha as [Ha|Ha]; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* What each step of the algorithm preserves                            *)
(* ------------------------------------------------------------------ *)

(* A step from environment [D] with supply [n] to [D'] with supply [n'],
   applying [s]: [D] is [Any] beyond [n], [s] is a substitution of the
   algorithm, the supply only grows, [D'] refines [D], and [s] respects the
   sorts. *)
Definition Good (D : denv) (n : nat) (s : sub) (D' : denv) (n' : nat) : Prop :=
  DOk D n /\ OkS s /\ DOk D' n' /\ n <= n' /\ kres D D' idt /\ kres D D' (sT s).

Lemma Good_id : forall D n, DOk D n -> Good D n sid D n.
Proof.
  intros D n H.
  exact (conj H (conj OkS_id (conj H (conj (le_n n) (conj (kres_id D) (kres_id D)))))).
Qed.

Lemma Good_comp : forall D n s1 D1 n1 s2 D2 n2,
  Good D n s1 D1 n1 -> Good D1 n1 s2 D2 n2 -> Good D n (scomp s2 s1) D2 n2.
Proof.
  intros D n s1 D1 n1 s2 D2 n2 (Hd & Hs1 & _ & Hl1 & Hi1 & Hk1) (_ & Hs2 & Hd2 & Hl2 & Hi2 & Hk2).
  exact (conj Hd (conj (OkS_comp _ _ Hs2 Hs1) (conj Hd2 (conj (Nat.le_trans _ _ _ Hl1 Hl2)
    (conj (kres_idt_trans _ _ _ Hi1 Hi2) (kres_scomp _ _ _ _ _ Hk1 Hk2)))))).
Qed.

Lemma Good_unify : forall D n s n',
  OkS s -> kres D D (sT s) -> n <= n' -> DOk D n -> Good D n s D n'.
Proof.
  intros D n s n' Hs Hk Hl Hd.
  exact (conj Hd (conj Hs (conj (DOk_mono D n n' Hd Hl) (conj Hl (conj (kres_id D) Hk))))).
Qed.

Lemma Good_lift : forall D n D' n' s D'' n'',
  Good D n sid D' n' -> Good D' n' s D'' n'' -> Good D n s D'' n''.
Proof.
  intros D n D' n' s D'' n'' (Hd & _ & _ & Hl1 & Hi1 & _) (_ & Hs & Hd2 & Hl2 & Hi2 & Hk2).
  exact (conj Hd (conj Hs (conj Hd2 (conj (Nat.le_trans _ _ _ Hl1 Hl2)
    (conj (kres_idt_trans _ _ _ Hi1 Hi2) (kres_refine_l _ _ _ _ Hi1 Hk2)))))).
Qed.

Lemma Good_upd : forall D n k, DOk D n -> Good D n sid (upd D (ea n) k) (S n).
Proof.
  intros D n k H.
  exact (conj H (conj OkS_id (conj (DOk_upd D n k H) (conj (le_S _ _ (le_n n))
    (conj (kres_upd D n k H) (kres_upd D n k H)))))).
Qed.

Lemma Good_pre : forall D n m s D' n',
  n <= m -> DOk D n -> Good D m s D' n' -> Good D n s D' n'.
Proof.
  intros D n m s D' n' Hnm Hd (_ & Hs & Hd' & Hl & Hi & Hk).
  exact (conj Hd (conj Hs (conj Hd' (conj (Nat.le_trans _ _ _ Hnm Hl) (conj Hi Hk))))).
Qed.

Lemma typing_ap_G : forall D n s D' n' G e T,
  Good D n s D' n' -> WfCtx G -> typing D G e T -> typing D' (apC s G) e (apT s T).
Proof.
  intros D n s D' n' G e T (Hd & Hs & Hd' & _ & _ & Hk) HG Hty.
  exact (typing_ap D D' s G e T Hs HG (DOk_supp D n Hd) (DOk_supp D' n' Hd') Hk Hty).
Qed.

Lemma typing_refine : forall D n D' n' G e T,
  Good D n sid D' n' -> WfCtx G -> typing D G e T -> typing D' G e T.
Proof.
  intros D n D' n' G e T Hg HG Hty.
  pose proof (typing_ap_G D n sid D' n' G e T Hg HG Hty) as H.
  rewrite apC_sid, apT_sid in H. exact H.
Qed.

(* The sorts the generalization records survive a step of the algorithm. *)
Lemma kres_ext_lift : forall D D' s V k,
  OkS s -> kres D D' (sT s) -> (forall a, a `in` V -> od a) ->
  kres (ext D V k) (ext D' V k) (sT s).
Proof.
  intros D D' s V k Hs Hk Hodd a.
  destruct Hs as [_ [Ht [_ [Hfx _]]]].
  destruct (AtomSetImpl.mem a V) eqn:Em.
  - apply AtomSetFacts.mem_iff in Em. rewrite (ext_in _ _ _ _ Em).
    rewrite (Hfx a (not_ev_od a (Hodd a Em))). simpl. rewrite (ext_in _ _ _ _ Em). apply finer_refl.
  - apply AtomSetFacts.not_mem_iff in Em. unfold kres in Hk.
    pose proof (Hk a) as Hka.
    rewrite (ext_out _ _ _ _ Em).
    apply sat_ext_out; [ exact Hka | ].
    intros b Hb Hbv.
    assert (Hna : ~ ev a).
    { intro Hea. pose proof (Ht a Hea) as HE. rewrite Hb in HE.
      exact (ev_od b (ev_var_T b HE) (Hodd b Hbv)). }
    rewrite (Hfx a Hna) in Hb. inversion Hb; subst. contradiction.
Qed.

Theorem infer_sound : forall f,
  (forall D G e n s D' T n', infer f D G e n = Some (s, D', T, n') -> WfCtx G -> DOk D n ->
     Good D n s D' n' /\ EvT T /\ typing D' (apC s G) e T) /\
  (forall D G fs n s D' R n', infer_fields f D G fs n = Some (s, D', R, n') -> WfCtx G -> DOk D n ->
     Good D n s D' n' /\ EvR R /\ field_typing D' (apC s G) fs R).
Proof.
  induction f as [|f IH]; [ split; intros; discriminate | ].
  destruct IH as [IHe IHf]. split.
  - intros D G e n s D' T n' H HG HD. cbn [infer] in H.
    destruct e as [i | x | k | d | | | b | e1 e2 | e1 e2 | fl el | fs | e1 l | | q | c0 a0 b0 | a1 o a2 | a3];
      try discriminate H.
    + (* variable *)
      destruct (lookup x G) as [sc|] eqn:Hl; [|discriminate].
      destruct (instantiate D sc n) as [[T0 D1] n1] eqn:Hi.
      inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      pose proof (lookup_binds _ _ _ Hl) as Hb.
      destruct (instantiate_sound _ _ _ _ _ _ Hi ((proj2 HG) _ _ Hb) HD) as (Hinst & Hev & HD1 & Hk).
      assert (Hle : n <= n1) by (unfold instantiate in Hi; inversion Hi; lia).
      split; [ exact (conj HD (conj OkS_id (conj HD1 (conj Hle (conj Hk Hk))))) | ].
      split; [exact Hev|].
      rewrite apC_sid. eapply T_Var; [ exact (proj1 HG) | exact Hb | exact Hinst ].
    + (* numeral *)
      inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      split; [ apply Good_upd; exact HD | ].
      split; [apply EvT_var, ev_ea|].
      apply T_Num; [ apply uniq_apC; exact (proj1 HG) | ].
      simpl. rewrite upd_same. apply finer_refl.
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_Float|].
      apply T_Dec. apply uniq_apC. exact (proj1 HG).
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_Bool|].
      apply T_True. apply uniq_apC. exact (proj1 HG).
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_Bool|].
      apply T_False. apply uniq_apC. exact (proj1 HG).
    + (* abstraction *)
      destruct (infer f D ((fresh_var G b ~ sch_mono (typ_Var (ea n))) ++ G)
                  (open_exp_wrt_exp b (e_fvar_f (fresh_var G b))) (S n))
        as [[[[s0 D1] T0] n0]|] eqn:Ei; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      assert (Hbeta : EvT (typ_Var (ea n))) by (apply EvT_var, ev_ea).
      assert (Hwf : WfCtx ((fresh_var G b ~ sch_mono (typ_Var (ea n))) ++ G))
        by (apply WfCtx_cons; [ exact HG | apply fresh_var_notin_dom | apply WfSch_mono; exact Hbeta ]).
      destruct (IHe _ _ _ _ _ _ _ _ Ei Hwf (DOk_mono D n (S n) HD (le_S _ _ (le_n n)))) as (Gd0 & HT0 & Hty).
      pose proof (Good_pre D n (S n) s0 D1 n0 (le_S _ _ (le_n n)) HD Gd0) as Gd.
      destruct Gd0 as (_ & Hs0 & _).
      split; [exact Gd|]. split.
      { apply EvT_arrow; [ apply EvT_ap; auto | exact HT0 ]. }
      rewrite apC_app, apC_single in Hty.
      apply T_Abs with (L := dom G `union` {{fresh_var G b}}).
      intros y Hy.
      assert (Hdom : y `notin` dom (apC s0 G)) by (rewrite dom_apC; fsetdec).
      apply (typing_rename_var D1 (apC s0 G) (fresh_var G b) y).
      * exact Hty.
      * apply fresh_var_notin_fv.
      * exact Hdom.
      * fsetdec.
    + (* application *)
      destruct (infer f D G e1 n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      destruct (infer f D1 (apC s1 G) e2 n1) as [[[[s2 D2] T2] n2]|] eqn:E2; [|discriminate].
      destruct (unify_t f D2 (apT s2 T1) (typ_Arrow T2 (typ_Var (ea n2))) (S n2))
        as [[s3 n3]|] eqn:E3; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHe _ _ _ _ _ _ _ _ E2 HG1 HD1) as (Gd2 & HT2 & Hty2).
      pose proof Gd2 as (_ & Hs2 & HD2 & _).
      pose proof (WfCtx_ap s2 _ Hs2 HG1) as HG2.
      assert (Hbeta : EvT (typ_Var (ea n2))) by (apply EvT_var, ev_ea).
      destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ E3 (EvT_ap s2 T1 Hs2 HT1)
                  (EvT_arrow _ _ HT2 Hbeta)) as (Hs3 & Hteq & Hk3 & Hl3).
      pose proof (Good_unify D2 n2 s3 n3 Hs3 Hk3 ltac:(lia) HD2) as Gd3.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3) | ].
      split; [ apply EvT_ap; auto | ].
      rewrite <- !apC_comp.
      eapply T_App.
      * eapply T_Conv; [ | exact Hteq ].
        apply (typing_ap_G D2 n2 s3 D2 n3 _ _ _ Gd3 HG2).
        apply (typing_ap_G D1 n1 s2 D2 n2 _ _ _ Gd2 HG1). exact Hty1.
      * apply (typing_ap_G D2 n2 s3 D2 n3 _ _ _ Gd3 HG2). exact Hty2.
    + (* let *)
      destruct (is_gen_value e1) eqn:Hgv.
      2: { (* a computed value: monomorphic *)
      destruct (infer f D G e1 n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      destruct (infer f D1 ((fresh_var (apC s1 G) e2 ~ sch_mono T1) ++ apC s1 G)
                  (open_exp_wrt_exp e2 (e_fvar_f (fresh_var (apC s1 G) e2))) n1)
        as [[[[s2 D2] T2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      assert (Hwf : WfCtx ((fresh_var (apC s1 G) e2 ~ sch_mono T1) ++ apC s1 G))
        by (apply WfCtx_cons; [ exact HG1 | apply fresh_var_notin_dom | apply WfSch_mono; exact HT1 ]).
      destruct (IHe _ _ _ _ _ _ _ _ E2 Hwf HD1) as (Gd2 & HT2 & Hty2).
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ]. split; [ exact HT2 | ].
      rewrite <- apC_comp.
      rewrite apC_app, apC_single in Hty2.
      apply T_LetMono with (L := dom G `union` {{fresh_var (apC s1 G) e2}}) (T1 := apT s2 T1).
      * apply (typing_ap_G D1 n1 s2 D2 n2 _ _ _ Gd2 HG1). exact Hty1.
      * intros y Hy.
        destruct Gd2 as (_ & Hs2 & _).
        assert (Hdom : y `notin` dom (apC s2 (apC s1 G)))
          by (rewrite dom_apC, dom_apC; fsetdec).
        exact (typing_rename_var D2 (apC s2 (apC s1 G)) (fresh_var (apC s1 G) e2) y
                 (apS s2 (sch_mono T1)) e2 T2 Hty2
                 (fresh_var_notin_fv _ _) Hdom ltac:(fsetdec)). }
      destruct (infer f D G e1 n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      destruct (infer f D1 ((fresh_var (apC s1 G) e2 ~ gen_ren D1 (apC s1 G) T1) ++ apC s1 G)
                  (open_exp_wrt_exp e2 (e_fvar_f (fresh_var (apC s1 G) e2))) n1)
        as [[[[s2 D2] T2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      pose proof (gen_ren_wf D1 (apC s1 G) T1 HT1) as Hwsc.
      assert (Hwf : WfCtx ((fresh_var (apC s1 G) e2 ~ gen_ren D1 (apC s1 G) T1) ++ apC s1 G))
        by (apply WfCtx_cons; [ exact HG1 | apply fresh_var_notin_dom | exact Hwsc ]).
      destruct (IHe _ _ _ _ _ _ _ _ E2 Hwf HD1) as (Gd2 & HT2 & Hty2).
      pose proof Gd2 as (_ & Hs2 & HD2 & Hl2 & Hi2 & Hk2).
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ]. split; [ exact HT2 | ].
      rewrite <- apC_comp.
      rewrite apC_app, apC_single in Hty2.
      pose proof (gen_ren_equiv D1 (apC s1 G) T1 s2 Hs2 HG1 HT1) as Hequiv.
      pose proof Hequiv as (Htq & _).
      apply T_Let with (L := dom G `union` {{fresh_var (apC s1 G) e2}})
                       (T1 := apT s2 (s_body (gen_ren D1 (apC s1 G) T1)))
                       (k := s_sk (gen_ren D1 (apC s1 G) T1)).
      * exact Hgv.
      * pose proof (typing_gen_ren D1 (apC s1 G) T1 n1 e1 HD1 Hty1) as Hg.
        destruct (DOk_supp D1 n1 HD1) as [S1 HS1].
        destruct (DOk_supp D2 n2 HD2) as [S2 HS2].
        pose proof (typing_ap (ext D1 (s_tq (gen_ren D1 (apC s1 G) T1)) (s_sk (gen_ren D1 (apC s1 G) T1)))
                      (ext D2 (s_tq (gen_ren D1 (apC s1 G) T1)) (s_sk (gen_ren D1 (apC s1 G) T1)))
                      s2 (apC s1 G) e1 (s_body (gen_ren D1 (apC s1 G) T1)) Hs2 HG1
                      (ex_intro _ _ (supp_ok_ext_set _ _ _ _ HS1))
                      (ex_intro _ _ (supp_ok_ext_set _ _ _ _ HS2))
                      (kres_ext_lift D1 D2 s2 _ _ Hs2 Hk2 (gen_ren_od_t D1 (apC s1 G) T1)) Hg) as Hl.
        eapply typing_pw; [ exact Hl | ].
        intros a. apply ext_set_eq. exact Htq.
      * intros y Hy.
        assert (Hdom : y `notin` dom (apC s2 (apC s1 G)))
          by (rewrite dom_apC, dom_apC; fsetdec).
        pose proof (typing_rename_var D2 (apC s2 (apC s1 G)) (fresh_var (apC s1 G) e2) y
                      (apS s2 (gen_ren D1 (apC s1 G) T1)) e2 T2 Hty2
                      (fresh_var_notin_fv _ _) Hdom ltac:(fsetdec)) as Hren.
        eapply typing_sch_equiv_ctx; [ exact Hren | ].
        apply ctx_equiv_cons; [ | apply ctx_equiv_refl ].
        exact Hequiv.
    + (* recursive group *)
      destruct (is_fn_group fl) eqn:Hfg; [|discriminate].
      set (p := fresh_var G (e_rec fl)) in *.
      set (R0 := group_row fl n) in *.
      destruct (infer_fields f D ((p ~ sch_mono (typ_Record R0)) ++ G)
                  (open_fields_wrt_exp fl (e_fvar_f p)) (n + nfields fl))
        as [[[[s1 D1] R1] n1]|] eqn:E1; [|discriminate].
      destruct (unify_pw f D1 R1 (apR s1 R0) n1) as [[s2 n2]|] eqn:E2; [|discriminate].
      set (G1 := apC (scomp s2 s1) G) in *.
      set (Rf := apR (scomp s2 s1) R0) in *.
      set (q := fresh_var G1 el) in *.
      destruct (infer f D1 ((q ~ gen_ren D1 G1 (typ_Record Rf)) ++ G1)
                  (open_exp_wrt_exp el (e_fvar_f q)) n2)
        as [[[[s3 D3] T3] n3]|] eqn:E3; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      assert (HR0 : EvR R0) by apply EvR_group_row.
      assert (Hwf0 : WfCtx ((p ~ sch_mono (typ_Record R0)) ++ G))
        by (apply WfCtx_cons; [ exact HG | apply fresh_var_notin_dom | apply WfSch_mono, EvT_Record; exact HR0 ]).
      assert (Hnn : n <= n + nfields fl) by lia.
      destruct (IHf _ _ _ _ _ _ _ _ E1 Hwf0 (DOk_mono D n _ HD Hnn)) as (Gd1' & HR1 & Hty1).
      pose proof (Good_pre D n _ s1 D1 n1 Hnn HD Gd1') as Gd1.
      pose proof Gd1 as (_ & Hs1 & HD1 & Hl1 & Hi1 & Hk1).
      rewrite apC_app, apC_single in Hty1.
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      pose proof (EvR_ap s1 _ Hs1 HR0) as HR0'.
      destruct (unify_pw_sound f D1 _ _ _ _ _ E2 HR1 HR0') as (Hs2 & Hpw & Hk2 & Hl2).
      pose proof (Good_unify D1 n1 s2 n2 Hs2 Hk2 Hl2 HD1) as Gd2.
      pose proof (DOk_supp D1 n1 HD1) as HS1.
      pose proof (fields_ap D1 D1 s2 (apC s1 G) p _ _ _ Hs2 HG1 HS1 HS1 Hk2 Hty1) as Hty2.
      pose proof (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) as Gd21.
      assert (Hs21 : OkS (scomp s2 s1)) by (destruct Gd21 as (_ & H21 & _); exact H21).
      assert (HRf : EvR Rf) by (apply EvR_ap; assumption).
      assert (HG21 : WfCtx G1) by (apply WfCtx_ap; assumption).
      assert (Hty3 : field_typing D1 ((p ~ sch_mono (typ_Record Rf)) ++ G1)
                       (open_fields_wrt_exp fl (e_fvar_f p)) Rf).
      { unfold Rf, G1. rewrite <- apR_comp. rewrite <- apC_comp.
        apply pw_conv with (R := apR s2 R1); [ | exact Hpw ].
        change (typ_Record (apR s2 (apR s1 R0))) with (apT s2 (apT s1 (typ_Record R0))) in Hty2.
        exact Hty2. }
      pose proof (gen_ren_wf D1 G1 (typ_Record Rf) (proj2 (EvT_Record _) HRf)) as Hwsc.
      assert (Hwf1 : WfCtx ((q ~ gen_ren D1 G1 (typ_Record Rf)) ++ G1))
        by (apply WfCtx_cons; [ exact HG21 | apply fresh_var_notin_dom | exact Hwsc ]).
      destruct (IHe _ _ _ _ _ _ _ _ E3 Hwf1 (DOk_mono D1 n1 n2 HD1 Hl2)) as (Gd3' & HT3 & Hty4).
      pose proof Gd3' as Gd3.
      pose proof Gd3 as (_ & Hs3 & HD3 & Hl3 & Hi3 & Hk3).
      pose proof (Good_comp _ _ _ _ _ _ _ _ Gd21 Gd3) as Gdf.
      split; [ exact Gdf | ]. split; [ exact HT3 | ].
      rewrite <- apC_comp. fold G1.
      rewrite apC_app, apC_single in Hty4.
      pose proof (gen_ren_equiv D1 G1 (typ_Record Rf) s3 Hs3 HG21 (proj2 (EvT_Record _) HRf)) as Hequiv.
      pose proof Hequiv as (Htq & _).
      pose proof (fields_gen_ren D1 n2 G1 p Rf _ (DOk_mono D1 n1 n2 HD1 Hl2) Hty3) as Hty5.
      destruct (DOk_supp D1 n2 (DOk_mono D1 n1 n2 HD1 Hl2)) as [S1' HS1'].
      destruct (DOk_supp D3 n3 HD3) as [S3 HS3].
      pose proof (fields_ap (ext D1 (s_tq (gen_ren D1 G1 (typ_Record Rf))) (s_sk (gen_ren D1 G1 (typ_Record Rf))))
                    (ext D3 (s_tq (gen_ren D1 G1 (typ_Record Rf))) (s_sk (gen_ren D1 G1 (typ_Record Rf))))
                    s3 G1 p _ _ _ Hs3 HG21
                    (ex_intro _ _ (supp_ok_ext_set _ _ _ _ HS1'))
                    (ex_intro _ _ (supp_ok_ext_set _ _ _ _ HS3))
                    (kres_ext_lift D1 D3 s3 _ _ Hs3 Hk3 (gen_ren_od_t D1 G1 (typ_Record Rf))) Hty5) as Hty6.
      apply T_Letrec with (L := dom G `union` {{p}} `union` {{q}})
        (R := apR s3 (ap_row (rename_t (gen_vars_t G1 (typ_Record Rf)))
                             (rename_r (gen_vars_r G1 (typ_Record Rf))) Rf))
        (k := s_sk (gen_ren D1 G1 (typ_Record Rf))).
      * apply is_fn_group_sound. exact Hfg.
      * intros y Hy.
        assert (Hdom : y `notin` dom (apC s3 G1)) by (rewrite dom_apC; unfold G1; rewrite dom_apC; fsetdec).
        pose proof (fields_rename_var _ (apC s3 G1) p y _ _ _ Hty6
                      (fresh_var_notin_fv _ _) Hdom ltac:(fsetdec)) as Hf.
        eapply field_typing_pw; [ exact Hf | intros a; apply ext_set_eq; exact Htq ].
      * intros y Hy.
        assert (Hdom : y `notin` dom (apC s3 G1)) by (rewrite dom_apC; unfold G1; rewrite dom_apC; fsetdec).
        pose proof (typing_rename_var D3 (apC s3 G1) q y
                      (apS s3 (gen_ren D1 G1 (typ_Record Rf))) el T3 Hty4
                      (fresh_var_notin_fv _ _) Hdom ltac:(fsetdec)) as Hren.
        eapply typing_sch_equiv_ctx; [ exact Hren | ].
        apply ctx_equiv_cons; [ | apply ctx_equiv_refl ].
        exact Hequiv.
    + (* record *)
      destruct (infer_fields f D G fs n) as [[[[s0 D1] R0] n0]|] eqn:Ei; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      destruct (IHf _ _ _ _ _ _ _ _ Ei HG HD) as (Gd0 & HR0 & Hty).
      split; [exact Gd0|]. split; [ apply EvT_Record; exact HR0 | ].
      apply T_Record. exact Hty.
    + (* projection *)
      destruct (infer f D G e1 n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      destruct (unify_t f D1 T1 (typ_Record (row_Ext l (typ_Var (ea n1)) (row_Var (ea (S n1)))))
                  (n1 + 2)) as [[s2 n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      assert (Hrow : EvT (typ_Record (row_Ext l (typ_Var (ea n1)) (row_Var (ea (S n1)))))).
      { apply EvT_Record, EvR_ext; [ apply EvT_var, ev_ea | apply EvR_var, ev_ea ]. }
      destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ E2 HT1 Hrow) as (Hs2 & Hteq & Hk2 & Hl2).
      pose proof (Good_unify D1 n1 s2 n2 Hs2 Hk2 ltac:(lia) HD1) as Gd2.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ apply EvT_ap; [exact Hs2 | apply EvT_var, ev_ea] | ].
      rewrite <- apC_comp.
      eapply T_Proj.
      eapply T_Conv; [ | exact Hteq ].
      apply (typing_ap_G D1 n1 s2 D1 n2 _ _ _ Gd2 HG1). exact Hty1.
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_Unit|].
      apply T_Unit. apply uniq_apC. exact (proj1 HG).
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_String|].
      apply T_Str. apply uniq_apC. exact (proj1 HG).
    + (* conditional *)
      destruct (infer f D G c0 n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      destruct (unify_t f D1 T1 typ_Bool n1) as [[s2 n2]|] eqn:E2; [|discriminate].
      destruct (infer f D1 (apC s2 (apC s1 G)) a0 n2) as [[[[s3 D3] T2] n3]|] eqn:E3; [|discriminate].
      destruct (infer f D3 (apC s3 (apC s2 (apC s1 G))) b0 n3) as [[[[s4 D4] T3] n4]|] eqn:E4;
        [|discriminate].
      destruct (unify_t f D4 (apT s4 T2) T3 n4) as [[s5 n5]|] eqn:E5; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ E2 HT1 EvT_Bool) as (Hs2 & Hteq2 & Hk2 & Hl2).
      pose proof (Good_unify D1 n1 s2 n2 Hs2 Hk2 Hl2 HD1) as Gd2.
      pose proof (WfCtx_ap s2 _ Hs2 HG1) as HG2.
      assert (HD2 : DOk D1 n2) by (destruct Gd2 as (_ & _ & H2 & _); exact H2).
      destruct (IHe _ _ _ _ _ _ _ _ E3 HG2 HD2) as (Gd3 & HT2 & Hty2).
      pose proof Gd3 as (_ & Hs3 & HD3 & _).
      pose proof (WfCtx_ap s3 _ Hs3 HG2) as HG3.
      destruct (IHe _ _ _ _ _ _ _ _ E4 HG3 HD3) as (Gd4 & HT3 & Hty3).
      pose proof Gd4 as (_ & Hs4 & HD4 & _).
      pose proof (WfCtx_ap s4 _ Hs4 HG3) as HG4.
      destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ E5 (EvT_ap s4 T2 Hs4 HT2) HT3)
        as (Hs5 & Hteq5 & Hk5 & Hl5).
      pose proof (Good_unify D4 n4 s5 n5 Hs5 Hk5 Hl5 HD4) as Gd5.
      pose proof (WfCtx_ap s5 _ Hs5 HG4) as HG5.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _
                 (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3) Gd4) Gd5) | ].
      split; [ apply EvT_ap; auto | ].
      rewrite <- !apC_comp.
      assert (Hc : typing D1 (apC s2 (apC s1 G)) c0 typ_Bool).
      { eapply T_Conv; [ | exact Hteq2 ].
        apply (typing_ap_G D1 n1 s2 D1 n2 _ _ _ Gd2 HG1). exact Hty1. }
      eapply T_If.
      * exact (typing_ap_G D4 n4 s5 D4 n5 _ _ _ Gd5 HG4
                 (typing_ap_G D3 n3 s4 D4 n4 _ _ _ Gd4 HG3
                   (typing_ap_G D1 n2 s3 D3 n3 _ _ _ Gd3 HG2 Hc))).
      * eapply T_Conv; [ | exact Hteq5 ].
        apply (typing_ap_G D4 n4 s5 D4 n5 _ _ _ Gd5 HG4).
        apply (typing_ap_G D3 n3 s4 D4 n4 _ _ _ Gd4 HG3). exact Hty2.
      * apply (typing_ap_G D4 n4 s5 D4 n5 _ _ _ Gd5 HG4). exact Hty3.
    + (* binary operation *)
      destruct (infer f D G a1 n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      destruct (infer f D1 (apC s1 G) a2 n1) as [[[[s2 D2] T2] n2]|] eqn:E2; [|discriminate].
      destruct (IHe _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHe _ _ _ _ _ _ _ _ E2 HG1 HD1) as (Gd2 & HT2 & Hty2).
      pose proof Gd2 as (_ & Hs2 & HD2 & _).
      pose proof (WfCtx_ap s2 _ Hs2 HG1) as HG2.
      destruct (is_ring_op o) eqn:Hring.
      * (* [+ - *]: both operands at one Numeric variable's type *)
        assert (Hko : kind o = k_ring)
          by (unfold is_ring_op in Hring; destruct (kind o); [ reflexivity | discriminate | discriminate | discriminate ]).
        set (D2' := upd D2 (ea n2) k_Numeric) in *.
        destruct (unify_t f D2' (apT s2 T1) (typ_Var (ea n2)) (S n2)) as [[s3 n3]|] eqn:E3; [|discriminate].
        destruct (unify_t f D2' (apT s3 T2) (apT s3 (typ_Var (ea n2))) n3) as [[s4 n4]|] eqn:E4; [|discriminate].
        inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
        assert (HN : D2' (ea n2) = k_Numeric) by (unfold D2'; apply upd_same).
        assert (HEc : EvT (typ_Var (ea n2))) by (apply EvT_var, ev_ea).
        pose proof (Good_upd D2 n2 k_Numeric HD2) as GdU.
        fold D2' in GdU.
        assert (HD2' : DOk D2' (S n2)) by (destruct GdU as (_ & _ & H2 & _); exact H2).
        destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ E3 (EvT_ap s2 T1 Hs2 HT1) HEc)
          as (Hs3 & Hteq3 & Hk3 & Hl3).
        pose proof (Good_unify D2' (S n2) s3 n3 Hs3 Hk3 Hl3 HD2') as Gd3.
        pose proof (WfCtx_ap s3 _ Hs3 HG2) as HG3.
        destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ E4 (EvT_ap s3 T2 Hs3 HT2)
                    (EvT_ap s3 _ Hs3 HEc)) as (Hs4 & Hteq4 & Hk4 & Hl4).
        pose proof (Good_unify D2' n3 s4 n4 Hs4 Hk4 Hl4 (DOk_mono D2' (S n2) n3 HD2' Hl3)) as Gd4.
        split.
        { exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2)
                   (Good_lift _ _ _ _ _ _ _ GdU Gd3)) Gd4). }
        split; [ apply EvT_ap; [ exact Hs4 | apply EvT_ap; [ exact Hs3 | exact HEc ] ] | ].
        rewrite <- !apC_comp.
        assert (Hsat : sat D2' k_Numeric (apT s4 (apT s3 (typ_Var (ea n2))))).
        { pose proof (Hk3 (ea n2)) as H3. rewrite HN in H3.
          exact (sat_ap D2' D2' k_Numeric _ (sT s4) (sR s4) Hk4 H3). }
        eapply T_Bin with (A := apT s4 (apT s3 (typ_Var (ea n2)))).
        -- pose proof (teq_apT s4 _ _ Hteq3) as Hteq3'.
           eapply T_Conv; [ | exact Hteq3' ] .
           apply (typing_ap_G D2' n3 s4 D2' n4 _ _ _ Gd4 HG3).
           apply (typing_ap_G D2' (S n2) s3 D2' n3 _ _ _ Gd3 HG2).
           apply (typing_refine D2 n2 D2' (S n2) _ _ _ GdU HG2).
           apply (typing_ap_G D1 n1 s2 D2 n2 _ _ _ Gd2 HG1). exact Hty1.
        -- eapply T_Conv; [ | exact Hteq4 ].
           apply (typing_ap_G D2' n3 s4 D2' n4 _ _ _ Gd4 HG3).
           apply (typing_ap_G D2' (S n2) s3 D2' n3 _ _ _ Gd3 HG2).
           apply (typing_refine D2 n2 D2' (S n2) _ _ _ GdU HG2). exact Hty2.
        -- apply sig_ring; [ exact Hko | exact Hsat ].
      * destruct (bin_arg D2 o (apT s2 T1) T2) as [Ta|] eqn:E3; [|discriminate].
        destruct (unify_t f D2 (apT s2 T1) Ta n2) as [[s3 n3]|] eqn:E4; [|discriminate].
        destruct (unify_t f D2 (apT s3 T2) Ta n3) as [[s4 n4]|] eqn:E5; [|discriminate].
        destruct (bin_ty o Ta) as [R|] eqn:E6; [|discriminate].
        inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
        pose proof (bin_arg_ground _ _ _ _ _ E3) as Hg.
        pose proof (ground_EvT _ Hg) as HTa.
        destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ E4 (EvT_ap s2 T1 Hs2 HT1) HTa)
          as (Hs3 & Hteq3 & Hk3 & Hl3).
        pose proof (Good_unify D2 n2 s3 n3 Hs3 Hk3 Hl3 HD2) as Gd3.
        pose proof (WfCtx_ap s3 _ Hs3 HG2) as HG3.
        destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ E5 (EvT_ap s3 T2 Hs3 HT2) HTa)
          as (Hs4 & Hteq4 & Hk4 & Hl4).
        pose proof (Good_unify D2 n3 s4 n4 Hs4 Hk4 Hl4 (DOk_mono D2 n2 n3 HD2 Hl3)) as Gd4.
        pose proof (WfCtx_ap s4 _ Hs4 HG3) as HG4.
        rewrite (ground_ap s3 _ Hg) in Hteq3.
        rewrite (ground_ap s4 _ Hg) in Hteq4.
        split.
        { exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3) Gd4). }
        split; [ exact (bin_ty_EvT _ _ _ E6) | ].
        rewrite <- !apC_comp.
        eapply T_Bin; [ | | exact (bin_ty_sig D2 _ _ _ E6) ].
        -- pose proof (teq_apT s4 _ _ Hteq3) as Hteq3'.
           rewrite (ground_ap s4 _ Hg) in Hteq3'.
           eapply T_Conv; [ | exact Hteq3' ].
           apply (typing_ap_G D2 n3 s4 D2 n4 _ _ _ Gd4 HG3).
           apply (typing_ap_G D2 n2 s3 D2 n3 _ _ _ Gd3 HG2).
           apply (typing_ap_G D1 n1 s2 D2 n2 _ _ _ Gd2 HG1). exact Hty1.
        -- eapply T_Conv; [ | exact Hteq4 ].
           apply (typing_ap_G D2 n3 s4 D2 n4 _ _ _ Gd4 HG3).
           apply (typing_ap_G D2 n2 s3 D2 n3 _ _ _ Gd3 HG2). exact Hty2.
    + (* Int-to-Float coercion at any Numeric type *)
      destruct (infer f D G a3 n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      set (D1' := upd D1 (ea n1) k_Numeric) in *.
      destruct (unify_t f D1' T1 (typ_Var (ea n1)) (S n1)) as [[s2 n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      assert (HN : D1' (ea n1) = k_Numeric) by (unfold D1'; apply upd_same).
      assert (HEc : EvT (typ_Var (ea n1))) by (apply EvT_var, ev_ea).
      pose proof (Good_upd D1 n1 k_Numeric HD1) as GdU. fold D1' in GdU.
      assert (HD1' : DOk D1' (S n1)) by (destruct GdU as (_ & _ & H2 & _); exact H2).
      destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ E2 HT1 HEc) as (Hs2 & Hteq & Hk2 & Hl2).
      pose proof (Good_unify D1' (S n1) s2 n2 Hs2 Hk2 Hl2 HD1') as Gd2.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 (Good_lift _ _ _ _ _ _ _ GdU Gd2)) | ].
      split; [ apply EvT_Float | ].
      rewrite <- apC_comp.
      apply T_ToFloat with (A := apT s2 (typ_Var (ea n1))).
      * eapply T_Conv; [ | exact Hteq ].
        apply (typing_ap_G D1' (S n1) s2 D1' n2 _ _ _ Gd2 HG1).
        apply (typing_refine D1 n1 D1' (S n1) _ _ _ GdU HG1). exact Hty1.
      * pose proof (Hk2 (ea n1)) as H3. rewrite HN in H3. exact H3.
  - intros D G fs n s D' R n' H HG HD. cbn [infer_fields] in H.
    destruct fs as [| l e rest]; try discriminate H.
    + inversion H; try subst s; try subst D'; try subst R; try subst n'; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvR_Empty|].
      apply FT_nil. apply uniq_apC. exact (proj1 HG).
    + destruct (infer f D G e n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      destruct (infer_fields f D1 (apC s1 G) rest n1) as [[[[s2 D2] R2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst R; try subst n'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHf _ _ _ _ _ _ _ _ E2 HG1 HD1) as (Gd2 & HR2 & Hty2).
      pose proof Gd2 as (_ & Hs2 & _).
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ apply EvR_ext; [ apply EvT_ap; auto | exact HR2 ] | ].
      rewrite <- apC_comp.
      eapply FT_cons.
      * apply (typing_ap_G D1 n1 s2 D2 n2 _ _ _ Gd2 HG1). exact Hty1.
      * exact Hty2.
Qed.

(* The statement for programs: a closed term the algorithm accepts has the
   type it returns, in the kinding environment it returns, which records the
   sort of each variable the type leaves free. *)
Theorem infer_closed_sound : forall fuel e D T,
  infer_closed_env fuel e = Some (D, T) -> typing D nil e T.
Proof.
  intros fuel e D T H. unfold infer_closed_env in H.
  destruct (infer fuel d_any nil e 0) as [[[[s D0] T0] n]|] eqn:Ei; [|discriminate].
  inversion H; subst; clear H.
  assert (Hwf : WfCtx nil) by (split; [constructor | intros x sc Hb; inversion Hb]).
  destruct ((proj1 (infer_sound fuel)) _ _ _ _ _ _ _ _ Ei Hwf (d_any_DOk 0)) as (_ & _ & Hty).
  exact Hty.
Qed.
