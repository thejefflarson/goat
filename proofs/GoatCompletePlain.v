(* Completeness of algorithm W, stage 7.9: collapsing a monomorphic derivation
   (docs/design/phase7-proof-plan.md).

   [rtyping] (GoatCompleteConv.v) demands that every type a derivation holds be
   record-free.  A derivation of [typing] may choose a record, a recursive type
   or a tag group for a parameter, an operand or a result, although a term
   without records, tags, [letrec], [fold] or [unfold] never builds or takes one
   apart.  [psi] sends each such type to [Float], which satisfies every sort,
   and is the identity on a record-free type.  The conversions [teq] relates keep
   the head of a type ([teq_thead]), so two convertible types have one image:
   a derivation that moves between them by [T_ConvD] needs no step after the
   collapse.

   [mtyping] is the monomorphic core over arbitrary types, with the conversion
   rule: every rule of [rtyping] without the record-free premises, and
   [M_Conv].  [mtyping_rtyping] collapses it to [rtyping] at the images of the
   types; the theorem the stage ends on is [infer_complete_core_plain_mono].

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatMu.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferW.
Require Import Goat.GoatElab.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteFresh.
Require Import Goat.GoatCompleteMono.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteCore.
Require Import Goat.GoatCompleteCoreW.
Require Import Goat.GoatCompleteConv.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the collapse of a type ---- *)

Fixpoint psi (T : typ) : typ :=
  match T with
  | typ_Arrow A B => typ_Arrow (psi A) (psi B)
  | typ_Record _ | typ_Mu _ | typ_Grp _ _ | typ_Bvar _ => typ_Float
  | typ_Int | typ_Float | typ_Bool | typ_Unit | typ_String | typ_Var _ => T
  end.

Lemma rf_psi : forall T, rf (psi T).
Proof. induction T; simpl; try exact I; split; assumption. Qed.

Lemma psi_rf : forall T, rf T -> psi T = T.
Proof.
  induction T; simpl; intros H; try reflexivity; try contradiction.
  destruct H as [H1 H2]. rewrite (IHT1 H1), (IHT2 H2). reflexivity.
Qed.

Lemma teq_psi : forall T T', teq T T' -> psi T = psi T'.
Proof.
  intros T T' H.
  induction H using teq_mutind with (P0 := fun R R' _ => True); simpl; try reflexivity; try exact I.
  - rewrite IHteq1, IHteq2. reflexivity.
  - etransitivity; eassumption.
  - symmetry. assumption.
Qed.

Lemma psi_nfT : forall D T, psi (nfT D T) = psi T.
Proof.
  intros D. induction T; simpl; try reflexivity. rewrite IHT1, IHT2. reflexivity.
Qed.

Lemma teqD_psi : forall D T T', teqD D T T' -> psi T = psi T'.
Proof.
  intros D T T' H. rewrite <- (psi_nfT D T), <- (psi_nfT D T'). apply teq_psi. exact H.
Qed.

Lemma sat_psi : forall D k T, sat D k T -> sat D k (psi T).
Proof.
  intros D k T. induction T; simpl; intros H; try exact H; try exact I.
Qed.

(* ---- the monomorphic core over arbitrary types ---- *)

Inductive mtyping : list (atom * typ) -> exp -> typ -> Prop :=
  | M_Var : forall Gm x T, uniq (mctx Gm) -> In (x, T) Gm -> mtyping Gm (e_fvar_f x) T
  | M_Num : forall Gm i T, uniq (mctx Gm) -> sat d_any k_Literal T -> mtyping Gm (e_num i) T
  | M_Dec : forall Gm d, uniq (mctx Gm) -> mtyping Gm (e_dec d) typ_Float
  | M_True : forall Gm, uniq (mctx Gm) -> mtyping Gm e_true typ_Bool
  | M_False : forall Gm, uniq (mctx Gm) -> mtyping Gm e_false typ_Bool
  | M_Unit : forall Gm, uniq (mctx Gm) -> mtyping Gm e_unit typ_Unit
  | M_Str : forall Gm q, uniq (mctx Gm) -> mtyping Gm (e_str q) typ_String
  | M_Abs : forall Gm e T1 T2,
      (forall x, x `notin` dom (mctx Gm) `union` fv_exp e ->
         mtyping ((x, T1) :: Gm) (open_exp_wrt_exp e (e_fvar_f x)) T2) ->
      mtyping Gm (e_abs e) (typ_Arrow T1 T2)
  | M_App : forall Gm e1 e2 T1 T2,
      mtyping Gm e1 (typ_Arrow T1 T2) -> mtyping Gm e2 T1 -> mtyping Gm (e_app e1 e2) T2
  | M_If : forall Gm e1 e2 e3 T,
      mtyping Gm e1 typ_Bool -> mtyping Gm e2 T -> mtyping Gm e3 T -> mtyping Gm (e_ite e1 e2 e3) T
  | M_ToFloat : forall Gm e A, sat d_any k_Literal A ->
      mtyping Gm e A -> mtyping Gm (e_tofloat e) typ_Float
  | M_Arith : forall Gm e1 o e2 A, kind o <> k_cmp -> sat d_any (generic_sort o) A ->
      mtyping Gm e1 A -> mtyping Gm e2 A -> mtyping Gm (e_bin e1 o e2) A
  | M_Cmp : forall Gm e1 o e2 A, kind o = k_cmp -> sat d_any k_Eq A ->
      mtyping Gm e1 A -> mtyping Gm e2 A -> mtyping Gm (e_bin e1 o e2) typ_Bool
  | M_LetMono : forall Gm e1 e2 T1 T2,
      mtyping Gm e1 T1 ->
      (forall x, x `notin` dom (mctx Gm) `union` fv_exp e2 ->
         mtyping ((x, T1) :: Gm) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
      mtyping Gm (e_let e1 e2) T2
  | M_Conv : forall Gm e T T', mtyping Gm e T -> teqD d_any T T' -> mtyping Gm e T'.

Theorem mtyping_typing : forall Gm e T, mtyping Gm e T -> typing d_any (mctx Gm) e T.
Proof.
  intros Gm e T H. induction H.
  - eapply T_Var; [ assumption | apply binds_mctx; eassumption | apply inst_mono_self ].
  - apply T_Num; assumption.
  - apply T_Dec; assumption.
  - apply T_True; assumption.
  - apply T_False; assumption.
  - apply T_Unit; assumption.
  - apply T_Str; assumption.
  - apply T_Abs with (L := dom (mctx Gm) `union` fv_exp e). exact H0.
  - eapply T_App; eassumption.
  - apply T_If; assumption.
  - eapply T_ToFloat; eassumption.
  - eapply T_Bin; [ exact IHmtyping1 | exact IHmtyping2 | ].
    unfold generic_sort in H0. destruct (kind o) eqn:Ek; try contradiction.
    + apply sig_ring; assumption.
    + assert (Ho : o = bop_div) by (destruct o; first [ reflexivity | discriminate Ek ]).
      rewrite Ho. apply sig_quot. assumption.
    + apply sig_whole; assumption.
  - eapply T_Bin; [ exact IHmtyping1 | exact IHmtyping2 | ]. apply sig_cmp; assumption.
  - apply T_LetMono with (L := dom (mctx Gm) `union` fv_exp e2) (T1 := T1); [ exact IHmtyping | assumption ].
  - eapply T_ConvD; eassumption.
Qed.

(* ---- the collapse of a derivation ---- *)

Definition mpsi (Gm : list (atom * typ)) : list (atom * typ) := List.map (fun p => (fst p, psi (snd p))) Gm.

Lemma dom_mctx_mpsi : forall Gm, dom (mctx (mpsi Gm)) = dom (mctx Gm).
Proof. induction Gm as [|[y U] Gm IH]; [ reflexivity | ]. simpl. f_equal. exact IH. Qed.

Lemma uniq_mctx_mpsi : forall Gm, uniq (mctx Gm) -> uniq (mctx (mpsi Gm)).
Proof.
  intros Gm H. induction Gm as [|[y U] Gm IH]; [ constructor | ].
  simpl in *. inversion H; subst. constructor; [ apply IH; assumption | ].
  rewrite dom_mctx_mpsi. assumption.
Qed.

Theorem mtyping_rtyping : forall Gm e T, mtyping Gm e T -> rtyping (mpsi Gm) e (psi T).
Proof.
  intros Gm e T H. induction H; simpl.
  - apply R_Var; [ apply uniq_mctx_mpsi; assumption | | apply rf_psi ].
    unfold mpsi. change (x, psi T) with ((fun p => (fst p, psi (snd p))) (x, T)). apply in_map. assumption.
  - apply R_Num; [ apply uniq_mctx_mpsi; assumption | apply sat_psi; assumption | apply rf_psi ].
  - apply R_Dec. apply uniq_mctx_mpsi; assumption.
  - apply R_True. apply uniq_mctx_mpsi; assumption.
  - apply R_False. apply uniq_mctx_mpsi; assumption.
  - apply R_Unit. apply uniq_mctx_mpsi; assumption.
  - apply R_Str. apply uniq_mctx_mpsi; assumption.
  - apply R_Abs; [ apply rf_psi | apply rf_psi | ].
    intros x Hx. rewrite dom_mctx_mpsi in Hx. exact (H0 x Hx).
  - simpl in IHmtyping1. eapply R_App; [ apply rf_psi | apply rf_psi | exact IHmtyping1 | exact IHmtyping2 ].
  - apply R_If; assumption.
  - apply R_ToFloat with (A := psi A); [ apply rf_psi | apply sat_psi; assumption | assumption ].
  - apply R_Arith; [ assumption | apply sat_psi; assumption | apply rf_psi | assumption | assumption ].
  - apply R_Cmp with (A := psi A); [ assumption | apply sat_psi; assumption | apply rf_psi | assumption | assumption ].
  - apply R_LetMono with (T1 := psi T1); [ apply rf_psi | apply rf_psi | assumption | ].
    intros x Hx. rewrite dom_mctx_mpsi in Hx. exact (H1 x Hx).
  - rewrite <- (teqD_psi _ _ _ H0). exact IHmtyping.
Qed.

(* ---- substitution on a record-free type ---- *)

Fixpoint rs (f : atom -> typ) (T : typ) : typ :=
  match T with
  | typ_Var a => f a
  | typ_Arrow A B => typ_Arrow (rs f A) (rs f B)
  | _ => T
  end.

Lemma ap_rs : forall st sr T, rf T -> ap_typ st sr T = rs st T.
Proof.
  intros st sr T. induction T; simpl; intros H; try contradiction; try reflexivity.
  destruct H as [H1 H2]. rewrite (IHT1 H1), (IHT2 H2). reflexivity.
Qed.

Lemma rs_comp : forall f h T, rs f (rs h T) = rs (fun a => rs f (h a)) T.
Proof. intros f h. induction T; simpl; try reflexivity. rewrite IHT1, IHT2. reflexivity. Qed.

Lemma rs_agree : forall f f' T, (forall a, a `in` ftv_typ T -> f a = f' a) -> rs f T = rs f' T.
Proof.
  intros f f' T. induction T; simpl; intros H; try reflexivity.
  - rewrite (IHT1 (fun a Ha => H a ltac:(fsetdec))), (IHT2 (fun a Ha => H a ltac:(fsetdec))). reflexivity.
  - apply H. fsetdec.
Qed.

Lemma rs_var : forall T, rs typ_Var T = T.
Proof. induction T; simpl; try reflexivity. rewrite IHT1, IHT2. reflexivity. Qed.

Lemma rnT_rs : forall g T, rf T -> rnT g T = rs (fun a => typ_Var (g a)) T.
Proof. intros g T H. unfold rnT. exact (ap_rs _ _ _ H). Qed.

Lemma rs_rf : forall f T, rf T -> (forall a, a `in` ftv_typ T -> rf (f a)) -> rf (rs f T).
Proof.
  intros f T. induction T; simpl; intros H Hf; try contradiction; try exact I.
  - destruct H as [H1 H2]. split; [ apply IHT1 | apply IHT2 ]; try assumption;
      intros a Ha; apply Hf; fsetdec.
  - apply Hf. fsetdec.
Qed.

Lemma rnT_invol : forall g T, (forall x, g (g x) = x) -> rf T -> rnT g (rnT g T) = T.
Proof.
  intros g T Hg H. rewrite (rnT_rs g T H). rewrite (rnT_rs g _ (rs_rf (fun a => typ_Var (g a)) T H (fun a _ => I))).
  rewrite rs_comp. rewrite <- (rs_var T) at 2. apply rs_agree. intros a _. simpl. rewrite Hg. reflexivity.
Qed.

(* ---- the closed program ---- *)

(* A swap of atoms that makes a record-free type even, undone by itself. *)
Lemma even_swap_inv : forall T : typ, rf T ->
  exists g, (forall x, g (g x) = x) /\ PEv (rnT g T).
Proof.
  intros T Hrf.
  destruct (mk_rename_even (ftv_typ T) (ftv_typ T)) as (f & N & Hinv & HNB & HNV & HVN & Hfix & HNev).
  exists f. split; [ exact Hinv | ].
  split; [ | apply rf_rnT; exact Hrf ].
  apply ev_rnT; [ exact Hrf | ]. intros a Ha. apply HNev. apply HVN. exact Ha.
Qed.

(* A monomorphic derivation of a core program, at any type, gives a run of the
   closed entry point, from some fuel on, whose result is a principal type of
   the derivation's type with each record, recursive type and tag group
   replaced by [Float]: that type is an instance of the result, under a
   substitution that respects the sorts [D] gives the result's atoms.  On a
   record-free type [psi] is the identity, so the derivation's own type is the
   instance. *)
Theorem infer_complete_core_plain : forall e T, mtyping nil e T ->
  exists D T' e' S,
    Stable (fun f => infer_closed_elab f e = Some (D, T', e')) /\ erase e' = e /\
    kres D d_any (sT S) /\ rkres D d_any (sR S) /\ teqD d_any (apT S T') (psi T) /\ rf T'.
Proof.
  intros e T H.
  destruct (even_swap_inv (psi T) (rf_psi T)) as (g & Hg & HP).
  pose proof (rtyping_ren _ _ _ (mtyping_rtyping nil e T H) g) as H'.
  change (mren g (mpsi nil)) with (@nil (atom * typ)) in H'.
  pose proof (rtyping_ctyping _ _ _ H' (fun x U Hin => match Hin with end) HP {}) as Hc.
  destruct (infer_complete_core_closed e (rnT g (psi T)) Hc)
    as (D & T' & e' & S2 & Hs & He & Hl & Hr & Ht & Hf).
  assert (Hlf : forall a, a `in` ftv_typ T' -> rf (sT S2 a)) by (intros a Ha; exact (proj2 (proj2 (Hl a Ha)))).
  set (S := Sub (fun a => if AtomSetImpl.mem a (ftv_typ T') then rnT g (sT S2 a) else typ_Float) (sR S2)).
  exists D, T', e', S.
  assert (HS : apT S T' = rnT g (apT S2 T')).
  { unfold apT. cbn [sT sR S]. rewrite (ap_rs _ _ _ Hf), (ap_rs _ _ _ Hf).
    rewrite (rnT_rs g _ (rs_rf _ _ Hf Hlf)), rs_comp. apply rs_agree. intros a Ha. simpl.
    pose proof (Hlf a Ha) as Hfa. apply AtomSetFacts.mem_iff in Ha. rewrite Ha. rewrite (rnT_rs g _ Hfa).
    reflexivity. }
  refine (conj Hs (conj He (conj _ (conj Hr (conj _ Hf))))).
  - intros a. cbn [sT S]. destruct (AtomSetImpl.mem a (ftv_typ T')) eqn:Em.
    + apply AtomSetFacts.mem_iff in Em. exact (sat_rnT g _ _ (proj1 (Hl a Em))).
    + exact I.
  - rewrite HS.
    pose proof (teqD_rf_eq d_any (apT S2 T') (rnT g (psi T)) (rf_ap S2 T' Hf Hlf) Ht) as Eq.
    rewrite <- Eq. rewrite (rnT_invol g _ Hg (rf_psi T)). apply teq_teqD. apply teq_refl.
Qed.
