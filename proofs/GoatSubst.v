(* Substitution-metatheory groundwork for core goat: the Hindley-Milner
   type/row substitution ALGEBRA and the structural L4 lemmas (docs/semantics.md
   section 7).  The two canonical HM lemmas (L4 [typing_weaken], L5
   [typing_tsubst_fix]), term substitution (L6a/L6b), preservation and soundness
   build on [casch_inst] (GoatHM) and so live in GoatSound.v, which is compiled
   after it; this file holds only what GoatBij/GoatHM/GoatSound depend on.

   Type and row variables are metalib [atom]s (issue #151); [ftv]/[frv] and the
   scheme quantifier sets are [atoms] finite sets with decidable membership, so
   capture-avoiding type/row substitution of a context is computable and the
   substitution lemmas go through without any classical or functional-
   extensionality axiom.

   Assumption-free (no axioms, no admits):

   - Type/row-substitution algebra: [ap_typ_pointwise_id], [ap_typ_ext],
     [ap_typ_comp], and the monotype-instance facts [inst_mono_eq] /
     [inst_mono_self].
   - [teq_ap]: type equivalence is closed under any type/row substitution.
   - [typing_sch_equiv_ctx] (typing respects pointwise scheme-equivalence of the
     context) and [typing_ftv_mono] (a more-general / fewer-ftv context preserves
     typing).
   - L5 renaming: [typing_rename] -- typing is preserved by any bijective
     type/row-variable renaming.
   - [gen_antimono] / [ctx_more_gen]: generalization is antitone in the context.
*)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMeta.
Require Import Coq.Lists.List.

(* ================= type-substitution algebra (from L5 groundwork) ========== *)

(* pointwise-identity substitution is the identity *)
Lemma ap_pointwise_id_mut :
  (forall T st sr, (forall a, st a = typ_Var a) -> (forall r, sr r = row_Var r) ->
     ap_typ st sr T = T) /\
  (forall R st sr, (forall a, st a = typ_Var a) -> (forall r, sr r = row_Var r) ->
     ap_row st sr R = R).
Proof.
  apply typ_row_mutind; intros; simpl; try reflexivity;
    try (f_equal; auto).
Qed.

Lemma ap_typ_pointwise_id : forall T st sr,
  (forall a, st a = typ_Var a) -> (forall r, sr r = row_Var r) -> ap_typ st sr T = T.
Proof. apply ap_pointwise_id_mut. Qed.

(* the only instance of a monotype scheme is itself *)
Lemma inst_mono_eq : forall T U, inst T (sch_mono U) -> T = U.
Proof.
  intros T U [st [sr [Ht [Hr Heq]]]]. simpl in *.
  rewrite Heq. apply ap_typ_pointwise_id.
  - intros a. apply Ht. simpl. fsetdec.
  - intros r. apply Hr. simpl. fsetdec.
Qed.

(* sch_mono is always an instance of itself *)
Lemma inst_mono_self : forall U, inst U (sch_mono U).
Proof.
  intros U. exists idt, idr.
  split; [|split].
  - intros a _. reflexivity.
  - intros r _. reflexivity.
  - symmetry. apply ap_typ_pointwise_id; reflexivity.
Qed.

(* ================= type-substitution algebra ================= *)

(* extensionality: ap_typ depends only on the substitution's action on fvs *)
Lemma ap_ext_mut :
  (forall T st sr st' sr',
     (forall a, a `in` ftv_typ T -> st a = st' a) ->
     (forall r, r `in` frv_typ T -> sr r = sr' r) ->
     ap_typ st sr T = ap_typ st' sr' T) /\
  (forall R st sr st' sr',
     (forall a, a `in` ftv_row R -> st a = st' a) ->
     (forall r, r `in` frv_row R -> sr r = sr' r) ->
     ap_row st sr R = ap_row st' sr' R).
Proof.
  apply typ_row_mutind; intros; simpl in *; try reflexivity.
  - (* Arrow *) f_equal; [ apply H | apply H0 ]; intros; [apply H1|apply H2|apply H1|apply H2]; fsetdec.
  - (* Record *) f_equal; apply H; intros; [apply H0|apply H1]; fsetdec.
  - (* Var a *) apply H. fsetdec.
  - (* row_Var *) apply H0. fsetdec.
  - (* row_Ext *) f_equal; [ apply H | apply H0 ]; intros; [apply H1|apply H2|apply H1|apply H2]; fsetdec.
Qed.

Lemma ap_typ_ext : forall T st sr st' sr',
  (forall a, a `in` ftv_typ T -> st a = st' a) ->
  (forall r, r `in` frv_typ T -> sr r = sr' r) ->
  ap_typ st sr T = ap_typ st' sr' T.
Proof. apply ap_ext_mut. Qed.

(* composition *)
Definition tcomp (st : tsub) (sr : rsub) (st0 : tsub) : tsub :=
  fun a => ap_typ st sr (st0 a).
Definition rcomp (st : tsub) (sr : rsub) (sr0 : rsub) : rsub :=
  fun r => ap_row st sr (sr0 r).

Lemma ap_comp_mut :
  (forall T st sr st0 sr0,
     ap_typ st sr (ap_typ st0 sr0 T) = ap_typ (tcomp st sr st0) (rcomp st sr sr0) T) /\
  (forall R st sr st0 sr0,
     ap_row st sr (ap_row st0 sr0 R) = ap_row (tcomp st sr st0) (rcomp st sr sr0) R).
Proof.
  apply typ_row_mutind; intros; simpl in *; try reflexivity;
    try (f_equal; auto).
Qed.

Lemma ap_typ_comp : forall T st sr st0 sr0,
  ap_typ st sr (ap_typ st0 sr0 T) = ap_typ (tcomp st sr st0) (rcomp st sr sr0) T.
Proof. apply ap_comp_mut. Qed.

(* ================= scheme/context equivalence; L4 structural lemmas ======== *)

(* scheme equivalence up to the quantifier sets *)
Definition sch_equiv (s s' : scheme) : Prop :=
  s_tq s [=] s_tq s' /\ s_rq s [=] s_rq s' /\ s_body s = s_body s'.

Lemma sch_equiv_refl : forall s, sch_equiv s s.
Proof. intros s. unfold sch_equiv. split; [|split]; [ fsetdec | fsetdec | reflexivity ]. Qed.

Lemma sch_equiv_sym : forall s s', sch_equiv s s' -> sch_equiv s' s.
Proof.
  intros s s' (A & B & C). unfold sch_equiv.
  split; [ fsetdec | split; [ fsetdec | congruence ] ].
Qed.

(* inst respects sch_equiv *)
Lemma inst_sch_equiv : forall T s s',
  sch_equiv s s' -> inst T s -> inst T s'.
Proof.
  intros T s s' [Htq [Hrq Hbody]] [st [sr [Ht [Hr Heq]]]].
  exists st, sr. repeat split.
  - intros a Ha. apply Ht. fsetdec.
  - intros r Hr0. apply Hr. fsetdec.
  - rewrite <- Hbody. exact Heq.
Qed.

(* Ftv_sch respects sch_equiv *)
Lemma Ftv_sch_equiv : forall s s' a, sch_equiv s s' -> (Ftv_sch s a <-> Ftv_sch s' a).
Proof.
  intros s s' a (Htq & Hrq & Hbody). unfold Ftv_sch, ftv_sch. rewrite Hbody. fsetdec.
Qed.

Lemma Frv_sch_equiv : forall s s' r, sch_equiv s s' -> (Frv_sch s r <-> Frv_sch s' r).
Proof.
  intros s s' r (Htq & Hrq & Hbody). unfold Frv_sch, frv_sch. rewrite Hbody. fsetdec.
Qed.

(* pointwise scheme-equivalence of contexts *)
Definition ctx_equiv (G G' : ctx) : Prop :=
  Forall2 (fun b b' => fst b = fst b' /\ sch_equiv (snd b) (snd b')) G G'.

Lemma ctx_equiv_refl : forall G, ctx_equiv G G.
Proof. induction G as [|[x s] G IH]; constructor; auto using sch_equiv_refl. Qed.

Lemma ctx_equiv_dom : forall G G', ctx_equiv G G' -> dom G [=] dom G'.
Proof.
  induction 1 as [|[x s] [y s'] G G' [Hk He] HF IH]; simpl in *.
  - reflexivity.
  - subst y. rewrite IH. reflexivity.
Qed.

Lemma ctx_equiv_uniq : forall G G', ctx_equiv G G' -> uniq G -> uniq G'.
Proof.
  induction 1 as [|[x s] [y s'] G G' [Hk He] HF IH]; intros Hu; auto.
  simpl in *. subst y. inversion Hu; subst.
  constructor; auto. rewrite <- (ctx_equiv_dom _ _ HF). auto.
Qed.

Lemma ctx_equiv_binds : forall G G' x s,
  ctx_equiv G G' -> binds x s G ->
  exists s', binds x s' G' /\ sch_equiv s s'.
Proof.
  induction 1 as [|[y sy] [z sz] G G' [Hk He] HF IH]; intros Hb.
  - inversion Hb.
  - simpl in *. subst z. apply binds_cons_1 in Hb. destruct Hb as [[Hx Hs]|Hb].
    + subst. exists sz. split; [ apply binds_cons_2; auto | auto ].
    + destruct (IH Hb) as [s' [Hb' Heq']]. exists s'. split; [ apply binds_cons_3; auto | auto ].
Qed.

Lemma ctx_equiv_Ftv : forall G G' a,
  ctx_equiv G G' -> (Ftv_ctx G a <-> Ftv_ctx G' a).
Proof.
  unfold Ftv_ctx. induction 1 as [|[x s] [y s'] G G' [Hk He] HF IH]; simpl.
  - reflexivity.
  - pose proof (Ftv_sch_equiv s s' a He) as Hs. unfold Ftv_sch in Hs.
    rewrite !AtomSetFacts.union_iff. rewrite Hs, IH. reflexivity.
Qed.

Lemma ctx_equiv_sym : forall G G', ctx_equiv G G' -> ctx_equiv G' G.
Proof.
  induction 1 as [|[u su][v sv] ? ? [Hk Hs] ? IH]; constructor; auto.
  simpl in *; subst; split; auto using sch_equiv_sym.
Qed.

Lemma ctx_equiv_Frv : forall G G' r,
  ctx_equiv G G' -> (Frv_ctx G r <-> Frv_ctx G' r).
Proof.
  unfold Frv_ctx. induction 1 as [|[x s] [y s'] G G' [Hk He] HF IH]; simpl.
  - reflexivity.
  - pose proof (Frv_sch_equiv s s' r He) as Hs. unfold Frv_sch in Hs.
    rewrite !AtomSetFacts.union_iff. rewrite Hs, IH. reflexivity.
Qed.

(* generalization respects context equivalence *)
Lemma gen_ctx_equiv : forall G G' T,
  ctx_equiv G G' -> sch_equiv (gen G T) (gen G' T).
Proof.
  intros G G' T H. unfold sch_equiv, gen; simpl. split; [| split]; [| |reflexivity].
  - assert (ftv_ctx G [=] ftv_ctx G') by (intro z; apply (ctx_equiv_Ftv _ _ z H)).
    fsetdec.
  - assert (frv_ctx G [=] frv_ctx G') by (intro z; apply (ctx_equiv_Frv _ _ z H)).
    fsetdec.
Qed.

Lemma ctx_equiv_cons : forall x s s' G G',
  sch_equiv s s' -> ctx_equiv G G' -> ctx_equiv ((x ~ s) ++ G) ((x ~ s') ++ G').
Proof. intros. constructor; simpl; auto. Qed.

(* typing respects pointwise scheme-equivalence of the context *)
Lemma typing_sch_equiv_ctx_mut :
  (forall G e T, typing G e T -> forall G', ctx_equiv G G' -> typing G' e T) /\
  (forall G fs R, field_typing G fs R -> forall G', ctx_equiv G G' -> field_typing G' fs R).
Proof.
  apply typing_field_mutind; intros.
  - (* T_Var *) destruct (ctx_equiv_binds _ _ _ _ H b) as [s' [Hb' Heq]].
    apply T_Var with (s := s'); eauto using ctx_equiv_uniq, inst_sch_equiv.
  - (* T_Num *) apply T_Num; eauto using ctx_equiv_uniq.
  - (* T_NumFloat *) apply T_NumFloat; eauto using ctx_equiv_uniq.
  - (* T_Dec *) apply T_Dec; eauto using ctx_equiv_uniq.
  - (* T_True *) apply T_True; eauto using ctx_equiv_uniq.
  - (* T_False *) apply T_False; eauto using ctx_equiv_uniq.
  - (* T_Abs *) apply T_Abs with (L := L); intros x Hx.
    apply H; auto. apply ctx_equiv_cons; auto using sch_equiv_refl.
  - (* T_App *) eapply T_App; eauto.
  - (* T_Let *) apply T_Let with (L := L) (T1 := T1); auto.
    intros x Hx. apply H0; auto.
    apply ctx_equiv_cons; auto. apply gen_ctx_equiv; auto.
  - (* T_Record *) apply T_Record; eauto.
  - (* T_Proj *) eapply T_Proj; eauto.
  - (* T_Conv *) eapply T_Conv; eauto.
  - (* T_Unit *) apply T_Unit; eauto using ctx_equiv_uniq.
  - (* T_Str *) apply T_Str; eauto using ctx_equiv_uniq.
  - (* T_If *) eapply T_If; eauto.
  - (* T_Bin *) eapply T_Bin; eauto.
  - (* FT_nil *) apply FT_nil; eauto using ctx_equiv_uniq.
  - (* FT_cons *) eapply FT_cons; eauto.
Qed.

Lemma typing_sch_equiv_ctx : forall G G' e T,
  typing G e T -> ctx_equiv G G' -> typing G' e T.
Proof. intros. eapply (proj1 typing_sch_equiv_ctx_mut); eauto. Qed.

(* "s' is at least as general as s, and mentions no more free variables" *)
Definition sch_more_gen (s s' : scheme) : Prop :=
  (forall W, inst W s -> inst W s') /\
  (forall a, Ftv_sch s' a -> Ftv_sch s a) /\
  (forall r, Frv_sch s' r -> Frv_sch s r).

Lemma sch_more_gen_refl : forall s, sch_more_gen s s.
Proof. intros; split; [|split]; auto. Qed.

Definition ctx_more_gen (G G' : ctx) : Prop :=
  Forall2 (fun b b' => fst b = fst b' /\ sch_more_gen (snd b) (snd b')) G G'.

Lemma ctx_more_gen_dom : forall G G', ctx_more_gen G G' -> dom G [=] dom G'.
Proof.
  induction 1 as [|[x s][y s'] G G' [Hk He] HF IH]; simpl in *; [reflexivity|].
  subst y. rewrite IH. reflexivity.
Qed.

Lemma ctx_more_gen_uniq : forall G G', ctx_more_gen G G' -> uniq G -> uniq G'.
Proof.
  induction 1 as [|[x s][y s'] G G' [Hk He] HF IH]; intros Hu; auto.
  simpl in *; subst y. inversion Hu; subst.
  constructor; auto. rewrite <- (ctx_more_gen_dom _ _ HF); auto.
Qed.

Lemma ctx_more_gen_binds : forall G G' x s,
  ctx_more_gen G G' -> binds x s G ->
  exists s', binds x s' G' /\ sch_more_gen s s'.
Proof.
  induction 1 as [|[y sy][z sz] G G' [Hk He] HF IH]; intros Hb; [inversion Hb|].
  simpl in *; subst z. apply binds_cons_1 in Hb. destruct Hb as [[Hx Hs]|Hb].
  - subst. exists sz. split; [apply binds_cons_2; auto|auto].
  - destruct (IH Hb) as [s' [Hb' Hg']]. exists s'. split; [apply binds_cons_3; auto|auto].
Qed.

(* if G' mentions no more free vars than G (pointwise), then ftv_ctx G' [<=] ftv_ctx G *)
Lemma ctx_more_gen_Ftv : forall G G' a,
  ctx_more_gen G G' -> Ftv_ctx G' a -> Ftv_ctx G a.
Proof.
  unfold Ftv_ctx. induction 1 as [|[y sy][z sz] G G' [Hk Hg] HF IH]; simpl; intros Hin.
  - fsetdec.
  - rewrite AtomSetFacts.union_iff in Hin |- *.
    destruct Hg as [_ [Hftv _]].
    destruct Hin as [Hin|Hin]; [left; apply Hftv; exact Hin | right; apply IH; exact Hin].
Qed.

Lemma ctx_more_gen_Frv : forall G G' r,
  ctx_more_gen G G' -> Frv_ctx G' r -> Frv_ctx G r.
Proof.
  unfold Frv_ctx. induction 1 as [|[y sy][z sz] G G' [Hk Hg] HF IH]; simpl; intros Hin.
  - fsetdec.
  - rewrite AtomSetFacts.union_iff in Hin |- *.
    destruct Hg as [_ [_ Hfrv]].
    destruct Hin as [Hin|Hin]; [left; apply Hfrv; exact Hin | right; apply IH; exact Hin].
Qed.

(* gen respects ctx_more_gen: fewer ctx free vars => more general & fewer scheme free vars *)
Lemma gen_more_gen : forall G G' T,
  ctx_more_gen G G' -> sch_more_gen (gen G T) (gen G' T).
Proof.
  intros G G' T H.
  assert (Hsub_t : ftv_ctx G' [<=] ftv_ctx G)
    by (intros a Ha; apply (ctx_more_gen_Ftv _ _ _ H); exact Ha).
  assert (Hsub_r : frv_ctx G' [<=] frv_ctx G)
    by (intros r Hr; apply (ctx_more_gen_Frv _ _ _ H); exact Hr).
  unfold sch_more_gen, Ftv_sch, Frv_sch, ftv_sch, frv_sch, gen; simpl.
  split; [|split].
  - intros W [st [sr [Ht [Hr Heq]]]]. simpl in Ht, Hr.
    exists st, sr. simpl. split; [| split].
    + intros a Hna. apply Ht. simpl in Hna |- *. fsetdec.
    + intros r Hnr. apply Hr. simpl in Hnr |- *. fsetdec.
    + exact Heq.
  - intros a Hin. fsetdec.
  - intros r Hin. fsetdec.
Qed.

Lemma ctx_more_gen_cons : forall x s s' G G',
  sch_more_gen s s' -> ctx_more_gen G G' -> ctx_more_gen ((x ~ s) ++ G) ((x ~ s') ++ G').
Proof. intros. constructor; simpl; auto. Qed.

(* L4-style: typing is preserved under a more-general / fewer-ftv context *)
Lemma typing_ftv_mono_mut :
  (forall G e T, typing G e T -> forall G', ctx_more_gen G G' -> typing G' e T) /\
  (forall G fs R, field_typing G fs R -> forall G', ctx_more_gen G G' -> field_typing G' fs R).
Proof.
  apply typing_field_mutind; intros.
  - (* T_Var *) destruct (ctx_more_gen_binds _ _ _ _ H b) as [s' [Hb' [Hinst _]]].
    apply T_Var with (s := s'); eauto using ctx_more_gen_uniq.
  - apply T_Num; eauto using ctx_more_gen_uniq.
  - apply T_NumFloat; eauto using ctx_more_gen_uniq.
  - apply T_Dec; eauto using ctx_more_gen_uniq.
  - apply T_True; eauto using ctx_more_gen_uniq.
  - apply T_False; eauto using ctx_more_gen_uniq.
  - (* T_Abs *) apply T_Abs with (L := L); intros x Hx.
    apply H; auto. apply ctx_more_gen_cons; auto using sch_more_gen_refl.
  - eapply T_App; eauto.
  - (* T_Let *) apply T_Let with (L := L) (T1 := T1); auto. intros x Hx.
    apply H0; auto. apply ctx_more_gen_cons; auto. apply gen_more_gen; auto.
  - apply T_Record; eauto.
  - eapply T_Proj; eauto.
  - eapply T_Conv; eauto.
  - (* T_Unit *) apply T_Unit; eauto using ctx_more_gen_uniq.
  - (* T_Str *) apply T_Str; eauto using ctx_more_gen_uniq.
  - (* T_If *) eapply T_If; eauto.
  - (* T_Bin *) eapply T_Bin; eauto.
  - apply FT_nil; eauto using ctx_more_gen_uniq.
  - eapply FT_cons; eauto.
Qed.

Lemma typing_ftv_mono : forall G e T G',
  typing G e T -> ctx_more_gen G G' -> typing G' e T.
Proof. intros. eapply (proj1 typing_ftv_mono_mut); eauto. Qed.

(* ================= teq under substitution; L5 for bijective renamings ====== *)

(* type-equivalence is a congruence closed under any type/row substitution
   (labels are untouched by substitution, so the swap rule still applies). *)
Scheme teq_mutind := Induction for teq Sort Prop
with   req_mutind := Induction for req Sort Prop.
Combined Scheme teq_req_mutind from teq_mutind, req_mutind.

Lemma teq_ap_mut :
  (forall T T', teq T T' -> forall st sr, teq (ap_typ st sr T) (ap_typ st sr T')) /\
  (forall R R', req R R' -> forall st sr, req (ap_row st sr R) (ap_row st sr R')).
Proof.
  apply teq_req_mutind; intros; simpl in *.
  - apply teq_refl.
  - apply teq_refl.
  - apply teq_refl.
  - apply teq_refl.
  - apply teq_refl.
  - apply teq_refl.
  - apply teq_arrow; auto.
  - apply teq_rec; auto.
  - eapply teq_trans; eauto.
  - apply teq_sym; auto.
  - apply req_refl.
  - apply req_refl.
  - apply req_head; auto.
  - apply req_swap; auto.
  - eapply req_trans; eauto.
  - apply req_sym; auto.
Qed.

Lemma teq_ap : forall T T' st sr, teq T T' -> teq (ap_typ st sr T) (ap_typ st sr T').
Proof. intros. apply teq_ap_mut; auto. Qed.

(* ================= finite-set image under a function ================= *)

Lemma in_fold_add : forall (f : atom -> atom) l b,
  b `in` fold_right (fun a acc => add (f a) acc) {} l <-> exists a, List.In a l /\ f a = b.
Proof.
  induction l as [|a0 l IH]; simpl; intros b.
  - split; [ intro H; fsetdec | intros [a [[] _]] ].
  - rewrite AtomSetFacts.add_iff. split.
    + intros [Heq | Hin].
      * exists a0. split; [ left; reflexivity | exact Heq ].
      * apply IH in Hin. destruct Hin as [a [Hina Hfa]]. exists a. split; [ right; auto | auto ].
    + intros [a [[Ha|Ha] Hfa]].
      * subst a. left. exact Hfa.
      * right. apply IH. exists a. auto.
Qed.

Lemma In_elements : forall a S, List.In a (AtomSetImpl.elements S) <-> a `in` S.
Proof.
  intros a S. split; intro H.
  - apply AtomSetImpl.elements_2. apply (In_InA eq_equivalence). exact H.
  - apply AtomSetImpl.elements_1 in H. apply InA_alt in H.
    destruct H as [y [Hy Hin]]. subst; auto.
Qed.

Definition amap (f : atom -> atom) (S : atoms) : atoms :=
  fold_right (fun a acc => add (f a) acc) {} (AtomSetImpl.elements S).

Lemma amap_in : forall f S b, b `in` amap f S <-> exists a, a `in` S /\ f a = b.
Proof.
  intros f S b. unfold amap. rewrite in_fold_add.
  split; intros [a [Ha Hfa]]; exists a; split; auto; apply In_elements; auto.
Qed.

(* ================= L5 for bijective renamings ====== *)

Section Renaming.
Variables (f g : typvar -> typvar) (fr gr : rowvar -> rowvar).
Hypothesis gf : forall a, g (f a) = a.
Hypothesis fg : forall a, f (g a) = a.
Hypothesis grfr : forall r, gr (fr r) = r.
Hypothesis frgr : forall r, fr (gr r) = r.

Definition rt : tsub := fun a => typ_Var (f a).
Definition rr : rsub := fun r => row_Var (fr r).
Definition ren_typ (T:typ) := ap_typ rt rr T.
Definition ren_row (R:row) := ap_row rt rr R.

Lemma amap_f_in : forall S b, b `in` amap f S <-> g b `in` S.
Proof.
  intros S b. rewrite amap_in. split.
  - intros [a [Ha Hfa]]. subst b. rewrite gf. exact Ha.
  - intro H. exists (g b). split; [ exact H | apply fg ].
Qed.

Lemma amap_fr_in : forall S b, b `in` amap fr S <-> gr b `in` S.
Proof.
  intros S b. rewrite amap_in. split.
  - intros [a [Ha Hfa]]. subst b. rewrite grfr. exact Ha.
  - intro H. exists (gr b). split; [ exact H | apply frgr ].
Qed.

Lemma Ftv_ren_mut :
  (forall T a, a `in` ftv_typ (ap_typ rt rr T) <-> g a `in` ftv_typ T) /\
  (forall R a, a `in` ftv_row (ap_row rt rr R) <-> g a `in` ftv_row R).
Proof.
  apply typ_row_mutind; intros; simpl.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - rewrite !AtomSetFacts.union_iff. rewrite H, H0. reflexivity.
  - apply H.
  - (* Var a0 *) unfold rt; simpl. rewrite !AtomSetFacts.singleton_iff.
    split; [ intro HH; rewrite <- HH; symmetry; apply gf | intro HH; rewrite HH; apply fg ].
  - fsetdec.
  - (* row_Var *) unfold rr; simpl. fsetdec.
  - rewrite !AtomSetFacts.union_iff. rewrite H, H0. reflexivity.
Qed.

Lemma Frv_ren_mut :
  (forall T r, r `in` frv_typ (ap_typ rt rr T) <-> gr r `in` frv_typ T) /\
  (forall R r, r `in` frv_row (ap_row rt rr R) <-> gr r `in` frv_row R).
Proof.
  apply typ_row_mutind; intros; simpl.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - rewrite !AtomSetFacts.union_iff. rewrite H, H0. reflexivity.
  - apply H.
  - (* Var a0 *) unfold rt; simpl. fsetdec.
  - fsetdec.
  - (* row_Var *) unfold rr; simpl. rewrite !AtomSetFacts.singleton_iff.
    split; [ intro HH; rewrite <- HH; symmetry; apply grfr | intro HH; rewrite HH; apply frgr ].
  - rewrite !AtomSetFacts.union_iff. rewrite H, H0. reflexivity.
Qed.

Definition ren_sch (s:scheme) : scheme :=
  Sch (amap f (s_tq s)) (amap fr (s_rq s)) (ren_typ (s_body s)).
Definition ren_ctx (G:ctx) : ctx :=
  List.map (fun b => (fst b, ren_sch (snd b))) G.

Lemma dom_ren_ctx : forall G, dom (ren_ctx G) [=] dom G.
Proof. induction G as [|[x s] G IH]; simpl; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma uniq_ren_ctx : forall G, uniq G -> uniq (ren_ctx G).
Proof.
  induction G as [|[x s] G IH]; intros Hu; simpl; auto.
  inversion Hu; subst. constructor; auto. rewrite dom_ren_ctx; auto.
Qed.

Lemma binds_ren_ctx : forall x s G, binds x s G -> binds x (ren_sch s) (ren_ctx G).
Proof.
  induction G as [|[y sy] G IH]; intros Hb; [inversion Hb|].
  apply binds_cons_1 in Hb. destruct Hb as [[Hx Hs]|Hb].
  - subst. apply binds_cons_2; auto.
  - apply binds_cons_3; auto.
Qed.

Lemma Ftv_sch_ren : forall s a, Ftv_sch (ren_sch s) a <-> Ftv_sch s (g a).
Proof.
  intros s a. unfold Ftv_sch, ftv_sch, ren_sch, ren_typ; simpl.
  pose proof (proj1 Ftv_ren_mut (s_body s) a) as HF.
  rewrite !AtomSetFacts.diff_iff. rewrite HF. rewrite amap_f_in. reflexivity.
Qed.

Lemma Frv_sch_ren : forall s r, Frv_sch (ren_sch s) r <-> Frv_sch s (gr r).
Proof.
  intros s r. unfold Frv_sch, frv_sch, ren_sch, ren_typ; simpl.
  pose proof (proj1 Frv_ren_mut (s_body s) r) as HF.
  rewrite !AtomSetFacts.diff_iff. rewrite HF. rewrite amap_fr_in. reflexivity.
Qed.

Lemma Ftv_ctx_ren : forall G a, Ftv_ctx (ren_ctx G) a <-> Ftv_ctx G (g a).
Proof.
  intros G a. unfold Ftv_ctx. induction G as [|[x s] G IH].
  - simpl. fsetdec.
  - replace (ren_ctx ((x, s) :: G)) with ((x, ren_sch s) :: ren_ctx G) by reflexivity.
    simpl ftv_ctx. rewrite !AtomSetFacts.union_iff.
    pose proof (Ftv_sch_ren s a) as Hs. unfold Ftv_sch in Hs.
    rewrite Hs, IH. reflexivity.
Qed.

Lemma Frv_ctx_ren : forall G r, Frv_ctx (ren_ctx G) r <-> Frv_ctx G (gr r).
Proof.
  intros G r. unfold Frv_ctx. induction G as [|[x s] G IH].
  - simpl. fsetdec.
  - replace (ren_ctx ((x, s) :: G)) with ((x, ren_sch s) :: ren_ctx G) by reflexivity.
    simpl frv_ctx. rewrite !AtomSetFacts.union_iff.
    pose proof (Frv_sch_ren s r) as Hs. unfold Frv_sch in Hs.
    rewrite Hs, IH. reflexivity.
Qed.

(* instantiation commutes with a bijective renaming *)
Lemma inst_ren : forall T s, inst T s -> inst (ren_typ T) (ren_sch s).
Proof.
  intros T s [st [sr [Ht [Hr Heq]]]].
  exists (fun c => ren_typ (st (g c))), (fun c => ren_row (sr (gr c))).
  unfold ren_sch; simpl. repeat split.
  - (* id off quantifier *)
    intros a Hna. unfold ren_typ.
    assert (st (g a) = typ_Var (g a)) as Hid.
    { apply Ht. intro Hc. apply Hna. apply amap_f_in. exact Hc. }
    rewrite Hid. simpl. unfold rt. rewrite fg. reflexivity.
  - intros r Hnr. unfold ren_row.
    assert (sr (gr r) = row_Var (gr r)) as Hid.
    { apply Hr. intro Hc. apply Hnr. apply amap_fr_in. exact Hc. }
    rewrite Hid. simpl. unfold rr. rewrite frgr. reflexivity.
  - (* ren_typ T = ap_typ (new) ... (ren_typ body) *)
    unfold ren_typ, ren_row. subst T.
    rewrite ap_typ_comp. rewrite ap_typ_comp.
    apply ap_typ_ext; intros; unfold tcomp, rcomp.
    + unfold rt. simpl. rewrite gf. reflexivity.
    + unfold rr. simpl. rewrite grfr. reflexivity.
Qed.

Lemma ren_sch_mono_equiv : forall T, sch_equiv (ren_sch (sch_mono T)) (sch_mono (ren_typ T)).
Proof.
  intros T. unfold sch_equiv, ren_sch, sch_mono; simpl. split; [|split].
  - intro a. rewrite amap_f_in. fsetdec.
  - intro r. rewrite amap_fr_in. fsetdec.
  - reflexivity.
Qed.

Lemma ren_ctx_app : forall x sx G,
  ren_ctx ((x ~ sx) ++ G) = (x ~ ren_sch sx) ++ ren_ctx G.
Proof. reflexivity. Qed.

(* generalization commutes with a bijective renaming (up to sch_equiv) *)
Lemma gen_ren : forall G T,
  sch_equiv (ren_sch (gen G T)) (gen (ren_ctx G) (ren_typ T)).
Proof.
  intros G T. unfold sch_equiv, ren_sch, gen; simpl. split; [|split]; [| |reflexivity].
  - (* amap f (diff (ftv_typ T) (ftv_ctx G)) [=] diff (ftv_typ (ren_typ T)) (ftv_ctx (ren_ctx G)) *)
    intro a. rewrite amap_f_in. rewrite !AtomSetFacts.diff_iff.
    pose proof (proj1 Ftv_ren_mut T a) as HT. unfold ren_typ in HT. rewrite HT.
    pose proof (Ftv_ctx_ren G a) as HG. unfold Ftv_ctx in HG. rewrite HG.
    reflexivity.
  - intro r. rewrite amap_fr_in. rewrite !AtomSetFacts.diff_iff.
    pose proof (proj1 Frv_ren_mut T r) as HT. unfold ren_typ in HT. rewrite HT.
    pose proof (Frv_ctx_ren G r) as HG. unfold Frv_ctx in HG. rewrite HG.
    reflexivity.
Qed.

(* typing is preserved by a bijective type/row-variable renaming *)
Lemma typing_rename_mut :
  (forall G e T, typing G e T -> typing (ren_ctx G) e (ren_typ T)) /\
  (forall G fs R, field_typing G fs R -> field_typing (ren_ctx G) fs (ren_row R)).
Proof.
  apply typing_field_mutind; intros.
  - (* T_Var *) apply T_Var with (s := ren_sch s);
      [ apply uniq_ren_ctx; auto | apply binds_ren_ctx; auto | apply inst_ren; auto ].
  - apply T_Num; apply uniq_ren_ctx; auto.
  - apply T_NumFloat; apply uniq_ren_ctx; auto.
  - apply T_Dec; apply uniq_ren_ctx; auto.
  - apply T_True; apply uniq_ren_ctx; auto.
  - apply T_False; apply uniq_ren_ctx; auto.
  - (* T_Abs *) unfold ren_typ; simpl. apply T_Abs with (L := L).
    intros x Hx. specialize (H x Hx). rewrite ren_ctx_app in H.
    eapply typing_sch_equiv_ctx; [ exact H | ].
    apply ctx_equiv_cons; [ apply ren_sch_mono_equiv | apply ctx_equiv_refl ].
  - (* T_App *) unfold ren_typ in H; simpl in H. eapply T_App; [ exact H | exact H0 ].
  - (* T_Let *) unfold ren_typ; simpl. apply T_Let with (L := L) (T1 := ren_typ T1);
      [ exact H | ].
    intros x Hx. specialize (H0 x Hx).
    eapply typing_sch_equiv_ctx; [ exact H0 | ].
    apply ctx_equiv_cons; [ apply gen_ren | apply ctx_equiv_refl ].
  - (* T_Record *) unfold ren_typ; simpl. apply T_Record. exact H.
  - (* T_Proj *) unfold ren_typ, ren_row in H; simpl in H. eapply T_Proj. exact H.
  - (* T_Conv *) eapply T_Conv; [ exact H | apply teq_ap; auto ].
  - (* T_Unit *) apply T_Unit; apply uniq_ren_ctx; auto.
  - (* T_Str *) apply T_Str; apply uniq_ren_ctx; auto.
  - (* T_If *) unfold ren_typ in *; simpl in *. eapply T_If; eauto.
  - (* T_Bin: the signature's types are closed, so renaming leaves them alone *)
    unfold ren_typ in *.
    destruct (bin_sig_ap _ _ _ _ rt rr b) as [HA [HB HR]].
    rewrite HA in H. rewrite HB in H0. rewrite HR.
    eapply T_Bin; eauto.
  - apply FT_nil; apply uniq_ren_ctx; auto.
  - (* FT_cons *) unfold ren_row; simpl. eapply FT_cons; [ exact H | exact H0 ].
Qed.

Lemma typing_rename : forall G e T, typing G e T -> typing (ren_ctx G) e (ren_typ T).
Proof. apply typing_rename_mut. Qed.
End Renaming.

(* ================================================================== *)
(* Context free-variable bookkeeping, and generalization is antitone in  *)
(* the context: a smaller context (fewer free vars) generalizes more.    *)
(* ================================================================== *)

Lemma ftv_ctx_app : forall G1 G2,
  ftv_ctx (G1 ++ G2) [=] ftv_ctx G1 `union` ftv_ctx G2.
Proof. induction G1 as [|[x s] G1 IH]; simpl; intros; [ fsetdec | rewrite IH; fsetdec ]. Qed.

Lemma frv_ctx_app : forall G1 G2,
  frv_ctx (G1 ++ G2) [=] frv_ctx G1 `union` frv_ctx G2.
Proof. induction G1 as [|[x s] G1 IH]; simpl; intros; [ fsetdec | rewrite IH; fsetdec ]. Qed.

(* gen is antitone: dropping context free variables only quantifies more,
   so [gen G2 T] (the smaller context) is at least as general as [gen G1 T]
   and has no more free variables -- exactly [sch_more_gen] of the two. *)
Lemma gen_antimono : forall G1 G2 T,
  ftv_ctx G2 [<=] ftv_ctx G1 -> frv_ctx G2 [<=] frv_ctx G1 ->
  sch_more_gen (gen G1 T) (gen G2 T).
Proof.
  intros G1 G2 T Ht Hr.
  unfold sch_more_gen, Ftv_sch, Frv_sch, ftv_sch, frv_sch, gen; simpl.
  split; [|split].
  - intros W [st [sr [Hst [Hsr Heq]]]]. simpl in Hst, Hsr.
    exists st, sr; simpl; repeat split.
    + intros a Hna. apply Hst. simpl. fsetdec.
    + intros r Hnr. apply Hsr. simpl. fsetdec.
    + exact Heq.
  - intros a Hin. fsetdec.
  - intros r Hin. fsetdec.
Qed.

Lemma ctx_more_gen_refl : forall G, ctx_more_gen G G.
Proof. induction G as [|[x s] G IH]; constructor; simpl; auto using sch_more_gen_refl. Qed.
