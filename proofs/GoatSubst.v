(* Substitution metatheory toward closing L5/L6a/L6b (issue #151, finishing #71).

   This file develops the Hindley-Milner type/row-substitution theory that the
   two Admitted lemmas in GoatMeta.v (typing_subst = L6a, typing_subst_poly =
   L6b) rest on, over the hand-written type system of GoatDefs.v.  It is built
   AFTER GoatMeta.v (it reuses that file's [typing_field_mutind]); the soundness
   theorems do not yet draw on it -- see the roadmap at the admits in GoatMeta.v
   for exactly what remains.

   Proved here, fully (no axioms, no admits):

   - Type/row-substitution algebra: [ap_typ_pointwise_id], [ap_typ_ext],
     [ap_typ_comp], and the monotype-instance facts [inst_mono_eq] /
     [inst_mono_self].
   - [teq_ap]: type equivalence is closed under any type/row substitution
     (labels are untouched, so the swap rule survives).  This is the piece of L5
     the T-Conv case needs.
   - L4 (structural), two forms:
       * [typing_sch_equiv_ctx]: typing respects pointwise scheme-equivalence of
         the context (schemes equal up to their quantifier predicates).  This
         sidesteps the lack of functional extensionality for [scheme] equality.
       * [typing_ftv_mono]: typing is preserved when each context scheme is made
         more general AND mentions no more free variables ([ctx_more_gen]).  This
         is exactly what L6a's let case needs: removing x from the context makes
         [gen] more general with fewer free variables.
   - L5 for the renaming case: [typing_rename] -- typing is preserved by any
     bijective type/row-variable renaming, via [inst_ren] (instantiation
     commutes) and [gen_ren] (generalization commutes up to scheme-equivalence).

   What is NOT yet here (the research remainder tracked in #151):

   - General weakening under binders.  Its let case must freshen the
     let-generalized variables away from the inserted context's free variables
     (otherwise generalization silently shrinks and the derivation breaks); the
     freshening is a [typing_rename] with a bijection that fixes a finite set and
     moves the rest, which is a sub-development in its own right.
   - L5 for a GENERAL instantiating substitution (not a renaming), which L6b's
     [inst_gen_typing] step needs.  Because a scheme's quantifier sets are
     arbitrary Props (not decidable), capture-avoiding substitution of a context
     cannot be defined computationally for an arbitrary context, so this does not
     reduce to the renaming case.  See the DECISION note in the PR. *)

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
  - intros a. apply Ht. intro HF; exact HF.
  - intros r. apply Hr. intro HF; exact HF.
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
     (forall a, Ftv_typ T a -> st a = st' a) ->
     (forall r, Frv_typ T r -> sr r = sr' r) ->
     ap_typ st sr T = ap_typ st' sr' T) /\
  (forall R st sr st' sr',
     (forall a, Ftv_row R a -> st a = st' a) ->
     (forall r, Frv_row R r -> sr r = sr' r) ->
     ap_row st sr R = ap_row st' sr' R).
Proof.
  apply typ_row_mutind; intros; simpl in *; try reflexivity.
  - (* Arrow *) f_equal; [ apply H | apply H0 ]; intros; eauto.
  - (* Record *) f_equal; apply H; intros; eauto.
  - (* Var a *) apply H. reflexivity.
  - (* row_Var *) apply H0. reflexivity.
  - (* row_Ext *) f_equal; [ apply H | apply H0 ]; intros; eauto.
Qed.

Lemma ap_typ_ext : forall T st sr st' sr',
  (forall a, Ftv_typ T a -> st a = st' a) ->
  (forall r, Frv_typ T r -> sr r = sr' r) ->
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

(* scheme equivalence up to the quantifier predicates (no funext needed) *)
Definition sch_equiv (s s' : scheme) : Prop :=
  (forall a, s_tq s a <-> s_tq s' a) /\
  (forall r, s_rq s r <-> s_rq s' r) /\
  s_body s = s_body s'.

Lemma sch_equiv_refl : forall s, sch_equiv s s.
Proof. intros; repeat split; auto; tauto. Qed.

Lemma sch_equiv_sym : forall s s', sch_equiv s s' -> sch_equiv s' s.
Proof.
  intros s s' (A & B & C). split; [| split].
  - intro a0. specialize (A a0). tauto.
  - intro r0. specialize (B r0). tauto.
  - symmetry. exact C.
Qed.

(* inst respects sch_equiv *)
Lemma inst_sch_equiv : forall T s s',
  sch_equiv s s' -> inst T s -> inst T s'.
Proof.
  intros T s s' [Htq [Hrq Hbody]] [st [sr [Ht [Hr Heq]]]].
  exists st, sr. repeat split.
  - intros a Ha. apply Ht. intro Hc. apply Ha. apply Htq. exact Hc.
  - intros r Hr0. apply Hr. intro Hc. apply Hr0. apply Hrq. exact Hc.
  - rewrite <- Hbody. exact Heq.
Qed.

(* Ftv_sch respects sch_equiv *)
Lemma Ftv_sch_equiv : forall s s' a, sch_equiv s s' -> (Ftv_sch s a <-> Ftv_sch s' a).
Proof.
  intros s s' a [Htq [Hrq Hbody]]. unfold Ftv_sch. rewrite Hbody.
  split; intros [H1 H2]; split; auto; intro Hc; apply H2; apply Htq; auto.
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
  intros G G' a H. split; intros [x [s [Hb Hf]]].
  - destruct (ctx_equiv_binds _ _ _ _ H Hb) as [s' [Hb' Heq]].
    exists x, s'. split; auto. apply (Ftv_sch_equiv _ _ _ Heq); auto.
  - assert (H' : ctx_equiv G' G).
    { clear - H. induction H as [|[u su][v sv] ? ? [Hk Hs] ? IH]; constructor; auto.
      simpl in *; subst; split; auto using sch_equiv_sym. }
    destruct (ctx_equiv_binds _ _ _ _ H' Hb) as [s' [Hb' Heq]].
    exists x, s'. split; auto. apply (Ftv_sch_equiv _ _ _ Heq); auto.
Qed.

Lemma Frv_sch_equiv : forall s s' r, sch_equiv s s' -> (Frv_sch s r <-> Frv_sch s' r).
Proof.
  intros s s' r (Htq & Hrq & Hbody). unfold Frv_sch. rewrite Hbody.
  split; intros [H1 H2]; split; auto; intro Hc; apply H2; apply Hrq; auto.
Qed.

Lemma ctx_equiv_sym : forall G G', ctx_equiv G G' -> ctx_equiv G' G.
Proof.
  induction 1 as [|[u su][v sv] ? ? [Hk Hs] ? IH]; constructor; auto.
  simpl in *; subst; split; auto using sch_equiv_sym.
Qed.

Lemma ctx_equiv_Frv : forall G G' r,
  ctx_equiv G G' -> (Frv_ctx G r <-> Frv_ctx G' r).
Proof.
  intros G G' r H. split; intros [x [s [Hb Hf]]].
  - destruct (ctx_equiv_binds _ _ _ _ H Hb) as [s' [Hb' Heq]].
    exists x, s'. split; auto. apply (Frv_sch_equiv _ _ _ Heq); auto.
  - destruct (ctx_equiv_binds _ _ _ _ (ctx_equiv_sym _ _ H) Hb) as [s' [Hb' Heq]].
    exists x, s'. split; auto. apply (Frv_sch_equiv _ _ _ Heq); auto.
Qed.

(* generalization respects context equivalence *)
Lemma gen_ctx_equiv : forall G G' T,
  ctx_equiv G G' -> sch_equiv (gen G T) (gen G' T).
Proof.
  intros G G' T H. unfold gen, sch_equiv; simpl. split; [| split]; auto.
  - intro a. split; intros [HF HN]; split; auto;
      intro Hc; apply HN; [ apply (ctx_equiv_Ftv _ _ _ H) | apply (ctx_equiv_Ftv _ _ _ (ctx_equiv_sym _ _ H)) ]; auto.
  - intro r. split; intros [HF HN]; split; auto;
      intro Hc; apply HN; [ apply (ctx_equiv_Frv _ _ _ H) | apply (ctx_equiv_Frv _ _ _ (ctx_equiv_sym _ _ H)) ]; auto.
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
  - (* FT_nil *) apply FT_nil; eauto using ctx_equiv_uniq.
  - (* FT_cons *) eapply FT_cons; eauto.
Qed.

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

(* if G' mentions no more free vars than G (pointwise), then Ftv_ctx G' implies Ftv_ctx G *)
Lemma ctx_more_gen_Ftv : forall G G' a,
  ctx_more_gen G G' -> Ftv_ctx G' a -> Ftv_ctx G a.
Proof.
  intros G G' a H [x [s' [Hb' Hf']]].
  revert x s' Hb' Hf'. induction H as [|[y sy][z sz] G G' [Hk Hg] HF IH]; intros x s' Hb' Hf'.
  - inversion Hb'.
  - simpl in *; subst z. apply binds_cons_1 in Hb'. destruct Hb' as [[Hx Hs]|Hb'].
    + subst x. subst s'. exists y, sy. split; [apply binds_cons_2; auto|].
      destruct Hg as [_ [Hftv _]]. apply Hftv; exact Hf'.
    + destruct (IH _ _ Hb' Hf') as [u [su [Hbu Hfu]]].
      exists u, su. split; [apply binds_cons_3; auto|auto].
Qed.

Lemma ctx_more_gen_Frv : forall G G' r,
  ctx_more_gen G G' -> Frv_ctx G' r -> Frv_ctx G r.
Proof.
  intros G G' r H [x [s' [Hb' Hf']]].
  revert x s' Hb' Hf'. induction H as [|[y sy][z sz] G G' [Hk Hg] HF IH]; intros x s' Hb' Hf'.
  - inversion Hb'.
  - simpl in *; subst z. apply binds_cons_1 in Hb'. destruct Hb' as [[Hx Hs]|Hb'].
    + subst x. subst s'. exists y, sy. split; [apply binds_cons_2; auto|].
      destruct Hg as [_ [_ Hfrv]]. apply Hfrv; exact Hf'.
    + destruct (IH _ _ Hb' Hf') as [u [su [Hbu Hfu]]].
      exists u, su. split; [apply binds_cons_3; auto|auto].
Qed.

(* gen respects ctx_more_gen: fewer ctx free vars => more general & fewer scheme free vars *)
Lemma gen_more_gen : forall G G' T,
  ctx_more_gen G G' -> sch_more_gen (gen G T) (gen G' T).
Proof.
  intros G G' T H. unfold sch_more_gen, gen; simpl. split; [|split].
  - (* inst preserved: gen G' quantifies a superset *)
    intros W [st [sr [Ht [Hr Heq]]]]. exists st, sr. repeat split; auto.
    + intros a Hna. apply Ht. intro Hq. apply Hna. destruct Hq as [HF HN].
      split; auto. intro Hc. apply HN. apply (ctx_more_gen_Ftv _ _ _ H); auto.
    + intros r Hnr. apply Hr. intro Hq. apply Hnr. destruct Hq as [HF HN].
      split; auto. intro Hc. apply HN. apply (ctx_more_gen_Frv _ _ _ H); auto.
  - (* Ftv_sch(gen G' T) a -> Ftv_sch(gen G T) a *)
    intros a [HF HN]. split; auto. intro Hq. apply HN. destruct Hq as [HF2 HN2].
    split; auto. intro Hc. apply HN2. apply (ctx_more_gen_Ftv _ _ _ H); auto.
  - intros r [HF HN]. split; auto. intro Hq. apply HN. destruct Hq as [HF2 HN2].
    split; auto. intro Hc. apply HN2. apply (ctx_more_gen_Frv _ _ _ H); auto.
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

Lemma Ftv_ren_mut :
  (forall T a, Ftv_typ (ren_typ T) a <-> Ftv_typ T (g a)) /\
  (forall R a, Ftv_row (ren_row R) a <-> Ftv_row R (g a)).
Proof.
  unfold ren_typ, ren_row.
  apply typ_row_mutind; simpl; intros.
  - tauto.
  - tauto.
  - specialize (H a); specialize (H0 a); tauto.
  - apply H.
  - unfold rt; simpl; split;
      [ intro HH; rewrite HH; apply gf | intro HH; rewrite <- HH; symmetry; apply fg ].
  - tauto.
  - unfold rr; simpl. tauto.
  - specialize (H a); specialize (H0 a); tauto.
Qed.

Lemma Frv_ren_mut :
  (forall T r, Frv_typ (ren_typ T) r <-> Frv_typ T (gr r)) /\
  (forall R r, Frv_row (ren_row R) r <-> Frv_row R (gr r)).
Proof.
  unfold ren_typ, ren_row.
  apply typ_row_mutind; simpl; intros.
  - tauto.
  - tauto.
  - specialize (H r); specialize (H0 r); tauto.
  - apply H.
  - unfold rt; simpl. tauto.
  - tauto.
  - unfold rr; simpl; split;
      [ intro HH; rewrite HH; apply grfr | intro HH; rewrite <- HH; symmetry; apply frgr ].
  - specialize (H r); specialize (H0 r); tauto.
Qed.


Definition ren_sch (s:scheme) : scheme :=
  Sch (fun a => s_tq s (g a)) (fun r => s_rq s (gr r)) (ren_typ (s_body s)).
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
  intros s a. unfold Ftv_sch, ren_sch; simpl.
  pose proof (proj1 Ftv_ren_mut (s_body s) a) as HF.
  split.
  - intros [H1 H2]. split; [ apply (proj1 HF); exact H1 | exact H2 ].
  - intros [H1 H2]. split; [ apply (proj2 HF); exact H1 | exact H2 ].
Qed.

Lemma Frv_sch_ren : forall s r, Frv_sch (ren_sch s) r <-> Frv_sch s (gr r).
Proof.
  intros s r. unfold Frv_sch, ren_sch; simpl.
  pose proof (proj1 Frv_ren_mut (s_body s) r) as HF.
  split.
  - intros [H1 H2]. split; [ apply (proj1 HF); exact H1 | exact H2 ].
  - intros [H1 H2]. split; [ apply (proj2 HF); exact H1 | exact H2 ].
Qed.

Lemma Ftv_ctx_ren : forall G a, Ftv_ctx (ren_ctx G) a <-> Ftv_ctx G (g a).
Proof.
  intros G a. split.
  - intros [x [s [Hb Hf]]].
    (* binds in ren_ctx comes from a binding in G *)
    assert (exists s0, binds x s0 G /\ s = ren_sch s0) as [s0 [Hb0 Hs0]].
    { clear Hf. induction G as [|[y sy] G IH]; [inversion Hb|].
      apply binds_cons_1 in Hb. destruct Hb as [[Hx Hs]|Hb].
      - subst. exists sy. split; [apply binds_cons_2; auto|auto].
      - destruct (IH Hb) as [s0 [Hb0 Hs0]]. exists s0. split; [apply binds_cons_3; auto|auto]. }
    subst s. exists x, s0. split; auto. apply Ftv_sch_ren; auto.
  - intros [x [s0 [Hb0 Hf0]]]. exists x, (ren_sch s0). split.
    + apply binds_ren_ctx; auto.
    + apply Ftv_sch_ren; auto.
Qed.

Lemma Frv_ctx_ren : forall G r, Frv_ctx (ren_ctx G) r <-> Frv_ctx G (gr r).
Proof.
  intros G r. split.
  - intros [x [s [Hb Hf]]].
    assert (exists s0, binds x s0 G /\ s = ren_sch s0) as [s0 [Hb0 Hs0]].
    { clear Hf. induction G as [|[y sy] G IH]; [inversion Hb|].
      apply binds_cons_1 in Hb. destruct Hb as [[Hx Hs]|Hb].
      - subst. exists sy. split; [apply binds_cons_2; auto|auto].
      - destruct (IH Hb) as [s0 [Hb0 Hs0]]. exists s0. split; [apply binds_cons_3; auto|auto]. }
    subst s. exists x, s0. split; auto. apply Frv_sch_ren; auto.
  - intros [x [s0 [Hf0 Hf1]]]. exists x, (ren_sch s0). split.
    + apply binds_ren_ctx; auto.
    + apply Frv_sch_ren; auto.
Qed.

(* instantiation commutes with a bijective renaming *)
Lemma inst_ren : forall T s, inst T s -> inst (ren_typ T) (ren_sch s).
Proof.
  intros T s [st [sr [Ht [Hr Heq]]]].
  exists (fun c => ren_typ (st (g c))), (fun c => ren_row (sr (gr c))).
  unfold ren_sch; simpl. repeat split.
  - (* id off quantifier *)
    intros a Hna. unfold ren_typ. 
    assert (st (g a) = typ_Var (g a)) as Hid by (apply Ht; exact Hna).
    rewrite Hid. simpl. unfold rt. rewrite fg. reflexivity.
  - intros r Hnr. unfold ren_row.
    assert (sr (gr r) = row_Var (gr r)) as Hid by (apply Hr; exact Hnr).
    rewrite Hid. simpl. unfold rr. rewrite frgr. reflexivity.
  - (* ren_typ T = ap_typ (new) ... (ren_typ body) *)
    unfold ren_typ, ren_row. subst T.
    rewrite ap_typ_comp. rewrite ap_typ_comp.
    apply ap_typ_ext; intros; unfold tcomp, rcomp.
    + unfold rt. simpl. rewrite gf. reflexivity.
    + unfold rr. simpl. rewrite grfr. reflexivity.
Qed.


Lemma ren_sch_mono : forall T, ren_sch (sch_mono T) = sch_mono (ren_typ T).
Proof. reflexivity. Qed.

Lemma ren_ctx_app : forall x sx G,
  ren_ctx ((x ~ sx) ++ G) = (x ~ ren_sch sx) ++ ren_ctx G.
Proof. reflexivity. Qed.

(* generalization commutes with a bijective renaming (up to sch_equiv) *)
Lemma gen_ren : forall G T,
  sch_equiv (ren_sch (gen G T)) (gen (ren_ctx G) (ren_typ T)).
Proof.
  intros G T. unfold sch_equiv, ren_sch, gen; simpl. split; [|split]; [| |reflexivity].
  - intro a. split; intros [HF HN].
    + split.
      * apply (proj1 Ftv_ren_mut); auto.
      * intro Hc. apply HN. apply Ftv_ctx_ren; auto.
    + split.
      * apply (proj1 Ftv_ren_mut) in HF; auto.
      * intro Hc. apply HN. apply Ftv_ctx_ren; auto.
  - intro r. split; intros [HF HN].
    + split.
      * apply (proj1 Frv_ren_mut); auto.
      * intro Hc. apply HN. apply Frv_ctx_ren; auto.
    + split.
      * apply (proj1 Frv_ren_mut) in HF; auto.
      * intro Hc. apply HN. apply Frv_ctx_ren; auto.
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
  - apply T_True; apply uniq_ren_ctx; auto.
  - apply T_False; apply uniq_ren_ctx; auto.
  - (* T_Abs *) unfold ren_typ; simpl. apply T_Abs with (L := L).
    intros x Hx. apply (H x Hx).
  - (* T_App *) unfold ren_typ in H; simpl in H. eapply T_App; [ exact H | exact H0 ].
  - (* T_Let *) unfold ren_typ; simpl. apply T_Let with (L := L) (T1 := ren_typ T1);
      [ exact H | ].
    intros x Hx. specialize (H0 x Hx).
    eapply (proj1 typing_sch_equiv_ctx_mut); [ exact H0 | ].
    apply ctx_equiv_cons; [ apply gen_ren | apply ctx_equiv_refl ].
  - (* T_Record *) unfold ren_typ; simpl. apply T_Record. exact H.
  - (* T_Proj *) unfold ren_typ, ren_row in H; simpl in H. eapply T_Proj. exact H.
  - (* T_Conv *) eapply T_Conv; [ exact H | apply teq_ap; auto ].
  - apply FT_nil; apply uniq_ren_ctx; auto.
  - (* FT_cons *) unfold ren_row; simpl. eapply FT_cons; [ exact H | exact H0 ].
Qed.

Lemma typing_rename : forall G e T, typing G e T -> typing (ren_ctx G) e (ren_typ T).
Proof. apply typing_rename_mut. Qed.
End Renaming.
