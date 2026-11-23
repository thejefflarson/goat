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
   - Bijective type/row renamings ([ren_typ]) and their free-variable facts.
   - [gen_more_gen] / [ctx_more_gen]: generalization is antitone in the context,
     at the sorts the extra quantified atoms already had.
*)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Goat.GoatMeta.
Require Import Stdlib.Lists.List.

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
Lemma inst_mono_eq : forall D T U, inst D T (sch_mono U) -> T = U.
Proof.
  intros D T U [st [sr [Ht [Hr [Heq _]]]]]. simpl in *.
  rewrite Heq. apply ap_typ_pointwise_id.
  - intros a. apply Ht. simpl. fsetdec.
  - intros r. apply Hr. simpl. fsetdec.
Qed.

(* sch_mono is always an instance of itself *)
Lemma inst_mono_self : forall D U, inst D U (sch_mono U).
Proof.
  intros D U. exists idt, idr.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a _. reflexivity.
  - intros r _. reflexivity.
  - symmetry. apply ap_typ_pointwise_id; reflexivity.
  - intros a Ha. simpl in Ha. fsetdec.
  - intros r Hr. simpl in Hr. fsetdec.
  - apply lc_sub_id.
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
  - (* Mu *) f_equal. apply H; assumption.
  - (* Grp *) f_equal. apply H; assumption.
  - (* row_Var *) apply H0. fsetdec.
  - (* row_Ext *) f_equal; [ apply H | apply H0 ]; intros; [apply H1|apply H2|apply H1|apply H2]; fsetdec.
  - (* row_Maybe *) f_equal; [ apply H | apply H0 | apply H1 ]; intros;
      first [ apply H2 | apply H3 ]; fsetdec.
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
  s_tq s [=] s_tq s' /\ s_rq s [=] s_rq s' /\ s_body s = s_body s' /\
  (forall a, a `in` s_tq s -> s_sk s a = s_sk s' a) /\
  (forall r, r `in` s_rq s -> s_rk s r = s_rk s' r).

Lemma sch_equiv_refl : forall s, sch_equiv s s.
Proof.
  intros s. unfold sch_equiv.
  split; [|split; [|split; [|split]]]; [ fsetdec | fsetdec | reflexivity | intros; reflexivity | intros; reflexivity ].
Qed.

Lemma sch_equiv_sym : forall s s', sch_equiv s s' -> sch_equiv s' s.
Proof.
  intros s s' (A & B & C & E & F). unfold sch_equiv.
  split; [ fsetdec | split; [ fsetdec | split; [ congruence | split ] ] ].
  - intros a Ha. assert (a `in` s_tq s) by (apply A; exact Ha). symmetry. apply E. exact H.
  - intros r Hr. assert (r `in` s_rq s) by (apply B; exact Hr). symmetry. apply F. exact H.
Qed.

Lemma sch_equiv_trans : forall s1 s2 s3, sch_equiv s1 s2 -> sch_equiv s2 s3 -> sch_equiv s1 s3.
Proof.
  intros s1 s2 s3 (A1 & B1 & C1 & E1 & F1) (A2 & B2 & C2 & E2 & F2). unfold sch_equiv.
  split; [ fsetdec | split; [ fsetdec | split; [ congruence | split ] ] ].
  - intros a Ha. rewrite (E1 a Ha). apply E2. apply A1. exact Ha.
  - intros r Hr. rewrite (F1 r Hr). apply F2. apply B1. exact Hr.
Qed.

(* inst respects sch_equiv *)
Lemma inst_sch_equiv : forall D T s s',
  sch_equiv s s' -> inst D T s -> inst D T s'.
Proof.
  intros D T s s' [Htq [Hrq [Hbody [Hsk Hrk]]]] [st [sr [Ht [Hr [Heq [Hk [Hkr Hl]]]]]]].
  exists st, sr. split; [ | split; [ | split; [ | split; [ | split ] ] ] ].
  - intros a Ha. apply Ht. fsetdec.
  - intros r Hr0. apply Hr. fsetdec.
  - rewrite <- Hbody. exact Heq.
  - intros a Ha. assert (Hs : a `in` s_tq s) by (apply Htq; exact Ha).
    rewrite <- (Hsk a Hs). apply Hk. exact Hs.
  - intros q Hq0. assert (Hs : q `in` s_rq s) by (apply Hrq; exact Hq0).
    rewrite <- (Hrk q Hs). apply Hkr. exact Hs.
  - exact Hl.
Qed.

(* Ftv_sch respects sch_equiv *)
Lemma Ftv_sch_equiv : forall s s' a, sch_equiv s s' -> (Ftv_sch s a <-> Ftv_sch s' a).
Proof.
  intros s s' a (Htq & Hrq & Hbody & _). unfold Ftv_sch, ftv_sch. rewrite Hbody. fsetdec.
Qed.

Lemma Frv_sch_equiv : forall s s' r, sch_equiv s s' -> (Frv_sch s r <-> Frv_sch s' r).
Proof.
  intros s s' r (Htq & Hrq & Hbody & _). unfold Frv_sch, frv_sch. rewrite Hbody. fsetdec.
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
Lemma gen_ctx_equiv : forall G G' T k rk,
  ctx_equiv G G' -> sch_equiv (gen G T k rk) (gen G' T k rk).
Proof.
  intros G G' T k rk H. unfold sch_equiv, gen; simpl. split; [| split; [| split; [| split]]]; [| |reflexivity|intros; reflexivity|intros; reflexivity].
  - assert (ftv_ctx G [=] ftv_ctx G') by (intro z; apply (ctx_equiv_Ftv _ _ z H)).
    fsetdec.
  - assert (frv_ctx G [=] frv_ctx G') by (intro z; apply (ctx_equiv_Frv _ _ z H)).
    fsetdec.
Qed.

Lemma ctx_equiv_cons : forall x s s' G G',
  sch_equiv s s' -> ctx_equiv G G' -> ctx_equiv ((x ~ s) ++ G) ((x ~ s') ++ G').
Proof. intros. constructor; simpl; auto. Qed.

(* ================= typing depends on the kinding environment pointwise ===== *)

(* Two environments agree when they give every type variable one sort and
   every row variable one kind. *)
Definition denv_eq (D D2 : denv) : Prop :=
  (forall a, D a = D2 a) /\ (forall r, drk D r = drk D2 r).

Lemma denv_eq_refl : forall D, denv_eq D D.
Proof. intros D. split; intros; reflexivity. Qed.

Lemma ext_pw : forall D D2 V k, denv_eq D D2 -> denv_eq (ext D V k) (ext D2 V k).
Proof.
  intros D D2 V k [H1 H2]. split; intros a; unfold ext; simpl;
    [ destruct (AtomSetImpl.mem a V); auto | apply H2 ].
Qed.

Lemma extr_pw : forall D D2 V k, denv_eq D D2 -> denv_eq (extr D V k) (extr D2 V k).
Proof.
  intros D D2 V k [H1 H2]. split; intros a; unfold extr; simpl;
    [ apply H1 | destruct (AtomSetImpl.mem a V); auto ].
Qed.

Lemma extr_set_eq : forall D V V' rk, V [=] V' ->
  denv_eq (extr D V rk) (extr D V' rk).
Proof.
  intros D V V' rk H. split; [ intros; reflexivity | ]. intros r. unfold extr; simpl.
  destruct (AtomSetImpl.mem r V) eqn:E1, (AtomSetImpl.mem r V') eqn:E2; try reflexivity;
    exfalso;
    first [ apply AtomSetFacts.mem_iff in E1; apply AtomSetFacts.not_mem_iff in E2; apply E2; apply H; exact E1
          | apply AtomSetFacts.mem_iff in E2; apply AtomSetFacts.not_mem_iff in E1; apply E1; apply H; exact E2 ].
Qed.

Lemma ext_set_eq_d : forall D V V' k, V [=] V' -> denv_eq (ext D V k) (ext D V' k).
Proof.
  intros D V V' k H. split; [ | intros; reflexivity ]. intros a. unfold ext; simpl.
  destruct (AtomSetImpl.mem a V) eqn:E1, (AtomSetImpl.mem a V') eqn:E2; try reflexivity;
    exfalso;
    first [ apply AtomSetFacts.mem_iff in E1; apply AtomSetFacts.not_mem_iff in E2; apply E2; apply H; exact E1
          | apply AtomSetFacts.mem_iff in E2; apply AtomSetFacts.not_mem_iff in E1; apply E1; apply H; exact E2 ].
Qed.

Lemma denv_eq_sym : forall D D2, denv_eq D D2 -> denv_eq D2 D.
Proof. intros D D2 [H1 H2]. split; intros; [ symmetry; apply H1 | symmetry; apply H2 ]. Qed.

Lemma denv_eq_trans : forall D1 D2 D3, denv_eq D1 D2 -> denv_eq D2 D3 -> denv_eq D1 D3.
Proof. intros D1 D2 D3 [H1 H2] [H3 H4]. split; intros; [ rewrite H1; apply H3 | rewrite H2; apply H4 ]. Qed.

Lemma ext_set_eq : forall D V V' k, V [=] V' -> forall a, ext D V k a = ext D V' k a.
Proof.
  intros D V V' k H a. unfold ext. simpl.
  destruct (AtomSetImpl.mem a V) eqn:E1, (AtomSetImpl.mem a V') eqn:E2; auto.
  - apply AtomSetFacts.mem_iff in E1. apply AtomSetFacts.not_mem_iff in E2. exfalso. apply E2. apply H. exact E1.
  - apply AtomSetFacts.mem_iff in E2. apply AtomSetFacts.not_mem_iff in E1. exfalso. apply E1. apply H. exact E2.
Qed.

Lemma ext_in : forall D V k a, a `in` V -> ext D V k a = k a.
Proof.
  intros. unfold ext. simpl. destruct (AtomSetImpl.mem a V) eqn:E; [ reflexivity | ].
  apply AtomSetFacts.not_mem_iff in E. contradiction.
Qed.

Lemma ext_out : forall D V k a, a `notin` V -> ext D V k a = D a.
Proof.
  intros. unfold ext. simpl. destruct (AtomSetImpl.mem a V) eqn:E; [ | reflexivity ].
  apply AtomSetFacts.mem_iff in E. contradiction.
Qed.

Lemma extr_dsort : forall D V rk a, extr D V rk a = D a.
Proof. reflexivity. Qed.

Lemma ext_drk : forall D V k r, drk (ext D V k) r = drk D r.
Proof. reflexivity. Qed.

Lemma extr_in : forall D V rk r, r `in` V -> drk (extr D V rk) r = rk r.
Proof.
  intros. unfold extr. simpl. destruct (AtomSetImpl.mem r V) eqn:E; [ reflexivity | ].
  apply AtomSetFacts.not_mem_iff in E. contradiction.
Qed.

Lemma extr_out : forall D V rk r, r `notin` V -> drk (extr D V rk) r = drk D r.
Proof.
  intros. unfold extr. simpl. destruct (AtomSetImpl.mem r V) eqn:E; [ | reflexivity ].
  apply AtomSetFacts.mem_iff in E. contradiction.
Qed.

Lemma sat_pw_mut : forall D D2, denv_eq D D2 ->
  (forall T, (forall k, sat D k T -> sat D2 k T) /\
             (forall w j, spine_sat D w j T -> spine_sat D2 w j T)) /\
  (forall R k, rsat D k R -> rsat D2 k R).
Proof.
  intros D D2 [H Hr]. apply typ_row_mutind; simpl.
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - intros T1 [IH1 _] T2 [_ IH2]. split; [ intros; assumption | ].
    intros w j [Hu Hs]. split; [ intros Hc; exact (IH1 k_Eq (Hu Hc)) | exact (IH2 w (S j) Hs) ].
  - intros R IH. split; [ | intros; contradiction ]. intros k. destruct k; simpl;
      first [ (intros _; exact I) | (intros HH; contradiction) | exact (IH _) ].
  - intros a. split; [ intros k Hs; rewrite <- H; exact Hs | intros; contradiction ].
  - intros i. split; intros; first [ assumption | contradiction ].
  - intros B IH. split; [ | intros; contradiction ]. intros k Hs. destruct k; try exact I; try contradiction.
    exact (proj1 IH k_Eq Hs).
  - intros w A IH. split; [ | intros; contradiction ]. intros k Hs. destruct k; try exact I; try contradiction.
    exact (proj2 IH w 0 Hs).
  - intros k _. exact I.
  - intros r k Hs. rewrite <- Hr. exact Hs.
  - intros l T [IHT _] R IHR k [Hs1 Hs2]. split; [ exact (IHT k Hs1) | exact (IHR k Hs2) ].
  - intros l P _ T [IHT _] R IHR k [Hs1 Hs2]. split;
      [ destruct Hs1 as [Hp | Hs1]; [ left; exact Hp | right; exact (IHT k Hs1) ]
      | exact (IHR k Hs2) ].
Qed.

Lemma sat_pw : forall D D2 k T, denv_eq D D2 -> sat D k T -> sat D2 k T.
Proof. intros D D2 k T H Hs. exact (proj1 (proj1 (sat_pw_mut D D2 H) T) k Hs). Qed.

Lemma rsat_pw : forall D D2 k R, denv_eq D D2 -> rsat D k R -> rsat D2 k R.
Proof. intros D D2 k R H Hs. exact (proj2 (sat_pw_mut D D2 H) R k Hs). Qed.

Lemma rlacksD_pw : forall D D2 l R, denv_eq D D2 -> rlacksD D l R = rlacksD D2 l R.
Proof.
  intros D D2 l R [_ Hr]. induction R as [|r|l' T R IH|l' P T R IH]; simpl; auto;
    [ rewrite Hr; reflexivity | rewrite IH; reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma rkok_pw : forall D D2 K R, denv_eq D D2 -> rkok D K R -> rkok D2 K R.
Proof.
  intros D D2 K R H [H1 H2]. split; [ eapply rsat_pw; eauto | ].
  intros l Hl. rewrite <- (rlacksD_pw D D2 l R H). apply H2. exact Hl.
Qed.

Lemma inst_pw : forall D D2 T s, denv_eq D D2 -> inst D T s -> inst D2 T s.
Proof.
  intros D D2 T s H [st [sr [A [B [C [E [Er Hl]]]]]]]. exists st, sr.
  split; [ exact A | split; [ exact B | split; [ exact C | split; [ | split; [ | exact Hl ] ] ] ] ].
  - intros a Ha. eapply sat_pw; eauto.
  - intros r Hr. eapply rkok_pw; eauto.
Qed.

Lemma bin_sig_pw : forall D D2 o A B R, denv_eq D D2 -> bin_sig D o A B R -> bin_sig D2 o A B R.
Proof.
  intros D D2 o A B R H Hs. destruct Hs.
  - apply sig_ring; [ assumption | eapply sat_pw; eauto ].
  - apply sig_quot.
  - apply sig_whole; [ assumption | eapply sat_pw; eauto ].
  - apply sig_quot_rec; assumption.
  - apply sig_cmp; [ assumption | eapply sat_pw; eauto ].
Qed.

Lemma typing_pw_mut :
  (forall D G e T, typing D G e T -> forall D2, denv_eq D D2 -> typing D2 G e T) /\
  (forall D G fs R, field_typing D G fs R -> forall D2, denv_eq D D2 -> field_typing D2 G fs R).
Proof.
  apply typing_field_mutind; intros.
  - eapply T_Var; eauto. eapply inst_pw; eauto.
  - apply T_Num; auto. eapply sat_pw; eauto.
  - apply T_Dec; auto.
  - apply T_True; auto.
  - apply T_False; auto.
  - eapply T_Abs with (L := L). intros. eauto.
  - eapply T_App; eauto.
  - eapply T_Let with (L := L) (k := k) (rk := rk) (Tm := Tm);
      [ assumption | eassumption | apply H; apply extr_pw; apply ext_pw; assumption | intros; eauto ].
  - eapply T_LetMono with (L := L); eauto.
  - eapply T_Letrec with (L := L) (k := k) (rk := rk); [ assumption | | intros; eauto ].
    intros p Hp. apply H; auto. apply extr_pw. apply ext_pw. auto.
  - apply T_Record; eauto.
  - eapply T_Obj; eauto.
  - eapply T_Proj; eauto.
  - eapply T_Conv; eauto.
  - apply T_Unit; auto.
  - apply T_Str; auto.
  - eapply T_If; eauto.
  - eapply T_ToFloat; eauto. eapply sat_pw; eauto.
  - eapply T_Bin; eauto. eapply bin_sig_pw; eauto.
  - eapply T_Spread; eauto.
  - eapply T_SpreadL; eauto. rewrite <- (rlacksD_pw D D2 l R); auto.
  - eapply T_Restrict; eauto.
  - eapply T_Fold; eauto.
  - eapply T_Unfold; eauto.
  - eapply T_Con; eauto.
  - eapply T_Match with (L := L); intros; eauto.
  - apply FT_nil; auto.
  - eapply FT_cons; eauto.
  - eapply FT_meth; eauto.
Qed.

Lemma typing_pw : forall D G e T D2, typing D G e T -> denv_eq D D2 -> typing D2 G e T.
Proof. intros. eapply (proj1 typing_pw_mut); eauto. Qed.

Lemma field_typing_pw : forall D G fs R D2, field_typing D G fs R -> denv_eq D D2 -> field_typing D2 G fs R.
Proof. intros. eapply (proj2 typing_pw_mut); eauto. Qed.

(* typing respects pointwise scheme-equivalence of the context *)
Lemma typing_sch_equiv_ctx_mut :
  (forall D G e T, typing D G e T -> forall G', ctx_equiv G G' -> typing D G' e T) /\
  (forall D G fs R, field_typing D G fs R -> forall G', ctx_equiv G G' -> field_typing D G' fs R).
Proof.
  apply typing_field_mutind; intros.
  - (* T_Var *) destruct (ctx_equiv_binds _ _ _ _ H b) as [s' [Hb' Heq]].
    apply T_Var with (s := s'); eauto using ctx_equiv_uniq, inst_sch_equiv.
  - (* T_Num *) apply T_Num; eauto using ctx_equiv_uniq.
  - (* T_Dec *) apply T_Dec; eauto using ctx_equiv_uniq.
  - (* T_True *) apply T_True; eauto using ctx_equiv_uniq.
  - (* T_False *) apply T_False; eauto using ctx_equiv_uniq.
  - (* T_Abs *) apply T_Abs with (L := L); intros x Hx.
    apply H; auto. apply ctx_equiv_cons; auto using sch_equiv_refl.
  - (* T_App *) eapply T_App; eauto.
  - (* T_Let *)
    assert (Hf : ftv_ctx G [=] ftv_ctx G') by (intro z; apply (ctx_equiv_Ftv _ _ z H1)).
    assert (Hfr : frv_ctx G [=] frv_ctx G') by (intro z; apply (ctx_equiv_Frv _ _ z H1)).
    apply T_Let with (L := L) (T1 := T1) (k := k) (rk := rk) (Tm := Tm); auto.
    + intros Hc a Ha. apply (l Hc a). rewrite !ftv_pin_ctx in *. fsetdec.
    + eapply typing_pw; [ apply H; exact H1 | ].
      apply denv_eq_trans with (D2 := extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G'))) k)
                                 (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G))) rk).
      * apply extr_pw. apply ext_set_eq_d. rewrite !ftv_pin_ctx, Hf. reflexivity.
      * apply extr_set_eq. rewrite !frv_pin_ctx, Hfr. reflexivity.
    + intros x Hx. apply H0; auto.
      apply ctx_equiv_cons; auto. apply gen_ctx_equiv; auto.
      unfold pin_ctx. apply ctx_equiv_cons; [ apply sch_equiv_refl | exact H1 ].
  - (* T_LetMono *) apply T_LetMono with (L := L) (T1 := T1); auto.
    intros x Hx. apply H0; auto.
    apply ctx_equiv_cons; auto using sch_equiv_refl.
  - (* T_Letrec *) apply T_Letrec with (L := L) (R := R) (k := k) (rk := rk); auto.
    + intros p Hp. eapply field_typing_pw.
      * apply H; auto. apply ctx_equiv_cons; auto using sch_equiv_refl.
      * match goal with Hc : ctx_equiv G G' |- _ =>
          assert (Hf : ftv_ctx G [=] ftv_ctx G') by (intro z; apply (ctx_equiv_Ftv _ _ z Hc));
          assert (Hfr : frv_ctx G [=] frv_ctx G') by (intro z; apply (ctx_equiv_Frv _ _ z Hc));
          apply denv_eq_trans with (D2 := extr (ext D (AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G')) k)
                                 (AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G)) rk);
          [ apply extr_pw; apply ext_set_eq_d; rewrite Hf; reflexivity
          | apply extr_set_eq; rewrite Hfr; reflexivity ] end.
    + intros p Hp. apply H0; auto.
      apply ctx_equiv_cons; auto. apply gen_ctx_equiv; auto.
  - (* T_Record *) apply T_Record; eauto.
  - eapply T_Obj; eauto.
  - (* T_Proj *) eapply T_Proj; eauto.
  - (* T_Conv *) eapply T_Conv; eauto.
  - (* T_Unit *) apply T_Unit; eauto using ctx_equiv_uniq.
  - (* T_Str *) apply T_Str; eauto using ctx_equiv_uniq.
  - (* T_If *) eapply T_If; eauto.
  - (* T_ToFloat *) eapply T_ToFloat; eauto.
  - (* T_Bin *) eapply T_Bin; eauto.
  - (* T_Spread *) eapply T_Spread; eauto.
  - (* T_SpreadL *) eapply T_SpreadL; eauto.
  - (* T_Restrict *) eapply T_Restrict; eauto.
  - (* T_Fold *) eapply T_Fold; eauto.
  - (* T_Unfold *) eapply T_Unfold; eauto.
  - (* T_Con *) eapply T_Con; eauto.
  - (* T_Match *) eapply T_Match with (L := L); [ eauto | assumption | | intros e0 Hd; eauto ].
    intros tg b Hf x Hx. eapply (H0 tg b Hf x Hx).
    apply ctx_equiv_cons; auto using sch_equiv_refl.
  - (* FT_nil *) apply FT_nil; eauto using ctx_equiv_uniq.
  - (* FT_cons *) eapply FT_cons; eauto.
  - eapply FT_meth; eauto.
Qed.

Lemma typing_sch_equiv_ctx : forall D G G' e T,
  typing D G e T -> ctx_equiv G G' -> typing D G' e T.
Proof. intros. eapply (proj1 typing_sch_equiv_ctx_mut); eauto. Qed.

(* A [let] that generalizes every variable the context does not mention: the
   rule with the unit type pinning nothing. *)
Lemma T_Let_nopin : forall (L : vars) D G e1 e2 T1 T2 (k : sort_fn) (rk : rkind_fn),
  is_gen_value e1 = true ->
  lit_pinned e1 (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx G)) k ->
  typing (extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx G)) k)
               (AtomSetImpl.diff (frv_typ T1) (frv_ctx G)) rk) G e1 T1 ->
  (forall x, x `notin` L ->
     typing D ((x ~ gen G T1 k rk) ++ G) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
  typing D G (e_let e1 e2) T2.
Proof.
  intros L D G e1 e2 T1 T2 k rk Hg Hlp H1 H2.
  apply T_Let with (L := L) (T1 := T1) (k := k) (rk := rk) (Tm := typ_Unit); [ exact Hg | | | ].
  - intros Hc a Ha. apply Hlp; [ exact Hc | ]. rewrite ftv_pin_ctx in Ha. simpl in Ha. fsetdec.
  - eapply typing_pw; [ exact H1 | ].
    apply denv_eq_trans with (D2 := extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx typ_Unit G))) k)
                 (AtomSetImpl.diff (frv_typ T1) (frv_ctx G)) rk).
    + apply extr_pw. apply ext_set_eq_d. rewrite ftv_pin_ctx. simpl. fsetdec.
    + apply extr_set_eq. rewrite frv_pin_ctx. simpl. fsetdec.
  - intros x Hx. eapply typing_sch_equiv_ctx; [ apply H2; exact Hx | ].
    apply ctx_equiv_cons; [ | apply ctx_equiv_refl ].
    unfold sch_equiv, gen. cbn [s_tq s_rq s_body s_sk s_rk].
    rewrite ftv_pin_ctx, frv_pin_ctx. simpl.
    split; [ | split; [ | split; [ reflexivity | split; intros; reflexivity ] ] ]; fsetdec.
Qed.

(* ============ more general schemes and contexts (kinded) ============ *)

(* The sort function that keeps [k] on [V] and the environment's own sorts
   elsewhere: a generalization over a wider set [V'] quantifies the extra
   atoms at the sorts they already had. *)
Definition kup (D : denv) (V : atoms) (k : sort_fn) : sort_fn :=
  fun a => if AtomSetImpl.mem a V then k a else D a.

Lemma ext_kup : forall D V V' k, V [<=] V' ->
  forall a, ext D V k a = ext D V' (kup D V k) a.
Proof.
  intros D V V' k Hs a. unfold ext, kup. simpl.
  destruct (AtomSetImpl.mem a V) eqn:E1, (AtomSetImpl.mem a V') eqn:E2; try reflexivity.
  apply AtomSetFacts.mem_iff in E1. apply AtomSetFacts.not_mem_iff in E2.
  exfalso. apply E2. apply Hs. exact E1.
Qed.

Lemma ext_kup_d : forall D V V' k, V [<=] V' -> denv_eq (ext D V k) (ext D V' (kup D V k)).
Proof.
  intros D V V' k Hs. split; [ apply ext_kup; exact Hs | intros; reflexivity ].
Qed.

(* The row-variable analogue of [kup]. *)
Definition rkup (D : denv) (Vr : atoms) (rk : rkind_fn) : rkind_fn :=
  fun r => if AtomSetImpl.mem r Vr then rk r else drk D r.

Lemma extr_rkup : forall D0 D V V' rk, (forall r, drk D0 r = drk D r) -> V [<=] V' ->
  denv_eq (extr D0 V rk) (extr D0 V' (rkup D V rk)).
Proof.
  intros D0 D V V' rk Hd Hs. split; [ intros; reflexivity | ]. intros r. unfold extr, rkup; simpl.
  destruct (AtomSetImpl.mem r V) eqn:E1, (AtomSetImpl.mem r V') eqn:E2; try reflexivity.
  - apply AtomSetFacts.mem_iff in E1. apply AtomSetFacts.not_mem_iff in E2.
    exfalso. apply E2. apply Hs. exact E1.
  - apply Hd.
Qed.

Lemma lit_pinned_kup : forall D e V V' k,
  lit_pinned e V k -> V' [<=] V -> lit_pinned e V' (kup D V k).
Proof.
  intros D e V V' k Hp Hs Hc a Ha. unfold kup.
  assert (Hm : AtomSetImpl.mem a V = true) by (apply AtomSetFacts.mem_iff; apply Hs; exact Ha).
  rewrite Hm. apply Hp; [ exact Hc | apply Hs; exact Ha ].
Qed.

Lemma typ_with_ftv : forall S : atoms, exists T, ftv_typ T [=] S /\ frv_typ T [=] {}.
Proof.
  intros S. induction S using AtomSetProperties.set_induction.
  - exists typ_Unit. split; simpl; [ | reflexivity ].
    intro a. split; intro Ha; [ exfalso; fsetdec | exfalso; apply (H a); exact Ha ].
  - destruct IHS1 as [T [Hf Hr]]. exists (typ_Arrow (typ_Var x) T). simpl.
    split; [ | rewrite Hr; fsetdec ].
    intro a. rewrite AtomSetFacts.union_iff, AtomSetFacts.singleton_iff, (Hf a).
    pose proof (H0 a) as Ha. split; intro H1.
    + destruct H1 as [->|H1]; [ apply Ha; left; reflexivity | apply Ha; right; exact H1 ].
    + apply Ha in H1. destruct H1 as [->|H1]; [ left; reflexivity | right; exact H1 ].
Qed.

(* Shrinking a context: a type standing in for the old context's variables
   keeps them pinned. *)
Lemma repin : forall Tm G G',
  ftv_ctx G' [<=] ftv_ctx G -> frv_ctx G' [<=] frv_ctx G ->
  exists Tm', ftv_ctx (pin_ctx Tm' G') [=] ftv_ctx (pin_ctx Tm G) /\
              frv_ctx (pin_ctx Tm' G') [<=] frv_ctx (pin_ctx Tm G).
Proof.
  intros Tm G G' Hf Hr.
  destruct (typ_with_ftv (ftv_ctx (pin_ctx Tm G))) as [T [Ht Hv]].
  exists T. rewrite !ftv_pin_ctx, !frv_pin_ctx in *. rewrite Hv, Ht. split; fsetdec.
Qed.

(* [s'] is at least as general as [s]: it quantifies at least the same
   variables over the same body, at the same sorts, and any variable it
   quantifies extra is free in [s] and has its sort from [D]. *)
Definition sch_more_gen (D : denv) (s s' : scheme) : Prop :=
  s_tq s [<=] s_tq s' /\ s_rq s [<=] s_rq s' /\ s_body s = s_body s' /\
  (forall a, a `in` s_tq s -> s_sk s' a = s_sk s a) /\
  (forall a, a `in` s_tq s' -> a `notin` s_tq s ->
     a `in` ftv_sch s /\ s_sk s' a = D a) /\
  (forall r, r `in` s_rq s -> s_rk s' r = s_rk s r) /\
  (forall r, r `in` s_rq s' -> r `notin` s_rq s ->
     r `in` frv_sch s /\ s_rk s' r = drk D r).

Lemma sch_more_gen_refl : forall D s, sch_more_gen D s s.
Proof.
  intros D s. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - fsetdec.
  - fsetdec.
  - reflexivity.
  - intros; reflexivity.
  - intros a Ha Hn. exfalso. apply Hn. exact Ha.
  - intros; reflexivity.
  - intros r Hr Hn. exfalso. apply Hn. exact Hr.
Qed.

(* The kinds that [sch_more_gen] reads from the environment are the ones of
   the scheme's free variables, so an environment that agrees on them will do. *)
Lemma sch_more_gen_env : forall (D D' : denv) s s',
  (forall a, a `in` ftv_sch s -> D' a = D a) ->
  (forall r, r `in` frv_sch s -> drk D' r = drk D r) ->
  sch_more_gen D s s' -> sch_more_gen D' s s'.
Proof.
  intros D D' s s' Hv Hvr (A & B & C & E & F & G & H).
  refine (conj A (conj B (conj C (conj E (conj _ (conj G _)))))).
  - intros a Ha Hn. destruct (F a Ha Hn) as [Hf Hs]. split; [ exact Hf | ].
    rewrite Hs. symmetry. apply Hv. exact Hf.
  - intros r Hr Hn. destruct (H r Hr Hn) as [Hf Hs]. split; [ exact Hf | ].
    rewrite Hs. symmetry. apply Hvr. exact Hf.
Qed.

Lemma sch_more_gen_ext : forall D V k s s',
  (forall a, a `in` ftv_sch s -> a `notin` V) ->
  sch_more_gen D s s' -> sch_more_gen (ext D V k) s s'.
Proof.
  intros D V k s s' Hv H. eapply sch_more_gen_env; [ | | exact H ].
  - intros a Ha. apply ext_out. apply Hv. exact Ha.
  - intros r Hr. reflexivity.
Qed.

Lemma sch_more_gen_extr : forall D V rk s s',
  (forall r, r `in` frv_sch s -> r `notin` V) ->
  sch_more_gen D s s' -> sch_more_gen (extr D V rk) s s'.
Proof.
  intros D V rk s s' Hv H. eapply sch_more_gen_env; [ | | exact H ].
  - intros a Ha. reflexivity.
  - intros r Hr. unfold extr; simpl.
    destruct (AtomSetImpl.mem r V) eqn:Em; [ | reflexivity ].
    apply AtomSetFacts.mem_iff in Em. exfalso. apply (Hv r Hr). exact Em.
Qed.

Lemma sch_more_gen_inst : forall D s s' W,
  sch_more_gen D s s' -> inst D W s -> inst D W s'.
Proof.
  intros D s s' W (A & B & C & E & F & G & H) [st [sr [Ht [Hr [Hw [Hk [Hkr Hl]]]]]]].
  exists st, sr. split; [ | split; [ | split; [ | split; [ | split ] ] ] ].
  - intros a Ha. apply Ht. intro Hc. apply Ha. apply A. exact Hc.
  - intros r Hrr. apply Hr. intro Hc. apply Hrr. apply B. exact Hc.
  - rewrite <- C. exact Hw.
  - intros a Ha. destruct (AtomSetProperties.In_dec a (s_tq s)) as [Hin|Hn].
    + rewrite (E a Hin). apply Hk. exact Hin.
    + destruct (F a Ha Hn) as [_ Hs]. rewrite Hs. rewrite (Ht a Hn). simpl. apply finer_refl.
  - intros r Hrr. destruct (AtomSetProperties.In_dec r (s_rq s)) as [Hin|Hn].
    + rewrite (G r Hin). apply Hkr. exact Hin.
    + destruct (H r Hrr Hn) as [_ Hs]. rewrite Hs. rewrite (Hr r Hn). simpl.
      apply rkok_self.
  - exact Hl.
Qed.

Definition ctx_more_gen (D : denv) (G G' : ctx) : Prop :=
  Forall2 (fun b b' => fst b = fst b' /\ sch_more_gen D (snd b) (snd b')) G G'.

Lemma ctx_more_gen_dom : forall D G G', ctx_more_gen D G G' -> dom G [=] dom G'.
Proof.
  induction 1 as [|[x s][y s'] G G' [Hk He] HF IH]; simpl in *; [reflexivity|].
  subst y. rewrite IH. reflexivity.
Qed.

Lemma ctx_more_gen_uniq : forall D G G', ctx_more_gen D G G' -> uniq G -> uniq G'.
Proof.
  induction 1 as [|[x s][y s'] G G' [Hk He] HF IH]; intros Hu; auto.
  simpl in *; subst y. inversion Hu; subst.
  constructor; auto. rewrite <- (ctx_more_gen_dom _ _ _ HF); auto.
Qed.

Lemma ctx_more_gen_binds : forall D G G' x s,
  ctx_more_gen D G G' -> binds x s G ->
  exists s', binds x s' G' /\ sch_more_gen D s s'.
Proof.
  induction 1 as [|[y sy][z sz] G G' [Hk He] HF IH]; intros Hb; [inversion Hb|].
  simpl in *; subst z. apply binds_cons_1 in Hb. destruct Hb as [[Hx Hs]|Hb].
  - subst. exists sz. split; [apply binds_cons_2; auto|auto].
  - destruct (IH Hb) as [s' [Hb' Hg']]. exists s'. split; [apply binds_cons_3; auto|auto].
Qed.

Lemma sch_more_gen_ftv : forall D s s' a,
  sch_more_gen D s s' -> Ftv_sch s' a -> Ftv_sch s a.
Proof.
  intros D s s' a (A & B & C & _) H. unfold Ftv_sch, ftv_sch in *. rewrite C. fsetdec.
Qed.

Lemma sch_more_gen_frv : forall D s s' r,
  sch_more_gen D s s' -> Frv_sch s' r -> Frv_sch s r.
Proof.
  intros D s s' r (A & B & C & _) H. unfold Frv_sch, frv_sch in *. rewrite C. fsetdec.
Qed.

Lemma ctx_more_gen_Ftv : forall D G G' a,
  ctx_more_gen D G G' -> Ftv_ctx G' a -> Ftv_ctx G a.
Proof.
  unfold Ftv_ctx. induction 1 as [|[y sy][z sz] G G' [Hk Hg] HF IH]; simpl; intros Hin.
  - fsetdec.
  - rewrite AtomSetFacts.union_iff in Hin |- *.
    destruct Hin as [Hin|Hin];
      [ left; exact (sch_more_gen_ftv _ _ _ _ Hg Hin) | right; apply IH; exact Hin ].
Qed.

Lemma ctx_more_gen_Frv : forall D G G' r,
  ctx_more_gen D G G' -> Frv_ctx G' r -> Frv_ctx G r.
Proof.
  unfold Frv_ctx. induction 1 as [|[y sy][z sz] G G' [Hk Hg] HF IH]; simpl; intros Hin.
  - fsetdec.
  - rewrite AtomSetFacts.union_iff in Hin |- *.
    destruct Hin as [Hin|Hin];
      [ left; exact (sch_more_gen_frv _ _ _ _ Hg Hin) | right; apply IH; exact Hin ].
Qed.

Lemma ctx_more_gen_cons : forall D x s s' G G',
  sch_more_gen D s s' -> ctx_more_gen D G G' -> ctx_more_gen D ((x ~ s) ++ G) ((x ~ s') ++ G').
Proof. intros. constructor; simpl; auto. Qed.

Lemma ctx_more_gen_refl : forall D G, ctx_more_gen D G G.
Proof. induction G as [|[x s] G IH]; constructor; simpl; auto using sch_more_gen_refl. Qed.

(* Extending the environment on atoms the context never mentions leaves
   "more general" intact. *)
Lemma ctx_more_gen_ext : forall D V k G G',
  (forall a, a `in` ftv_ctx G -> a `notin` V) ->
  ctx_more_gen D G G' -> ctx_more_gen (ext D V k) G G'.
Proof.
  intros D V k G G' Hv H. revert Hv.
  induction H as [|[y sy][z sz] G G' [Hk Hg] HF IH]; intros Hv; constructor.
  - simpl. split; [ exact Hk | ]. apply sch_more_gen_ext; [ | exact Hg ].
    intros a Ha. apply Hv. simpl. fsetdec.
  - apply IH. intros a Ha. apply Hv. simpl. fsetdec.
Qed.

Lemma ctx_more_gen_extr : forall D V rk G G',
  (forall r, r `in` frv_ctx G -> r `notin` V) ->
  ctx_more_gen D G G' -> ctx_more_gen (extr D V rk) G G'.
Proof.
  intros D V rk G G' Hv H. revert Hv.
  induction H as [|[y sy][z sz] G G' [Hk Hg] HF IH]; intros Hv; constructor.
  - simpl. split; [ exact Hk | ]. apply sch_more_gen_extr; [ | exact Hg ].
    intros a Ha. apply Hv. simpl. fsetdec.
  - apply IH. intros a Ha. apply Hv. simpl. fsetdec.
Qed.

(* Generalizing over a smaller context quantifies more, at the sorts and
   kinds the atoms already had. *)
Lemma gen_more_gen : forall D G1 G2 T k rk,
  ftv_ctx G2 [<=] ftv_ctx G1 -> frv_ctx G2 [<=] frv_ctx G1 ->
  sch_more_gen D (gen G1 T k rk)
    (gen G2 T (kup D (AtomSetImpl.diff (ftv_typ T) (ftv_ctx G1)) k)
              (rkup D (AtomSetImpl.diff (frv_typ T) (frv_ctx G1)) rk)).
Proof.
  intros D G1 G2 T k rk Ht Hr. unfold sch_more_gen, gen; simpl.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - fsetdec.
  - fsetdec.
  - reflexivity.
  - intros a Ha. unfold kup.
    assert (Hm : AtomSetImpl.mem a (AtomSetImpl.diff (ftv_typ T) (ftv_ctx G1)) = true)
      by (apply AtomSetFacts.mem_iff; exact Ha).
    rewrite Hm. reflexivity.
  - intros a Ha Hn. split.
    + unfold ftv_sch; simpl. apply AtomSetFacts.diff_iff in Ha as [HaT _].
      apply AtomSetFacts.diff_iff. split; [ exact HaT | exact Hn ].
    + unfold kup.
      destruct (AtomSetImpl.mem a (AtomSetImpl.diff (ftv_typ T) (ftv_ctx G1))) eqn:Em;
        [ apply AtomSetFacts.mem_iff in Em; contradiction | reflexivity ].
  - intros r Hrr. unfold rkup.
    assert (Hm : AtomSetImpl.mem r (AtomSetImpl.diff (frv_typ T) (frv_ctx G1)) = true)
      by (apply AtomSetFacts.mem_iff; exact Hrr).
    rewrite Hm. reflexivity.
  - intros r Hrr Hn. split.
    + unfold frv_sch; simpl. apply AtomSetFacts.diff_iff in Hrr as [HrT _].
      apply AtomSetFacts.diff_iff. split; [ exact HrT | exact Hn ].
    + unfold rkup.
      destruct (AtomSetImpl.mem r (AtomSetImpl.diff (frv_typ T) (frv_ctx G1))) eqn:Em;
        [ apply AtomSetFacts.mem_iff in Em; contradiction | reflexivity ].
Qed.

Lemma typing_ftv_mono_mut :
  (forall D G e T, typing D G e T -> forall G', ctx_more_gen D G G' -> typing D G' e T) /\
  (forall D G fs R, field_typing D G fs R -> forall G', ctx_more_gen D G G' -> field_typing D G' fs R).
Proof.
  apply typing_field_mutind; intros.
  - (* T_Var *) destruct (ctx_more_gen_binds _ _ _ _ _ H b) as [s' [Hb' Hg]].
    apply T_Var with (s := s'); eauto using ctx_more_gen_uniq, sch_more_gen_inst.
  - apply T_Num; eauto using ctx_more_gen_uniq.
  - apply T_Dec; eauto using ctx_more_gen_uniq.
  - apply T_True; eauto using ctx_more_gen_uniq.
  - apply T_False; eauto using ctx_more_gen_uniq.
  - (* T_Abs *) apply T_Abs with (L := L); intros x Hx.
    apply H; auto. apply ctx_more_gen_cons; auto using sch_more_gen_refl.
  - eapply T_App; eauto.
  - (* T_Let *)
    assert (HV : forall a, a `in` ftv_ctx G -> a `notin` AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G)))
      by (intros a Ha Hd; apply AtomSetFacts.diff_iff in Hd; rewrite ftv_pin_ctx in Hd; fsetdec).
    assert (HVr : forall a, a `in` frv_ctx G -> a `notin` AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G)))
      by (intros a Ha Hd; apply AtomSetFacts.diff_iff in Hd; rewrite frv_pin_ctx in Hd; fsetdec).
    assert (HF : ftv_ctx G' [<=] ftv_ctx G) by (intros a Ha; eapply ctx_more_gen_Ftv; eauto).
    assert (HR : frv_ctx G' [<=] frv_ctx G) by (intros a Ha; eapply ctx_more_gen_Frv; eauto).
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
      * apply H. apply ctx_more_gen_extr; [ exact HVr | ].
        apply ctx_more_gen_ext; [ exact HV | exact H1 ].
      * apply denv_eq_trans with
          (D2 := extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm' G'))) (kup D V k))
                 (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G))) rk).
        -- apply extr_pw. apply ext_kup_d. rewrite HVe. fsetdec.
        -- apply extr_rkup; [ intros; reflexivity | ].
           intros b Hb. apply AtomSetFacts.diff_iff in Hb as [Hb Hc].
           apply AtomSetFacts.diff_iff. split; [ exact Hb | intro Hd; apply Hc; apply HRe; exact Hd ].
    + intros x Hx. apply H0; auto.
      apply ctx_more_gen_cons; [ apply gen_more_gen; [ rewrite HFe; fsetdec | exact HRe ] | exact H1 ].
  - (* T_LetMono *) apply T_LetMono with (L := L) (T1 := T1); auto. intros x Hx.
    apply H0; auto. apply ctx_more_gen_cons; auto using sch_more_gen_refl.
  - (* T_Letrec *)
    assert (HV : forall a, a `in` ftv_ctx G -> a `notin` AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G))
      by (intros a Ha Hd; apply AtomSetFacts.diff_iff in Hd; tauto).
    assert (HVr : forall a, a `in` frv_ctx G -> a `notin` AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G))
      by (intros a Ha Hd; apply AtomSetFacts.diff_iff in Hd; tauto).
    assert (HF : ftv_ctx G' [<=] ftv_ctx G) by (intros a Ha; eapply ctx_more_gen_Ftv; eauto).
    assert (HR : frv_ctx G' [<=] frv_ctx G) by (intros a Ha; eapply ctx_more_gen_Frv; eauto).
    apply T_Letrec with (L := L) (R := R)
      (k := kup D (AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G)) k)
      (rk := rkup D (AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G)) rk); auto.
    + intros p Hp. eapply field_typing_pw.
      * apply H; auto. apply ctx_more_gen_cons; [ apply sch_more_gen_refl | ].
        apply ctx_more_gen_extr; [ exact HVr | ].
        apply ctx_more_gen_ext; [ exact HV | exact H1 ].
      * apply denv_eq_trans with
          (D2 := extr (ext D (AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G')) (kup D (AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G)) k))
                 (AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G)) rk).
        -- apply extr_pw. apply ext_kup_d. intros b Hb. apply AtomSetFacts.diff_iff in Hb as [Hb Hc].
           apply AtomSetFacts.diff_iff. split; [ exact Hb | intro Hd; apply Hc; apply HF; exact Hd ].
        -- apply extr_rkup; [ intros; reflexivity | ].
           intros b Hb. apply AtomSetFacts.diff_iff in Hb as [Hb Hc].
           apply AtomSetFacts.diff_iff. split; [ exact Hb | intro Hd; apply Hc; apply HR; exact Hd ].
    + intros p Hp. apply H0; auto.
      apply ctx_more_gen_cons; [ apply gen_more_gen; assumption | exact H1 ].
  - apply T_Record; eauto.
  - eapply T_Obj; eauto.
  - eapply T_Proj; eauto.
  - eapply T_Conv; eauto.
  - (* T_Unit *) apply T_Unit; eauto using ctx_more_gen_uniq.
  - (* T_Str *) apply T_Str; eauto using ctx_more_gen_uniq.
  - (* T_If *) eapply T_If; eauto.
  - (* T_ToFloat *) eapply T_ToFloat; eauto.
  - (* T_Bin *) eapply T_Bin; eauto.
  - (* T_Spread *) eapply T_Spread; eauto.
  - (* T_SpreadL *) eapply T_SpreadL; eauto.
  - (* T_Restrict *) eapply T_Restrict; eauto.
  - (* T_Fold *) eapply T_Fold; eauto.
  - (* T_Unfold *) eapply T_Unfold; eauto.
  - (* T_Con *) eapply T_Con; eauto.
  - (* T_Match *) eapply T_Match with (L := L); [ eauto | assumption | | intros e0 Hd; eauto ].
    intros tg b Hf x Hx. eapply (H0 tg b Hf x Hx).
    apply ctx_more_gen_cons; auto using sch_more_gen_refl.
  - apply FT_nil; eauto using ctx_more_gen_uniq.
  - eapply FT_cons; eauto.
  - eapply FT_meth; eauto.
Qed.

Lemma typing_ftv_mono : forall D G e T G',
  typing D G e T -> ctx_more_gen D G G' -> typing D G' e T.
Proof. intros. eapply (proj1 typing_ftv_mono_mut); eauto. Qed.

(* ================= teq under substitution; L5 for bijective renamings ====== *)

(* type-equivalence is a congruence closed under any type/row substitution
   (labels are untouched by substitution, so the swap rule still applies). *)
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
  - apply teq_refl.
  - apply teq_mu; auto.
  - apply teq_grp; auto.
  - apply teq_rec; auto.
  - eapply teq_trans; eauto.
  - apply teq_sym; auto.
  - apply req_refl.
  - apply req_refl.
  - apply req_head; auto.
  - apply req_swap; auto.
  - apply req_maybe; auto.
  - apply req_pre.
  - apply req_abs. apply rlacks_ap; auto.
  - apply req_swap_em; auto.
  - apply req_swap_mm; auto.
  - eapply req_trans; eauto.
  - apply req_sym; auto.
Qed.

Lemma teq_ap : forall T T' st sr, teq T T' -> teq (ap_typ st sr T) (ap_typ st sr T').
Proof. intros. apply teq_ap_mut; auto. Qed.

(* Substitution commutes with the relation: a type or row variable may be
   replaced by a locally closed type without changing the budget. *)
Lemma unroll_ap_mut : forall st sr, lc_sub st sr ->
  (forall n T T', unroll_eq n T T' ->
     unroll_eq n (ap_typ st sr T) (ap_typ st sr T')) /\
  (forall n R R', unroll_row n R R' ->
     unroll_row n (ap_row st sr R) (ap_row st sr R')).
Proof.
  intros st sr Hlc.
  apply unroll_mutind; intros; cbn [ap_typ ap_row] in *; eauto.
  - apply UE_teq. apply teq_ap. auto.
  - rewrite (ap_open st sr B 0 (typ_Mu B) Hlc). cbn [ap_typ]. apply UE_unfold.
  - rewrite (ap_open st sr B 0 (typ_Mu B) Hlc). cbn [ap_typ]. apply UE_fold.
  - apply UR_req. apply (proj2 teq_ap_mut). auto.
Qed.

Theorem unroll_ap : forall st sr n T T', lc_sub st sr ->
  unroll_eq n T T' -> unroll_eq n (ap_typ st sr T) (ap_typ st sr T').
Proof. intros st sr n T T' Hlc H. exact (proj1 (unroll_ap_mut st sr Hlc) n T T' H). Qed.

(* The shared receiver survives a substitution: the receiver row, the literal's
   row and each method's type are all substituted alike. *)
Lemma ap_row_tail_with : forall st sr R Rt,
  plain_spine R = true ->
  ap_row st sr (row_tail_with R Rt) = row_tail_with (ap_row st sr R) (ap_row st sr Rt).
Proof.
  intros st sr R Rt. induction R; simpl; intros H; try discriminate; auto.
  rewrite IHR by exact H. reflexivity.
Qed.

Lemma meths_shared_ap : forall st sr Rs fs R, lc_sub st sr ->
  meths_shared Rs fs R -> meths_shared (ap_row st sr Rs) fs (ap_row st sr R).
Proof.
  intros st sr Rs fs R Hlc H. induction H; simpl; try constructor; auto.
  eapply MS_meth; [ | exact IHmeths_shared ].
  pose proof (unroll_ap st sr _ _ _ Hlc H) as Hu. simpl in Hu. exact Hu.
Qed.

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
  - apply H.
  - apply H.
  - fsetdec.
  - (* row_Var *) unfold rr; simpl. fsetdec.
  - rewrite !AtomSetFacts.union_iff. rewrite H, H0. reflexivity.
  - rewrite !AtomSetFacts.union_iff. rewrite H, H0, H1. reflexivity.
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
  - apply H.
  - apply H.
  - fsetdec.
  - (* row_Var *) unfold rr; simpl. rewrite !AtomSetFacts.singleton_iff.
    split; [ intro HH; rewrite <- HH; symmetry; apply grfr | intro HH; rewrite HH; apply frgr ].
  - rewrite !AtomSetFacts.union_iff. rewrite H, H0. reflexivity.
  - rewrite !AtomSetFacts.union_iff. rewrite H, H0, H1. reflexivity.
Qed.

End Renaming.

(* ================================================================== *)
(* Context free-variable bookkeeping.                                    *)
(* ================================================================== *)

Lemma ftv_ctx_app : forall G1 G2,
  ftv_ctx (G1 ++ G2) [=] ftv_ctx G1 `union` ftv_ctx G2.
Proof. induction G1 as [|[x s] G1 IH]; simpl; intros; [ fsetdec | rewrite IH; fsetdec ]. Qed.

Lemma frv_ctx_app : forall G1 G2,
  frv_ctx (G1 ++ G2) [=] frv_ctx G1 `union` frv_ctx G2.
Proof. induction G1 as [|[x s] G1 IH]; simpl; intros; [ fsetdec | rewrite IH; fsetdec ]. Qed.

