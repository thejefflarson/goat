(* The two canonical Hindley-Milner substitution lemmas (issue #151), and the
   term-substitution / preservation / soundness development that rests on them.

   The wall the earlier passes hit was the T-Let case: generalization does not
   commute with a capturing substitution, because the let-generalized variables
   can be captured by the substitution's range.  The fix (approach (a), a
   derivation-level freshness/Barendregt step) is carried out HERE rather than in
   the typing rule: at each T-Let the generalized variables are renamed to atoms
   fresh for the substitution and the target context ([mk_rename]), so that the
   capture-avoiding substituted scheme ([casch], GoatHM) both preserves the
   instances ([casch_inst]) AND lines up with [gen] over the target context
   ([casch_gen_sch_equiv] below).  No typing rule changes; the set of accepted
   programs is unchanged.

   Everything is axiom- and admit-free:

   - Free-variable image of a substitution ([ftv_ap_typ]/[frv_ap_typ] and their
     converses): which atoms survive [ap_typ].
   - [casch_gen_sch_equiv]: capture-avoiding substitution of a generalization,
     with the renamed quantifiers fresh for the target context, is [gen] of the
     substituted body -- the bridge from [casch_inst] back to [gen].
   - [ctx_subst]/[tr_supp]/[tr_compat] and [typing_tsubst_gen_mut]: the general
     type/row substitution lemma.  The context relation allows EXTRA target
     bindings, so the identity instance is weakening.
   - L5 [typing_tsubst_fix] and L4 [typing_weaken] fall out as instances.
   - L6a [typing_subst], L6b [typing_subst_poly], then [preservation] and
     [soundness] (moved here from GoatSubst now that the two lemmas are proved). *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatBij.
Require Import Goat.GoatHM.
Require Import Coq.Lists.List.
Import ListNotations.

(* ===== free-variable image of a substitution (membership form) ===== *)

Lemma ftv_ap_mut :
  (forall T st sr a,
     a `in` ftv_typ (ap_typ st sr T) ->
     (exists b, b `in` ftv_typ T /\ a `in` ftv_typ (st b)) \/
     (exists p, p `in` frv_typ T /\ a `in` ftv_row (sr p))) /\
  (forall R st sr a,
     a `in` ftv_row (ap_row st sr R) ->
     (exists b, b `in` ftv_row R /\ a `in` ftv_typ (st b)) \/
     (exists p, p `in` frv_row R /\ a `in` ftv_row (sr p))).
Proof.
  apply typ_row_mutind; intros; simpl in *.
  - fsetdec.
  - fsetdec.
  - (* Arrow *) rewrite AtomSetFacts.union_iff in H1. destruct H1 as [H1|H1].
    + destruct (H _ _ _ H1) as [[b [Hb Ha]]|[p [Hp Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists p; split; [fsetdec|auto].
    + destruct (H0 _ _ _ H1) as [[b [Hb Ha]]|[p [Hp Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists p; split; [fsetdec|auto].
  - (* Record *) destruct (H _ _ _ H0) as [[b [Hb Ha]]|[p [Hp Ha]]].
    + left; exists b; auto.
    + right; exists p; auto.
  - (* Var *) left. exists a. split; [fsetdec|auto].
  - fsetdec.
  - (* row_Var *) right. exists r. split; [fsetdec|auto].
  - (* row_Ext *) rewrite AtomSetFacts.union_iff in H1. destruct H1 as [H1|H1].
    + destruct (H _ _ _ H1) as [[b [Hb Ha]]|[p [Hp Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists p; split; [fsetdec|auto].
    + destruct (H0 _ _ _ H1) as [[b [Hb Ha]]|[p [Hp Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists p; split; [fsetdec|auto].
Qed.

Lemma frv_ap_mut :
  (forall T st sr p,
     p `in` frv_typ (ap_typ st sr T) ->
     (exists b, b `in` ftv_typ T /\ p `in` frv_typ (st b)) \/
     (exists q, q `in` frv_typ T /\ p `in` frv_row (sr q))) /\
  (forall R st sr p,
     p `in` frv_row (ap_row st sr R) ->
     (exists b, b `in` ftv_row R /\ p `in` frv_typ (st b)) \/
     (exists q, q `in` frv_row R /\ p `in` frv_row (sr q))).
Proof.
  apply typ_row_mutind; intros; simpl in *.
  - fsetdec.
  - fsetdec.
  - rewrite AtomSetFacts.union_iff in H1. destruct H1 as [H1|H1].
    + destruct (H _ _ _ H1) as [[b [Hb Ha]]|[q [Hq Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists q; split; [fsetdec|auto].
    + destruct (H0 _ _ _ H1) as [[b [Hb Ha]]|[q [Hq Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists q; split; [fsetdec|auto].
  - destruct (H _ _ _ H0) as [[b [Hb Ha]]|[q [Hq Ha]]].
    + left; exists b; auto.
    + right; exists q; auto.
  - (* Var *) left. exists a. split; [fsetdec|auto].
  - fsetdec.
  - (* row_Var *) right. exists r. split; [fsetdec|auto].
  - rewrite AtomSetFacts.union_iff in H1. destruct H1 as [H1|H1].
    + destruct (H _ _ _ H1) as [[b [Hb Ha]]|[q [Hq Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists q; split; [fsetdec|auto].
    + destruct (H0 _ _ _ H1) as [[b [Hb Ha]]|[q [Hq Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists q; split; [fsetdec|auto].
Qed.

Lemma ftv_ap_typ : forall st sr T a,
  a `in` ftv_typ (ap_typ st sr T) ->
  (exists b, b `in` ftv_typ T /\ a `in` ftv_typ (st b)) \/
  (exists p, p `in` frv_typ T /\ a `in` ftv_row (sr p)).
Proof. intros. eapply (proj1 ftv_ap_mut); eauto. Qed.

Lemma frv_ap_typ : forall st sr T p,
  p `in` frv_typ (ap_typ st sr T) ->
  (exists b, b `in` ftv_typ T /\ p `in` frv_typ (st b)) \/
  (exists q, q `in` frv_typ T /\ p `in` frv_row (sr q)).
Proof. intros. eapply (proj1 frv_ap_mut); eauto. Qed.

(* backward direction: a free var of the image is witnessed by a free var of the
   source mapped through the substitution. *)
Lemma ftv_ap_in_mut :
  (forall T st sr a,
     ((exists b, b `in` ftv_typ T /\ a `in` ftv_typ (st b)) \/
      (exists p, p `in` frv_typ T /\ a `in` ftv_row (sr p))) ->
     a `in` ftv_typ (ap_typ st sr T)) /\
  (forall R st sr a,
     ((exists b, b `in` ftv_row R /\ a `in` ftv_typ (st b)) \/
      (exists p, p `in` frv_row R /\ a `in` ftv_row (sr p))) ->
     a `in` ftv_row (ap_row st sr R)).
Proof.
  apply typ_row_mutind; intros; simpl in *.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - rewrite AtomSetFacts.union_iff.
    destruct H1 as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|Hb];
        [left; apply H; left; eauto | right; apply H0; left; eauto].
    + rewrite AtomSetFacts.union_iff in Hp. destruct Hp as [Hp|Hp];
        [left; apply H; right; eauto | right; apply H0; right; eauto].
  - apply H. destruct H0 as [[b [Hb Ha]]|[p [Hp Ha]]]; [left; eauto | right; eauto].
  - destruct H as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.singleton_iff in Hb. subst b. exact Ha.
    + fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp Ha]]]; [fsetdec|].
    rewrite AtomSetFacts.singleton_iff in Hp. subst p. exact Ha.
  - rewrite AtomSetFacts.union_iff.
    destruct H1 as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|Hb];
        [left; apply H; left; eauto | right; apply H0; left; eauto].
    + rewrite AtomSetFacts.union_iff in Hp. destruct Hp as [Hp|Hp];
        [left; apply H; right; eauto | right; apply H0; right; eauto].
Qed.

Lemma ftv_ap_in1 : forall st sr T a b,
  b `in` ftv_typ T -> a `in` ftv_typ (st b) -> a `in` ftv_typ (ap_typ st sr T).
Proof. intros. apply (proj1 ftv_ap_in_mut). left. eauto. Qed.

Lemma ftv_ap_in2 : forall st sr T a p,
  p `in` frv_typ T -> a `in` ftv_row (sr p) -> a `in` ftv_typ (ap_typ st sr T).
Proof. intros. apply (proj1 ftv_ap_in_mut). right. eauto. Qed.

Lemma frv_ap_in_mut :
  (forall T st sr a,
     ((exists b, b `in` ftv_typ T /\ a `in` frv_typ (st b)) \/
      (exists p, p `in` frv_typ T /\ a `in` frv_row (sr p))) ->
     a `in` frv_typ (ap_typ st sr T)) /\
  (forall R st sr a,
     ((exists b, b `in` ftv_row R /\ a `in` frv_typ (st b)) \/
      (exists p, p `in` frv_row R /\ a `in` frv_row (sr p))) ->
     a `in` frv_row (ap_row st sr R)).
Proof.
  apply typ_row_mutind; intros; simpl in *.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - rewrite AtomSetFacts.union_iff.
    destruct H1 as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|Hb];
        [left; apply H; left; eauto | right; apply H0; left; eauto].
    + rewrite AtomSetFacts.union_iff in Hp. destruct Hp as [Hp|Hp];
        [left; apply H; right; eauto | right; apply H0; right; eauto].
  - apply H. destruct H0 as [[b [Hb Ha]]|[p [Hp Ha]]]; [left; eauto | right; eauto].
  - destruct H as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.singleton_iff in Hb. subst b. exact Ha.
    + fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp Ha]]]; [fsetdec|].
    rewrite AtomSetFacts.singleton_iff in Hp. subst p. exact Ha.
  - rewrite AtomSetFacts.union_iff.
    destruct H1 as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|Hb];
        [left; apply H; left; eauto | right; apply H0; left; eauto].
    + rewrite AtomSetFacts.union_iff in Hp. destruct Hp as [Hp|Hp];
        [left; apply H; right; eauto | right; apply H0; right; eauto].
Qed.

Lemma frv_ap_in1 : forall st sr T a b,
  b `in` ftv_typ T -> a `in` frv_typ (st b) -> a `in` frv_typ (ap_typ st sr T).
Proof. intros. apply (proj1 frv_ap_in_mut). left. eauto. Qed.

Lemma frv_ap_in2 : forall st sr T a p,
  p `in` frv_typ T -> a `in` frv_row (sr p) -> a `in` frv_typ (ap_typ st sr T).
Proof. intros. apply (proj1 frv_ap_in_mut). right. eauto. Qed.

(* ====================================================================== *)
(* The casch->gen bridge: capture-avoiding scheme substitution of a       *)
(* generalization, with the renamed quantifiers chosen fresh for the      *)
(* target context's free vars (Ct/Cr) and fixed by the substitution, is   *)
(* exactly [gen]-equivalent to generalizing the substituted body over that *)
(* target context.  This is the piece that lets a substituted T-Let be    *)
(* reassembled: casch_inst supplies the instances, this lemma lines the    *)
(* scheme back up with [gen].                                             *)
(* ====================================================================== *)

Lemma casch_gen_sch_equiv : forall st sr g gr s Ct Cr,
  (forall a, g (g a) = a) -> (forall r, gr (gr r) = r) ->
  (forall a, a `in` ftv_sch s -> g a = a) ->
  (forall r, r `in` frv_sch s -> gr r = r) ->
  s_tq s [<=] ftv_typ (s_body s) ->
  s_rq s [<=] frv_typ (s_body s) ->
  (forall a, a `in` amap g (s_tq s) -> st a = typ_Var a) ->
  (forall r, r `in` amap gr (s_rq s) -> sr r = row_Var r) ->
  (forall a, a `in` amap g (s_tq s) -> a `notin` Ct) ->
  (forall r, r `in` amap gr (s_rq s) -> r `notin` Cr) ->
  (forall a, a `in` ftv_sch s -> ftv_typ (st a) [<=] Ct) ->
  (forall r, r `in` frv_sch s -> ftv_row (sr r) [<=] Ct) ->
  (forall a, a `in` ftv_sch s -> frv_typ (st a) [<=] Cr) ->
  (forall r, r `in` frv_sch s -> frv_row (sr r) [<=] Cr) ->
  sch_equiv (casch st sr g gr s)
            (Sch (AtomSetImpl.diff (ftv_typ (ap_typ st sr (ren_typ g gr (s_body s)))) Ct)
                 (AtomSetImpl.diff (frv_typ (ap_typ st sr (ren_typ g gr (s_body s)))) Cr)
                 (ap_typ st sr (ren_typ g gr (s_body s)))).
Proof.
  intros st sr g gr s Ct Cr Hgi Hgri Hgf Hgrf Hsubt Hsubr Hfx1 Hfx2 HfreshT HfreshR
    HcT_t HcT_r HcR_t HcR_r.
  set (B := ap_typ st sr (ren_typ g gr (s_body s))).
  (* ftv of the renamed body: b in ftv(ren body) <-> g b in ftv body *)
  assert (HFren : forall b, b `in` ftv_typ (ren_typ g gr (s_body s)) <-> g b `in` ftv_typ (s_body s)).
  { intro b. unfold ren_typ. apply (proj1 (Ftv_ren_mut g g gr Hgi Hgi)). }
  assert (HRren : forall b, b `in` frv_typ (ren_typ g gr (s_body s)) <-> gr b `in` frv_typ (s_body s)).
  { intro b. unfold ren_typ. apply (proj1 (Frv_ren_mut g gr gr Hgri Hgri)). }
  unfold sch_equiv, casch; simpl. split; [| split].
  - (* s_tq: amap g (s_tq s) [=] diff (ftv B) Ct *)
    apply AtomSetProperties.subset_antisym; intros a Ha.
    + (* amap g (s_tq s) subset diff (ftv B) Ct *)
      rewrite AtomSetFacts.diff_iff. split.
      * (* a in ftv B *)
        apply amap_in in Ha. destruct Ha as [q [Hq Hgq]].
        assert (Hqb : q `in` ftv_typ (s_body s)) by (apply Hsubt; exact Hq).
        assert (Hain : a `in` ftv_typ (ren_typ g gr (s_body s))).
        { apply HFren. rewrite <- Hgq. rewrite Hgi. exact Hqb. }
        assert (Hsta : st a = typ_Var a).
        { apply Hfx1. apply amap_in. exists q; auto. }
        unfold B. apply (ftv_ap_in1 st sr _ a a); [ exact Hain | rewrite Hsta; simpl; fsetdec ].
      * (* a notin Ct *)
        apply HfreshT. exact Ha.
    + (* diff (ftv B) Ct subset amap g (s_tq s) *)
      rewrite AtomSetFacts.diff_iff in Ha. destruct Ha as [HaB HaC].
      unfold B in HaB. apply ftv_ap_typ in HaB.
      destruct HaB as [[b [Hb Hast]]|[p [Hp Hast]]].
      * (* type-var contribution *)
        apply HFren in Hb. (* g b in ftv body *)
        destruct (AtomSetImpl.mem (g b) (s_tq s)) eqn:Em.
        -- apply AtomSetFacts.mem_iff in Em.
           (* b = g (g b) in amap g (s_tq s); st b = Var b; a in {b} *)
           assert (Hbamap : b `in` amap g (s_tq s)).
           { apply amap_in. exists (g b). split; [exact Em| apply Hgi]. }
           rewrite (Hfx1 b Hbamap) in Hast. simpl in Hast.
           assert (a = b) by fsetdec. subst a. exact Hbamap.
        -- apply AtomSetFacts.not_mem_iff in Em.
           assert (Hbf : g b `in` ftv_sch s)
             by (unfold ftv_sch; apply AtomSetImpl.diff_3; auto).
           (* g fixes ftv_sch s so g (g b) = g b, i.e. b = g b in ftv_sch s *)
           assert (Hgb : g (g b) = g b) by (apply Hgf; exact Hbf).
           rewrite Hgi in Hgb. (* b = g b *)
           assert (Hbf' : b `in` ftv_sch s) by (rewrite Hgb; exact Hbf).
           assert (ftv_typ (st b) [<=] Ct) by (apply HcT_t; exact Hbf').
           exfalso. apply HaC. fsetdec.
      * (* row-var contribution *)
        apply HRren in Hp. (* gr p in frv body *)
        destruct (AtomSetImpl.mem (gr p) (s_rq s)) eqn:Em.
        -- apply AtomSetFacts.mem_iff in Em.
           assert (Hpamap : p `in` amap gr (s_rq s)).
           { apply amap_in. exists (gr p). split; [exact Em| apply Hgri]. }
           rewrite (Hfx2 p Hpamap) in Hast. simpl in Hast. fsetdec.
        -- apply AtomSetFacts.not_mem_iff in Em.
           assert (Hpf : gr p `in` frv_sch s)
             by (unfold frv_sch; apply AtomSetImpl.diff_3; auto).
           assert (Hgp : gr (gr p) = gr p) by (apply Hgrf; exact Hpf).
           rewrite Hgri in Hgp.
           assert (Hpf' : p `in` frv_sch s) by (rewrite Hgp; exact Hpf).
           assert (ftv_row (sr p) [<=] Ct) by (apply HcT_r; exact Hpf').
           exfalso. apply HaC. fsetdec.
  - (* s_rq: amap gr (s_rq s) [=] diff (frv B) Cr *)
    apply AtomSetProperties.subset_antisym; intros a Ha.
    + rewrite AtomSetFacts.diff_iff. split.
      * apply amap_in in Ha. destruct Ha as [q [Hq Hgq]].
        assert (Hqb : q `in` frv_typ (s_body s)) by (apply Hsubr; exact Hq).
        assert (Hain : a `in` frv_typ (ren_typ g gr (s_body s))).
        { apply HRren. rewrite <- Hgq. rewrite Hgri. exact Hqb. }
        assert (Hsra : sr a = row_Var a).
        { apply Hfx2. apply amap_in. exists q; auto. }
        unfold B. apply (frv_ap_in2 st sr _ a a); [ exact Hain | rewrite Hsra; simpl; fsetdec ].
      * apply HfreshR. exact Ha.
    + rewrite AtomSetFacts.diff_iff in Ha. destruct Ha as [HaB HaC].
      unfold B in HaB. apply frv_ap_typ in HaB.
      destruct HaB as [[b [Hb Hast]]|[p [Hp Hast]]].
      * apply HFren in Hb.
        destruct (AtomSetImpl.mem (g b) (s_tq s)) eqn:Em.
        -- apply AtomSetFacts.mem_iff in Em.
           assert (Hbamap : b `in` amap g (s_tq s)).
           { apply amap_in. exists (g b). split; [exact Em| apply Hgi]. }
           rewrite (Hfx1 b Hbamap) in Hast. simpl in Hast. fsetdec.
        -- apply AtomSetFacts.not_mem_iff in Em.
           assert (Hbf : g b `in` ftv_sch s)
             by (unfold ftv_sch; apply AtomSetImpl.diff_3; auto).
           assert (Hgb : g (g b) = g b) by (apply Hgf; exact Hbf).
           rewrite Hgi in Hgb.
           assert (Hbf' : b `in` ftv_sch s) by (rewrite Hgb; exact Hbf).
           assert (frv_typ (st b) [<=] Cr) by (apply HcR_t; exact Hbf').
           exfalso. apply HaC. fsetdec.
      * apply HRren in Hp.
        destruct (AtomSetImpl.mem (gr p) (s_rq s)) eqn:Em.
        -- apply AtomSetFacts.mem_iff in Em.
           assert (Hpamap : p `in` amap gr (s_rq s)).
           { apply amap_in. exists (gr p). split; [exact Em| apply Hgri]. }
           rewrite (Hfx2 p Hpamap) in Hast. simpl in Hast.
           assert (a = p) by fsetdec. subst a. exact Hpamap.
        -- apply AtomSetFacts.not_mem_iff in Em.
           assert (Hpf : gr p `in` frv_sch s)
             by (unfold frv_sch; apply AtomSetImpl.diff_3; auto).
           assert (Hgp : gr (gr p) = gr p) by (apply Hgrf; exact Hpf).
           rewrite Hgri in Hgp.
           assert (Hpf' : p `in` frv_sch s) by (rewrite Hgp; exact Hpf).
           assert (frv_row (sr p) [<=] Cr) by (apply HcR_r; exact Hpf').
           exfalso. apply HaC. fsetdec.
  - reflexivity.
Qed.

(* ===================== context substitution relation ==================== *)

Definition sch_subst (st:tsub) (sr:rsub) (s s':scheme) : Prop :=
  forall W, inst W s -> inst (ap_typ st sr W) s'.

(* The context-substitution relation: every binding of [G] has a corresponding
   binding in [G'] whose scheme absorbs the substituted instances.  [G'] may
   carry EXTRA bindings (so this relation also expresses weakening, with the
   identity substitution). *)
Definition ctx_subst (st:tsub) (sr:rsub) (G G':ctx) : Prop :=
  forall x s, binds x s G -> exists s', binds x s' G' /\ sch_subst st sr s s'.

Lemma ctx_subst_binds : forall st sr G G' x s,
  ctx_subst st sr G G' -> binds x s G ->
  exists s', binds x s' G' /\ sch_subst st sr s s'.
Proof. intros st sr G G' x s H Hb. apply H; exact Hb. Qed.

Lemma ctx_subst_cons : forall st sr x s0 s0' G G',
  sch_subst st sr s0 s0' -> ctx_subst st sr G G' ->
  ctx_subst st sr ((x ~ s0) ++ G) ((x ~ s0') ++ G').
Proof.
  intros st sr x s0 s0' G G' Hs0 HG y sy Hb.
  apply binds_cons_1 in Hb. destruct Hb as [[Hy Hsy]|Hb].
  - subst. exists s0'. split; [ apply binds_cons_2; reflexivity | exact Hs0 ].
  - destruct (HG y sy Hb) as [s' [Hb' Hss]]. exists s'. split; [ apply binds_cons_3; auto | exact Hss ].
Qed.

Lemma binds_ftv_sch : forall x s G, binds x s G -> ftv_sch s [<=] ftv_ctx G.
Proof.
  induction G as [|[y sy] G IH]; intros Hb; [inversion Hb|].
  apply binds_cons_1 in Hb. simpl. destruct Hb as [[Hy Hs]|Hb].
  - subst. fsetdec.
  - specialize (IH Hb). fsetdec.
Qed.

Lemma binds_frv_sch : forall x s G, binds x s G -> frv_sch s [<=] frv_ctx G.
Proof.
  induction G as [|[y sy] G IH]; intros Hb; [inversion Hb|].
  apply binds_cons_1 in Hb. simpl. destruct Hb as [[Hy Hs]|Hb].
  - subst. fsetdec.
  - specialize (IH Hb). fsetdec.
Qed.

Lemma sch_subst_mono : forall st sr T,
  sch_subst st sr (sch_mono T) (sch_mono (ap_typ st sr T)).
Proof.
  intros st sr T W HW. apply inst_mono_eq in HW. subst W. apply inst_mono_self.
Qed.

(* a substitution fixing a scheme's free vars preserves its instances pointwise:
   this is the [T-Var] "re-chosen instance" with no renaming needed. *)
Lemma sch_subst_fix : forall st sr s,
  (forall a, a `in` ftv_sch s -> st a = typ_Var a) ->
  (forall r, r `in` frv_sch s -> sr r = row_Var r) ->
  sch_subst st sr s s.
Proof.
  intros st sr s Hf Hfr W [pt [pr [Hpt [Hpr HW]]]].
  exists (fun a => if AtomSetImpl.mem a (s_tq s) then ap_typ st sr (pt a) else typ_Var a),
         (fun r => if AtomSetImpl.mem r (s_rq s) then ap_row st sr (pr r) else row_Var r).
  split; [| split].
  - intros a Ha. destruct (AtomSetImpl.mem a (s_tq s)) eqn:Em;
      [apply AtomSetFacts.mem_iff in Em; contradiction|reflexivity].
  - intros r Hr. destruct (AtomSetImpl.mem r (s_rq s)) eqn:Em;
      [apply AtomSetFacts.mem_iff in Em; contradiction|reflexivity].
  - rewrite HW. rewrite ap_typ_comp. apply ap_typ_ext.
    + intros a Ha. unfold tcomp. destruct (AtomSetImpl.mem a (s_tq s)) eqn:Em.
      * reflexivity.
      * apply AtomSetFacts.not_mem_iff in Em.
        rewrite (Hpt a Em). simpl.
        assert (a `in` ftv_sch s) by (unfold ftv_sch; apply AtomSetImpl.diff_3; auto).
        rewrite (Hf a H). reflexivity.
    + intros r Hr. unfold rcomp. destruct (AtomSetImpl.mem r (s_rq s)) eqn:Em.
      * reflexivity.
      * apply AtomSetFacts.not_mem_iff in Em.
        rewrite (Hpr r Em). simpl.
        assert (r `in` frv_sch s) by (unfold frv_sch; apply AtomSetImpl.diff_3; auto).
        rewrite (Hfr r H). reflexivity.
Qed.

(* renaming a scheme's instance along a bijection fixing the scheme's free vars
   lands on another instance of the SAME scheme. *)
Lemma inst_ren_same : forall g gr s W,
  (forall a, a `in` ftv_sch s -> g a = a) ->
  (forall r, r `in` frv_sch s -> gr r = r) ->
  inst W s -> inst (ren_typ g gr W) s.
Proof.
  intros g gr s W Hgf Hgrf [pt [pr [Hpt [Hpr HW]]]].
  exists (fun a => if AtomSetImpl.mem a (s_tq s) then ren_typ g gr (pt a) else typ_Var a),
         (fun r => if AtomSetImpl.mem r (s_rq s) then ren_row g gr (pr r) else row_Var r).
  split; [| split].
  - intros a Ha. destruct (AtomSetImpl.mem a (s_tq s)) eqn:Em;
      [apply AtomSetFacts.mem_iff in Em; contradiction|reflexivity].
  - intros r Hr. destruct (AtomSetImpl.mem r (s_rq s)) eqn:Em;
      [apply AtomSetFacts.mem_iff in Em; contradiction|reflexivity].
  - rewrite HW. unfold ren_typ at 1. rewrite ap_typ_comp. apply ap_typ_ext.
    + intros a Ha. unfold tcomp. destruct (AtomSetImpl.mem a (s_tq s)) eqn:Em.
      * unfold ren_typ. reflexivity.
      * apply AtomSetFacts.not_mem_iff in Em.
        rewrite (Hpt a Em). simpl. unfold rt.
        assert (a `in` ftv_sch s) by (unfold ftv_sch; apply AtomSetImpl.diff_3; auto).
        rewrite (Hgf a H). reflexivity.
    + intros r Hr. unfold rcomp. destruct (AtomSetImpl.mem r (s_rq s)) eqn:Em.
      * unfold ren_row. reflexivity.
      * apply AtomSetFacts.not_mem_iff in Em.
        rewrite (Hpr r Em). simpl. unfold rr.
        assert (r `in` frv_sch s) by (unfold frv_sch; apply AtomSetImpl.diff_3; auto).
        rewrite (Hgrf r H). reflexivity.
Qed.

(* applying [st,sr] after a renaming equals applying the precomposed subst *)
Lemma ap_precomp : forall st sr g gr X,
  ap_typ (fun a => st (g a)) (fun r => sr (gr r)) X = ap_typ st sr (ren_typ g gr X).
Proof.
  intros. unfold ren_typ. rewrite ap_typ_comp. apply ap_typ_ext; intros.
  - unfold tcomp, rt. simpl. reflexivity.
  - unfold rcomp, rr. simpl. reflexivity.
Qed.

(* the context-substitution relation is stable under precomposing [st,sr] with a
   renaming that fixes the context's free variables. *)
Lemma ctx_subst_precomp : forall st sr g gr G G',
  ctx_subst st sr G G' ->
  (forall a, a `in` ftv_ctx G -> g a = a) ->
  (forall r, r `in` frv_ctx G -> gr r = r) ->
  ctx_subst (fun a => st (g a)) (fun r => sr (gr r)) G G'.
Proof.
  intros st sr g gr G G' HG Hgf Hgrf x s Hb.
  destruct (HG x s Hb) as [s' [Hb' Hss]]. exists s'. split; [exact Hb'|].
  intros W HW. rewrite ap_precomp. apply Hss. apply inst_ren_same.
  - intros a Ha. apply Hgf.
    assert (ftv_sch s [<=] ftv_ctx G) by (eapply binds_ftv_sch; eauto). fsetdec.
  - intros r Hr. apply Hgrf.
    assert (frv_sch s [<=] frv_ctx G) by (eapply binds_frv_sch; eauto). fsetdec.
  - exact HW.
Qed.

(* ================= toward the general type/row substitution lemma ======== *)

Fixpoint lset (l:list atom) : atoms :=
  match l with [] => {} | a :: l' => add a (lset l') end.

Lemma lset_in : forall x l, x `in` lset l <-> List.In x l.
Proof.
  induction l as [|a l IH]; simpl.
  - split; [fsetdec | intros []].
  - rewrite AtomSetFacts.add_iff, IH. split.
    + intros [H|H]; [left; auto | right; auto].
    + intros [H|H]; [left; auto | right; auto].
Qed.

Lemma typing_uniq_mut :
  (forall G e T, typing G e T -> uniq G) /\
  (forall G fs R, field_typing G fs R -> uniq G).
Proof.
  apply typing_field_mutind; intros; auto;
    (* T_Abs / T_Let: recover uniq G from the cofinite body premise *)
    try (pick fresh x;
         match goal with
         | H : forall y, y `notin` ?L -> uniq _ |- uniq ?G =>
             specialize (H x ltac:(auto)); apply uniq_cons_iff in H; apply H
         end).
Qed.

Lemma typing_uniq : forall G e T, typing G e T -> uniq G.
Proof. apply typing_uniq_mut. Qed.

Lemma ftv_sch_gen_sub : forall G T, ftv_sch (gen G T) [<=] ftv_ctx G.
Proof. intros. unfold ftv_sch, gen; simpl. fsetdec. Qed.

Lemma frv_sch_gen_sub : forall G T, frv_sch (gen G T) [<=] frv_ctx G.
Proof. intros. unfold frv_sch, gen; simpl. fsetdec. Qed.

(* a substitution fixing the context's free vars relates the context to itself *)
Lemma ctx_subst_fix : forall st sr G,
  (forall a, a `in` ftv_ctx G -> st a = typ_Var a) ->
  (forall r, r `in` frv_ctx G -> sr r = row_Var r) ->
  ctx_subst st sr G G.
Proof.
  intros st sr G Hf Hfr x s Hb. exists s. split; [exact Hb|].
  apply sch_subst_fix.
  - intros a Ha. apply Hf. assert (ftv_sch s [<=] ftv_ctx G) by (eapply binds_ftv_sch; eauto). fsetdec.
  - intros r Hr. apply Hfr. assert (frv_sch s [<=] frv_ctx G) by (eapply binds_frv_sch; eauto). fsetdec.
Qed.

(* identity-substitution instance of [ctx_subst] with extra target bindings:
   this is exactly what weakening needs. *)
Lemma ctx_subst_weaken : forall G G',
  (forall x s, binds x s G -> binds x s G') ->
  ctx_subst idt idr G G'.
Proof.
  intros G G' Hsub x s Hb. exists s. split; [ apply Hsub; exact Hb |].
  apply sch_subst_fix; intros; reflexivity.
Qed.

Lemma ftv_sch_mono : forall T, ftv_sch (sch_mono T) [=] ftv_typ T.
Proof. intro T. unfold ftv_sch, sch_mono; simpl. fsetdec. Qed.
Lemma frv_sch_mono : forall T, frv_sch (sch_mono T) [=] frv_typ T.
Proof. intro T. unfold frv_sch, sch_mono; simpl. fsetdec. Qed.

Definition tr_supp (st:tsub) (sr:rsub) (A:atoms) : Prop :=
  (forall a, a `notin` A -> st a = typ_Var a) /\
  (forall r, r `notin` A -> sr r = row_Var r).

Definition tr_compat (st:tsub) (sr:rsub) (G G':ctx) : Prop :=
  (forall a, a `in` ftv_ctx G -> ftv_typ (st a) [<=] ftv_ctx G') /\
  (forall a, a `in` ftv_ctx G -> frv_typ (st a) [<=] frv_ctx G') /\
  (forall r, r `in` frv_ctx G -> ftv_row (sr r) [<=] ftv_ctx G') /\
  (forall r, r `in` frv_ctx G -> frv_row (sr r) [<=] frv_ctx G').

(* The general type/row substitution lemma: a kind-respecting substitution
   applied to a derivation, with the context substituted capture-avoidingly
   ([ctx_subst]), finite support ([tr_supp]) and image-compatibility
   ([tr_compat]).  Every case is structural except T-Let, which freshens the
   let-generalized variables (via [mk_rename]) so that [casch_inst] supplies the
   instances and [casch_gen_sch_equiv] lines the scheme back up with [gen]. *)
Lemma typing_tsubst_gen_mut :
  (forall G e T, typing G e T -> forall st sr G' A,
      uniq G' -> ctx_subst st sr G G' -> tr_supp st sr A -> tr_compat st sr G G' ->
      typing G' e (ap_typ st sr T)) /\
  (forall G fs R, field_typing G fs R -> forall st sr G' A,
      uniq G' -> ctx_subst st sr G G' -> tr_supp st sr A -> tr_compat st sr G G' ->
      field_typing G' fs (ap_row st sr R)).
Proof.
  apply typing_field_mutind.
  - (* T_Var *) intros G x s T Hu Hb Hi st sr G' A Hu' Hcs Hsupp Hcompat.
    destruct (ctx_subst_binds _ _ _ _ _ _ Hcs Hb) as [s' [Hb' Hss]].
    apply T_Var with (s := s'); auto.
  - intros G n Hu st sr G' A Hu' Hcs Hsupp Hcompat. apply T_Num; auto.
  - intros G Hu st sr G' A Hu' Hcs Hsupp Hcompat. apply T_True; auto.
  - intros G Hu st sr G' A Hu' Hcs Hsupp Hcompat. apply T_False; auto.
  - (* T_Abs *) intros L G e T1 T2 Ht IH st sr G' A Hu' Hcs Hsupp Hcompat. simpl.
    apply T_Abs with (L := L `union` dom G'). intros x Hx.
    apply (IH x ltac:(fsetdec) st sr ((x ~ sch_mono (ap_typ st sr T1)) ++ G') A).
    + constructor; [ assumption | fsetdec ].
    + apply ctx_subst_cons; [ apply sch_subst_mono | assumption ].
    + assumption.
    + (* tr_compat for the extended ctx *)
      destruct Hcompat as [HcT [HcFr [HcRt HcRfr]]].
      unfold tr_compat; simpl. repeat split.
      * intros a Ha. rewrite AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha].
        -- rewrite ftv_sch_mono in Ha. intros z Hz. apply AtomSetFacts.union_iff. left.
           rewrite ftv_sch_mono. apply (ftv_ap_in1 st sr T1 z a); [ exact Ha | exact Hz ].
        -- intros z Hz. apply AtomSetFacts.union_iff. right. apply (HcT a Ha). exact Hz.
      * intros a Ha. rewrite AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha].
        -- rewrite ftv_sch_mono in Ha. intros z Hz. apply AtomSetFacts.union_iff. left.
           rewrite frv_sch_mono. apply (frv_ap_in1 st sr T1 z a); [ exact Ha | exact Hz ].
        -- intros z Hz. apply AtomSetFacts.union_iff. right. apply (HcFr a Ha). exact Hz.
      * intros r Hr. rewrite AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr].
        -- rewrite frv_sch_mono in Hr. intros z Hz. apply AtomSetFacts.union_iff. left.
           rewrite ftv_sch_mono. apply (ftv_ap_in2 st sr T1 z r); [ exact Hr | exact Hz ].
        -- intros z Hz. apply AtomSetFacts.union_iff. right. apply (HcRt r Hr). exact Hz.
      * intros r Hr. rewrite AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr].
        -- rewrite frv_sch_mono in Hr. intros z Hz. apply AtomSetFacts.union_iff. left.
           rewrite frv_sch_mono. apply (frv_ap_in2 st sr T1 z r); [ exact Hr | exact Hz ].
        -- intros z Hz. apply AtomSetFacts.union_iff. right. apply (HcRfr r Hr). exact Hz.
  - (* T_App *) intros G e1 e2 T1 T2 Ht1 IH1 Ht2 IH2 st sr G' A Hu' Hcs Hsupp Hcompat. simpl in *.
    eapply T_App; [ eapply IH1 | eapply IH2 ]; eauto.
  - (* T_Let *) intros L0 G e1 e2 T1 T2 Ht1 IH1 Ht2 IH2 st sr G' A Hu' Hcs Hsupp Hcompat.
    destruct Hsupp as [HsuppT HsuppR].
    destruct Hcompat as [HcT [HcFr [HcRt HcRfr]]].
    set (s := gen G T1).
    set (Bav := A `union` ftv_ctx G `union` frv_ctx G `union` ftv_ctx G' `union` frv_ctx G').
    destruct (mk_rename (s_tq s) Bav) as [g [Ng [Hginv [HgNB [HgNV [HgVN Hgfix]]]]]].
    destruct (mk_rename (s_rq s) Bav) as [gr [Ngr [Hgrinv [HgrNB [HgrNV [HgrVN Hgrfix]]]]]].
    (* renamed quantifiers are fresh for Bav *)
    assert (HgF : forall a, a `in` amap g (s_tq s) -> a `notin` Bav).
    { intros a Ha. apply amap_in in Ha. destruct Ha as [v [Hv Hgv]]. subst a.
      apply HgNB. apply HgVN. exact Hv. }
    assert (HgrF : forall p, p `in` amap gr (s_rq s) -> p `notin` Bav).
    { intros p Hp. apply amap_in in Hp. destruct Hp as [v [Hv Hgv]]. subst p.
      apply HgrNB. apply HgrVN. exact Hv. }
    (* g, gr fix sets inside Bav and disjoint from the quantifier set *)
    assert (Hgfix' : forall C, C [<=] Bav -> (forall x, x `in` C -> x `notin` s_tq s) ->
                     forall c, c `in` C -> g c = c).
    { intros C Hsub Hdisj c Hc. apply Hgfix; [ apply Hdisj; exact Hc |].
      intro HInc. apply (HgNB c HInc). apply Hsub. exact Hc. }
    assert (Hgrfix' : forall C, C [<=] Bav -> (forall x, x `in` C -> x `notin` s_rq s) ->
                      forall c, c `in` C -> gr c = c).
    { intros C Hsub Hdisj c Hc. apply Hgrfix; [ apply Hdisj; exact Hc |].
      intro HInc. apply (HgrNB c HInc). apply Hsub. exact Hc. }
    assert (HQtdisj : forall x, x `in` ftv_ctx G -> x `notin` s_tq s).
    { intros x Hx. unfold s, gen, s_tq; simpl. fsetdec. }
    assert (HQrdisj : forall x, x `in` frv_ctx G -> x `notin` s_rq s).
    { intros x Hx. unfold s, gen, s_rq; simpl. fsetdec. }
    assert (HgfixG : forall c, c `in` ftv_ctx G -> g c = c).
    { apply Hgfix'; [ unfold Bav; fsetdec | exact HQtdisj ]. }
    assert (HgrfixG : forall c, c `in` frv_ctx G -> gr c = c).
    { apply Hgrfix'; [ unfold Bav; fsetdec | exact HQrdisj ]. }
    assert (HsubST : ftv_sch s [<=] ftv_ctx G) by (unfold s; apply ftv_sch_gen_sub).
    assert (HsubSR : frv_sch s [<=] frv_ctx G) by (unfold s; apply frv_sch_gen_sub).
    assert (HgfixS : forall a, a `in` ftv_sch s -> g a = a).
    { apply Hgfix'; [ unfold Bav; fsetdec | intros x Hx; apply HQtdisj; fsetdec ]. }
    assert (HgrfixS : forall r, r `in` frv_sch s -> gr r = r).
    { apply Hgrfix'; [ unfold Bav; fsetdec | intros x Hx; apply HQrdisj; fsetdec ]. }
    (* substitution fixes the renamed quantifiers (fresh outside A) *)
    assert (HstQ : forall a, a `in` amap g (s_tq s) -> st a = typ_Var a).
    { intros a Ha. apply HsuppT. assert (a `notin` Bav) by (apply HgF; exact Ha).
      unfold Bav in H. fsetdec. }
    assert (HsrQ : forall r, r `in` amap gr (s_rq s) -> sr r = row_Var r).
    { intros r Hr. apply HsuppR. assert (r `notin` Bav) by (apply HgrF; exact Hr).
      unfold Bav in H. fsetdec. }
    (* no-capture conditions, from tr_compat + freshness of renamed quantifiers *)
    assert (Hnc1 : forall a b, b `in` ftv_sch s -> a `in` amap g (s_tq s) -> a `notin` ftv_typ (st b)).
    { intros a b Hb Ha. assert (ftv_typ (st b) [<=] ftv_ctx G') by (apply HcT; fsetdec).
      assert (a `notin` Bav) by (apply HgF; exact Ha). unfold Bav in *. fsetdec. }
    assert (Hnc2 : forall a r, r `in` frv_sch s -> a `in` amap g (s_tq s) -> a `notin` ftv_row (sr r)).
    { intros a r Hr Ha. assert (ftv_row (sr r) [<=] ftv_ctx G') by (apply HcRt; fsetdec).
      assert (a `notin` Bav) by (apply HgF; exact Ha). unfold Bav in *. fsetdec. }
    assert (Hnc3 : forall p b, b `in` ftv_sch s -> p `in` amap gr (s_rq s) -> p `notin` frv_typ (st b)).
    { intros p b Hb Hp. assert (frv_typ (st b) [<=] frv_ctx G') by (apply HcFr; fsetdec).
      assert (p `notin` Bav) by (apply HgrF; exact Hp). unfold Bav in *. fsetdec. }
    assert (Hnc4 : forall p r, r `in` frv_sch s -> p `in` amap gr (s_rq s) -> p `notin` frv_row (sr r)).
    { intros p r Hr Hp. assert (frv_row (sr r) [<=] frv_ctx G') by (apply HcRfr; fsetdec).
      assert (p `notin` Bav) by (apply HgrF; exact Hp). unfold Bav in *. fsetdec. }
    (* the capture-avoiding substituted scheme preserves instances *)
    assert (Hcaschinst : sch_subst st sr s (casch st sr g gr s)).
    { intros W HW. apply casch_inst; auto. }
    (* ... and lines up with gen over G' *)
    assert (Hbridge : sch_equiv (casch st sr g gr s)
                        (gen G' (ap_typ st sr (ren_typ g gr (s_body s))))).
    { unfold gen. apply casch_gen_sch_equiv.
      - exact Hginv.
      - exact Hgrinv.
      - exact HgfixS.
      - exact HgrfixS.
      - unfold s, gen; simpl. fsetdec.
      - unfold s, gen; simpl. fsetdec.
      - exact HstQ.
      - exact HsrQ.
      - intros a Ha. assert (a `notin` Bav) by (apply HgF; exact Ha). unfold Bav in *. fsetdec.
      - intros r Hr. assert (r `notin` Bav) by (apply HgrF; exact Hr). unfold Bav in *. fsetdec.
      - intros a Ha. apply HcT. fsetdec.
      - intros r Hr. apply HcRt. fsetdec.
      - intros a Ha. apply HcFr. fsetdec.
      - intros r Hr. apply HcRfr. fsetdec. }
    set (B' := ap_typ st sr (ren_typ g gr T1)).
    assert (HbodyT1 : s_body s = T1) by (unfold s, gen; reflexivity).
    apply T_Let with (L := L0 `union` dom G') (T1 := B').
    + (* e1 : B' *)
      unfold B'. rewrite <- ap_precomp.
      set (A2 := A `union` s_tq s `union` lset Ng `union` s_rq s `union` lset Ngr).
      apply (IH1 (fun a => st (g a)) (fun r => sr (gr r)) G' A2 Hu').
      * apply ctx_subst_precomp; [ exact Hcs | exact HgfixG | exact HgrfixG ].
      * (* tr_supp *)
        split.
        -- intros a Ha. unfold A2 in Ha.
           assert (g a = a).
           { apply Hgfix; [ fsetdec | ]. intro Hc. apply lset_in in Hc. fsetdec. }
           rewrite H. apply HsuppT. fsetdec.
        -- intros r Hr. unfold A2 in Hr.
           assert (gr r = r).
           { apply Hgrfix; [ fsetdec | ]. intro Hc. apply lset_in in Hc. fsetdec. }
           rewrite H. apply HsuppR. fsetdec.
      * (* tr_compat *)
        unfold tr_compat. repeat split.
        -- intros a Ha. rewrite (HgfixG a Ha). apply HcT; exact Ha.
        -- intros a Ha. rewrite (HgfixG a Ha). apply HcFr; exact Ha.
        -- intros r Hr. rewrite (HgrfixG r Hr). apply HcRt; exact Hr.
        -- intros r Hr. rewrite (HgrfixG r Hr). apply HcRfr; exact Hr.
    + (* body *)
      intros x Hx.
      apply typing_sch_equiv_ctx with (G := (x ~ casch st sr g gr s) ++ G').
      * apply (IH2 x ltac:(fsetdec) st sr ((x ~ casch st sr g gr s) ++ G') A).
        -- constructor; [ assumption | fsetdec ].
        -- apply ctx_subst_cons; [ exact Hcaschinst | exact Hcs ].
        -- split; [exact HsuppT | exact HsuppR].
        -- (* tr_compat for extended ctx *)
           unfold tr_compat; simpl. repeat split.
           ++ intros a Ha. intros z Hz. apply AtomSetFacts.union_iff. right.
              apply (HcT a); [ assert (ftv_sch s [<=] ftv_ctx G) by exact HsubST; fold s; fsetdec | exact Hz ].
           ++ intros a Ha. intros z Hz. apply AtomSetFacts.union_iff. right.
              apply (HcFr a); [ fold s; fsetdec | exact Hz ].
           ++ intros r Hr. intros z Hz. apply AtomSetFacts.union_iff. right.
              apply (HcRt r); [ fold s; fsetdec | exact Hz ].
           ++ intros r Hr. intros z Hz. apply AtomSetFacts.union_iff. right.
              apply (HcRfr r); [ fold s; fsetdec | exact Hz ].
      * apply ctx_equiv_cons; [ | apply ctx_equiv_refl ].
        rewrite HbodyT1 in Hbridge. fold B' in Hbridge. exact Hbridge.
  - (* T_Record *) intros G fs R Ht IH st sr G' A Hu' Hcs Hsupp Hcompat. simpl.
    apply T_Record. eapply IH; eauto.
  - (* T_Proj *) intros G e l T R Ht IH st sr G' A Hu' Hcs Hsupp Hcompat.
    eapply T_Proj. simpl in IH. eapply IH; eauto.
  - (* T_Conv *) intros G e T T' Ht IH Hte st sr G' A Hu' Hcs Hsupp Hcompat.
    eapply T_Conv; [ eapply IH; eauto | apply teq_ap; auto ].
  - intros G Hu st sr G' A Hu' Hcs Hsupp Hcompat. simpl. apply FT_nil; auto.
  - intros G l e T fs R Ht1 IH1 Ht2 IH2 st sr G' A Hu' Hcs Hsupp Hcompat. simpl.
    eapply FT_cons; [ eapply IH1 | eapply IH2 ]; eauto.
Qed.

(* L5, context-fixing form: substituting the type/row variables NOT free in the
   context preserves typing.  Specialize the general lemma to [G' = G] via a
   finitely-supported substitution agreeing with [st,sr] on [T]. *)
Lemma typing_tsubst_fix : forall G e T st sr,
  typing G e T ->
  (forall a, a `in` ftv_ctx G -> st a = typ_Var a) ->
  (forall r, r `in` frv_ctx G -> sr r = row_Var r) ->
  typing G e (ap_typ st sr T).
Proof.
  intros G e T st sr Hty Hfa Hfr.
  set (st0 := fun a => if AtomSetImpl.mem a (ftv_typ T) then st a else typ_Var a).
  set (sr0 := fun r => if AtomSetImpl.mem r (frv_typ T) then sr r else row_Var r).
  assert (Heq : ap_typ st0 sr0 T = ap_typ st sr T).
  { apply ap_typ_ext.
    - intros a Ha. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ T)) eqn:Em;
        [reflexivity | apply AtomSetFacts.not_mem_iff in Em; contradiction].
    - intros r Hr. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ T)) eqn:Em;
        [reflexivity | apply AtomSetFacts.not_mem_iff in Em; contradiction]. }
  rewrite <- Heq.
  apply (proj1 typing_tsubst_gen_mut G e T Hty st0 sr0 G (ftv_typ T `union` frv_typ T)).
  - eapply typing_uniq; eauto.
  - (* ctx_subst st0 sr0 G G *)
    apply ctx_subst_fix.
    + intros a Ha. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ T)) eqn:Em;
        [ apply Hfa; auto | reflexivity ].
    + intros r Hr. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ T)) eqn:Em;
        [ apply Hfr; auto | reflexivity ].
  - (* tr_supp *)
    split.
    + intros a Ha. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ T)) eqn:Em;
        [ apply AtomSetFacts.mem_iff in Em; exfalso; fsetdec | reflexivity ].
    + intros r Hr. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ T)) eqn:Em;
        [ apply AtomSetFacts.mem_iff in Em; exfalso; fsetdec | reflexivity ].
  - (* tr_compat st0 sr0 G G *)
    unfold tr_compat. repeat split.
    + intros a Ha. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ T)) eqn:Em.
      * rewrite (Hfa a Ha). simpl. fsetdec.
      * simpl. fsetdec.
    + intros a Ha. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ T)) eqn:Em.
      * rewrite (Hfa a Ha). simpl. fsetdec.
      * simpl. fsetdec.
    + intros r Hr. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ T)) eqn:Em.
      * rewrite (Hfr r Hr). simpl. fsetdec.
      * simpl. fsetdec.
    + intros r Hr. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ T)) eqn:Em.
      * rewrite (Hfr r Hr). simpl. fsetdec.
      * simpl. fsetdec.
Qed.

(* L4 (weakening): inserting a middle block preserves typing -- the identity
   substitution into a larger context, via the general lemma. *)
Lemma typing_weaken : forall E F G e T,
  typing (E ++ G) e T ->
  uniq (E ++ F ++ G) ->
  typing (E ++ F ++ G) e T.
Proof.
  intros E F G e T Hty Hu.
  assert (Heq : ap_typ idt idr T = T) by (apply ap_typ_pointwise_id; reflexivity).
  rewrite <- Heq.
  apply (proj1 typing_tsubst_gen_mut (E ++ G) e T Hty idt idr (E ++ F ++ G) {}).
  - exact Hu.
  - apply ctx_subst_weaken. intros x s Hb. apply binds_weaken; exact Hb.
  - split; intros a Ha; reflexivity.
  - unfold tr_compat. repeat split; intros a Ha.
    + (* ftv idt a = {a} subset ftv_ctx (E++F++G) *)
      unfold idt; simpl.
      assert (a `in` ftv_ctx (E ++ F ++ G)).
      { rewrite !ftv_ctx_app. rewrite ftv_ctx_app in Ha. fsetdec. }
      fsetdec.
    + unfold idt; simpl. fsetdec.
    + unfold idr; simpl. fsetdec.
    + unfold idr; simpl.
      assert (a `in` frv_ctx (E ++ F ++ G)).
      { rewrite !frv_ctx_app. rewrite frv_ctx_app in Ha. fsetdec. }
      fsetdec.
Qed.
(* A term with a generalizable type has every instance of its
   generalization (L5 specialized to [gen]). *)
Lemma typing_inst_gen : forall G v T1 W,
  typing G v T1 -> inst W (gen G T1) -> typing G v W.
Proof.
  intros G v T1 W Hv [st [sr [Hst [Hsr Heq]]]].
  simpl in Heq. subst W.
  apply typing_tsubst_fix; auto.
  - intros a Ha. apply Hst. simpl. fsetdec.
  - intros r Hr. apply Hsr. simpl. fsetdec.
Qed.

(* ================================================================== *)
(* L6a: monomorphic term substitution (for ST-Beta).                     *)
(* ================================================================== *)

Lemma typing_subst_mut : forall x U u G1,
  typing G1 u U ->
  (forall Gm e T, typing Gm e T ->
     forall G2, Gm = G2 ++ (x ~ sch_mono U) ++ G1 ->
     typing (G2 ++ G1) (subst_exp u x e) T) /\
  (forall Gm fs R, field_typing Gm fs R ->
     forall G2, Gm = G2 ++ (x ~ sch_mono U) ++ G1 ->
     field_typing (G2 ++ G1) (subst_fields u x fs) R).
Proof.
  intros x U u G1 Hu.
  apply typing_field_mutind.
  - (* T_Var *) intros G y s T Huq Hb Hi G2 Heq; subst.
    destruct (y == x) as [Hx|Hx].
    + subst y.
      assert (s = sch_mono U) as Hs by (eapply binds_mid_eq; [ exact Hb | exact Huq ]).
      subst s. apply inst_mono_eq in Hi. subst T. rewrite subst_self.
      apply (typing_weaken nil G2 G1 u U Hu). simpl_alist. solve_uniq.
    + rewrite subst_neq by congruence.
      apply T_Var with (s := s);
        [ solve_uniq | eapply binds_remove_mid; [ exact Hb | congruence ] | exact Hi ].
  - (* T_Num *) intros G n Huq G2 Heq; subst. simpl. apply T_Num. solve_uniq.
  - (* T_True *) intros G Huq G2 Heq; subst. simpl. apply T_True. solve_uniq.
  - (* T_False *) intros G Huq G2 Heq; subst. simpl. apply T_False. solve_uniq.
  - (* T_Abs *) intros L G e T1 T2 Hr IH G2 Heq; subst. simpl.
    apply T_Abs with (L := L `union` dom (G2 ++ G1) `union` {{x}} `union` fv_exp u).
    intros x0 Hx0.
    rewrite <- (subst_open_var e u x x0) by
      (first [ fsetdec | eapply typing_regular; exact Hu ]).
    rewrite_env (((x0 ~ sch_mono T1) ++ G2) ++ G1).
    apply (IH x0 ltac:(fsetdec) ((x0 ~ sch_mono T1) ++ G2)). simpl_alist. reflexivity.
  - (* T_App *) intros G e1 e2 T1 T2 Hr1 IH1 Hr2 IH2 G2 Heq; subst. simpl. eapply T_App.
    + apply (IH1 G2); reflexivity.
    + apply (IH2 G2); reflexivity.
  - (* T_Let *) intros L G e1 e2 T1 T2 Hr1 IH1 Hr2 IH2 G2 Heq; subst. simpl.
    apply T_Let with (L := L `union` dom (G2 ++ G1) `union` {{x}} `union` fv_exp u) (T1 := T1).
    + apply (IH1 G2); reflexivity.
    + intros x0 Hx0.
      rewrite <- (subst_open_var e2 u x x0) by
        (first [ fsetdec | eapply typing_regular; exact Hu ]).
      eapply typing_ftv_mono.
      * rewrite_env (((x0 ~ gen (G2 ++ (x ~ sch_mono U) ++ G1) T1) ++ G2) ++ G1).
        apply (IH2 x0 ltac:(fsetdec) ((x0 ~ gen (G2 ++ (x ~ sch_mono U) ++ G1) T1) ++ G2)).
        simpl_alist. reflexivity.
      * simpl_alist. apply ctx_more_gen_cons; [ | apply ctx_more_gen_refl ].
        apply gen_antimono; rewrite ?ftv_ctx_app, ?frv_ctx_app; simpl; fsetdec.
  - (* T_Record *) intros G fs R Hr IH G2 Heq; subst. simpl. apply T_Record. apply (IH G2); reflexivity.
  - (* T_Proj *) intros G e l T R Hr IH G2 Heq; subst. simpl. eapply T_Proj. apply (IH G2); reflexivity.
  - (* T_Conv *) intros G e T T' Hr IH Hteq G2 Heq; subst. eapply T_Conv; [ apply (IH G2); reflexivity | exact Hteq ].
  - (* FT_nil *) intros G Huq G2 Heq; subst. simpl. apply FT_nil. solve_uniq.
  - (* FT_cons *) intros G l e T fs R Hr1 IH1 Hr2 IH2 G2 Heq; subst. simpl. eapply FT_cons.
    + apply (IH1 G2); reflexivity.
    + apply (IH2 G2); reflexivity.
Qed.

Lemma typing_subst : forall G x U e T u,
  typing ((x ~ sch_mono U) ++ G) e T ->
  typing G u U ->
  typing G (subst_exp u x e) T.
Proof.
  intros G x U e T u Hty Hu.
  exact (proj1 (typing_subst_mut x U u G Hu) _ e T Hty nil eq_refl).
Qed.

(* ================================================================== *)
(* L6b: polymorphic term substitution (for ST-LetV).                     *)
(* ================================================================== *)

Lemma typing_subst_poly_mut : forall x T1 v G1,
  typing G1 v T1 ->
  (forall Gm e T, typing Gm e T ->
     forall G2, Gm = G2 ++ (x ~ gen G1 T1) ++ G1 ->
     typing (G2 ++ G1) (subst_exp v x e) T) /\
  (forall Gm fs R, field_typing Gm fs R ->
     forall G2, Gm = G2 ++ (x ~ gen G1 T1) ++ G1 ->
     field_typing (G2 ++ G1) (subst_fields v x fs) R).
Proof.
  intros x T1 v G1 Hv.
  apply typing_field_mutind.
  - (* T_Var *) intros G y s T Huq Hb Hi G2 Heq; subst.
    destruct (y == x) as [Hx|Hx].
    + subst y.
      assert (s = gen G1 T1) as Hs by (eapply binds_mid_eq; [ exact Hb | exact Huq ]).
      subst s.
      assert (typing G1 v T) as HvT by (eapply typing_inst_gen; [ exact Hv | exact Hi ]).
      rewrite subst_self.
      apply (typing_weaken nil G2 G1 v T HvT). simpl_alist. solve_uniq.
    + rewrite subst_neq by congruence.
      apply T_Var with (s := s);
        [ solve_uniq | eapply binds_remove_mid; [ exact Hb | congruence ] | exact Hi ].
  - (* T_Num *) intros G n Huq G2 Heq; subst. simpl. apply T_Num. solve_uniq.
  - (* T_True *) intros G Huq G2 Heq; subst. simpl. apply T_True. solve_uniq.
  - (* T_False *) intros G Huq G2 Heq; subst. simpl. apply T_False. solve_uniq.
  - (* T_Abs *) intros L G e T0 T2 Hr IH G2 Heq; subst. simpl.
    apply T_Abs with (L := L `union` dom (G2 ++ G1) `union` {{x}} `union` fv_exp v).
    intros x0 Hx0.
    rewrite <- (subst_open_var e v x x0) by
      (first [ fsetdec | eapply typing_regular; exact Hv ]).
    rewrite_env (((x0 ~ sch_mono T0) ++ G2) ++ G1).
    apply (IH x0 ltac:(fsetdec) ((x0 ~ sch_mono T0) ++ G2)). simpl_alist. reflexivity.
  - (* T_App *) intros G e1 e2 T0 T2 Hr1 IH1 Hr2 IH2 G2 Heq; subst. simpl. eapply T_App.
    + apply (IH1 G2); reflexivity.
    + apply (IH2 G2); reflexivity.
  - (* T_Let *) intros L G e1 e2 T0 T2 Hr1 IH1 Hr2 IH2 G2 Heq; subst. simpl.
    apply T_Let with (L := L `union` dom (G2 ++ G1) `union` {{x}} `union` fv_exp v) (T1 := T0).
    + apply (IH1 G2); reflexivity.
    + intros x0 Hx0.
      rewrite <- (subst_open_var e2 v x x0) by
        (first [ fsetdec | eapply typing_regular; exact Hv ]).
      eapply typing_ftv_mono.
      * rewrite_env (((x0 ~ gen (G2 ++ (x ~ gen G1 T1) ++ G1) T0) ++ G2) ++ G1).
        apply (IH2 x0 ltac:(fsetdec) ((x0 ~ gen (G2 ++ (x ~ gen G1 T1) ++ G1) T0) ++ G2)).
        simpl_alist. reflexivity.
      * simpl_alist. apply ctx_more_gen_cons; [ | apply ctx_more_gen_refl ].
        apply gen_antimono; rewrite ?ftv_ctx_app, ?frv_ctx_app; simpl; fsetdec.
  - (* T_Record *) intros G fs R Hr IH G2 Heq; subst. simpl. apply T_Record. apply (IH G2); reflexivity.
  - (* T_Proj *) intros G e l T R Hr IH G2 Heq; subst. simpl. eapply T_Proj. apply (IH G2); reflexivity.
  - (* T_Conv *) intros G e T T' Hr IH Hteq G2 Heq; subst. eapply T_Conv; [ apply (IH G2); reflexivity | exact Hteq ].
  - (* FT_nil *) intros G Huq G2 Heq; subst. simpl. apply FT_nil. solve_uniq.
  - (* FT_cons *) intros G l e T fs R Hr1 IH1 Hr2 IH2 G2 Heq; subst. simpl. eapply FT_cons.
    + apply (IH1 G2); reflexivity.
    + apply (IH2 G2); reflexivity.
Qed.

Lemma typing_subst_poly : forall G x T1 e T2 v,
  typing ((x ~ gen G T1) ++ G) e T2 ->
  typing G v T1 ->
  typing G (subst_exp v x e) T2.
Proof.
  intros G x T1 e T2 v Hty Hv.
  exact (proj1 (typing_subst_poly_mut x T1 v G Hv) _ e T2 Hty nil eq_refl).
Qed.

(* ================================================================== *)
(* Preservation (docs/semantics.md section 7).                          *)
(* ================================================================== *)

Scheme step_mut := Induction for step Sort Prop
with   step_fields_mut := Induction for step_fields Sort Prop.
Combined Scheme step_step_fields_mutind from step_mut, step_fields_mut.

Lemma preservation_mut :
  (forall e e', step e e' -> forall G T, typing G e T -> typing G e' T) /\
  (forall fs fs', step_fields fs fs' ->
     forall G R, field_typing G fs R -> field_typing G fs' R).
Proof.
  apply step_step_fields_mutind.
  - (* st_beta: (abs e) v --> open e v *)
    intros e v Hv G T Hty.
    apply app_inv in Hty. destruct Hty as [A [B [Habs [Harg Hbt]]]].
    apply abs_inv in Habs. destruct Habs as [L [A' [B' [Hbody Harr]]]].
    apply teq_Arrow_inv in Harr. destruct Harr as [A2 [B2 [Heq [HA HB]]]].
    inversion Heq; subst.
    pick fresh x for (L \u fv_exp e).
    assert (HxL : x `notin` L) by fsetdec.
    assert (Hxe : x `notin` fv_exp e) by fsetdec.
    assert (Hv' : typing G v A') by (eapply T_Conv; [ exact Harg | apply teq_sym; exact HA ]).
    assert (Hopen : typing G (subst_exp v x (open_exp_wrt_exp e (e_fvar_f x))) B')
      by (eapply typing_subst; [ apply Hbody; exact HxL | exact Hv' ]).
    rewrite <- subst_intro in Hopen by exact Hxe.
    eapply T_Conv; [ exact Hopen | ].
    eapply teq_trans; [ exact HB | exact Hbt ].
  - (* st_app1 *)
    intros e1 e1' e2 Hstep IH G T Hty.
    apply app_inv in Hty. destruct Hty as [A [B [Hty1 [Hty2 Hbt]]]].
    eapply T_Conv; [ eapply T_App; [ apply IH; exact Hty1 | exact Hty2 ] | exact Hbt ].
  - (* st_app2 *)
    intros v e2 e2' Hv Hstep IH G T Hty.
    apply app_inv in Hty. destruct Hty as [A [B [Hty1 [Hty2 Hbt]]]].
    eapply T_Conv; [ eapply T_App; [ exact Hty1 | apply IH; exact Hty2 ] | exact Hbt ].
  - (* st_letv: (let v e2) --> open e2 v *)
    intros v e2 Hv G T Hty.
    apply let_inv in Hty. destruct Hty as [L [T1 [T2 [Hty1 [Hbody Hteq]]]]].
    pick fresh x for (L \u fv_exp e2).
    assert (HxL : x `notin` L) by fsetdec.
    assert (Hxe : x `notin` fv_exp e2) by fsetdec.
    assert (Hopen : typing G (subst_exp v x (open_exp_wrt_exp e2 (e_fvar_f x))) T2)
      by (eapply typing_subst_poly; [ apply Hbody; exact HxL | exact Hty1 ]).
    rewrite <- subst_intro in Hopen by exact Hxe.
    eapply T_Conv; [ exact Hopen | exact Hteq ].
  - (* st_let1 *)
    intros e1 e1' e2 Hstep IH G T Hty.
    apply let_inv in Hty. destruct Hty as [L [T1 [T2 [Hty1 [Hbody Hteq]]]]].
    eapply T_Conv; [ eapply T_Let with (L := L) (T1 := T1);
                     [ apply IH; exact Hty1 | exact Hbody ] | exact Hteq ].
  - (* st_proj *)
    intros e e' l Hstep IH G T Hty.
    apply proj_inv in Hty. destruct Hty as [T0 [R [Hty0 Hteq]]].
    eapply T_Conv; [ eapply T_Proj; apply IH; exact Hty0 | exact Hteq ].
  - (* st_projrec *)
    intros fs l v Hrv Hlook G T Hty.
    apply proj_inv in Hty. destruct Hty as [T0 [R [Hrec Hteq]]].
    apply rec_inv in Hrec. destruct Hrec as [R' [Hft Hreq]].
    apply teq_Record_inv in Hreq. destruct Hreq as [R2 [Heq Hreq]].
    inversion Heq; subst.
    apply req_surface in Hreq. destruct Hreq as [T1 [rest [Hpi Hteq1]]].
    destruct (field_lookup_some _ _ _ _ _ _ Hft Hpi) as [v0 [Hlook0 Hty0]].
    assert (v0 = v) by congruence. subst v0.
    eapply T_Conv; [ exact Hty0 | ].
    eapply teq_trans; [ exact Hteq1 | exact Hteq ].
  - (* st_rec *)
    intros fs fs' Hstep IHf G T Hty.
    apply rec_inv in Hty. destruct Hty as [R [Hft Hteq]].
    eapply T_Conv; [ eapply T_Record; apply IHf; exact Hft | exact Hteq ].
  - (* stf_here *)
    intros l e e' fs Hstep IH G R Hft.
    inversion Hft; subst.
    eapply FT_cons; [ apply IH; eassumption | eassumption ].
  - (* stf_cons *)
    intros l v fs fs' Hv Hstep IHf G R Hft.
    inversion Hft; subst.
    eapply FT_cons; [ eassumption | apply IHf; eassumption ].
Qed.

Theorem preservation : forall G e e' T,
  typing G e T -> step e e' -> typing G e' T.
Proof. intros G e e' T Hty Hstep. eapply (proj1 preservation_mut); eauto. Qed.

(* ================================================================== *)
(* Soundness (docs/semantics.md section 7): a well-typed closed term     *)
(* never reaches a stuck state.                                           *)
(* ================================================================== *)

Theorem soundness : forall e T e',
  typing nil e T -> multistep e e' -> value e' \/ exists e'', step e' e''.
Proof.
  intros e T e' Hty Hms. revert T Hty.
  induction Hms as [ e | e1 e2 e3 Hstep Hms IH ]; intros T Hty.
  - (* refl *) apply progress with (T := T); exact Hty.
  - (* step *) apply IH with (T := T). eapply preservation; eauto.
Qed.

Corollary soundness_not_stuck : forall e T e',
  typing nil e T -> multistep e e' -> ~ stuck e'.
Proof.
  intros e T e' Hty Hms [Hnv Hns].
  destruct (soundness _ _ _ Hty Hms) as [Hv | [e'' Hstep]].
  - contradiction.
  - eapply Hns; exact Hstep.
Qed.
