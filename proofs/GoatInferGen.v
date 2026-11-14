(* Instantiation and generalization in algorithm W (GoatInfer.v): what the
   scheme the algorithm builds at a [let] and the instance it takes at a
   variable mean against [inst] and [gen]. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatHM.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferTyp.
Require Import Stdlib.Lists.List.
Import ListNotations.

Lemma aset_in : forall a l, a `in` aset l <-> In a l.
Proof.
  intros a l. induction l as [|b l IH]; simpl.
  - split; [ fsetdec | intros [] ].
  - rewrite AtomSetFacts.add_iff, IH. split.
    + intros [H|H]; [left; auto | right; auto].
    + intros [H|H]; [left; auto | right; auto].
Qed.

Lemma ftv_ctx_even : forall G a, WfCtx G -> a `in` ftv_ctx G -> ev a.
Proof.
  intros G a [Hu Hw] Ha. destruct (ftv_ctx_has _ _ Ha) as [x [sc [Hb Hin]]].
  exact ((proj1 (proj2 (proj2 (Hw _ _ Hb)))) a Hin).
Qed.

Lemma frv_ctx_even : forall G a, WfCtx G -> a `in` frv_ctx G -> ev a.
Proof.
  intros G a [Hu Hw] Ha. destruct (frv_ctx_has _ _ Ha) as [x [sc [Hb Hin]]].
  exact ((proj2 (proj2 (proj2 (Hw _ _ Hb)))) a Hin).
Qed.

(* ------------------------------------------------------------------ *)
(* Instantiation                                                        *)
(* ------------------------------------------------------------------ *)

Lemma instantiate_sound : forall sc n T n',
  instantiate sc n = (T, n') -> WfSch sc -> inst T sc /\ EvT T.
Proof.
  intros sc n T n' H (Hq & Hr & Hf & Hfr).
  unfold instantiate in H. inversion H; subst T n'; clear H.
  split.
  - exists (sT (inst_sub sc n)), (sR (inst_sub sc n)). split; [|split].
    + intros a Ha. unfold inst_sub; cbn [sT].
      destruct (in_dec Atom.eq_dec a (AtomSetImpl.elements (s_tq sc))) as [Hin|Hin];
        [ apply In_elements in Hin; contradiction | reflexivity ].
    + intros r Hr0. unfold inst_sub; cbn [sR].
      destruct (in_dec Atom.eq_dec r (AtomSetImpl.elements (s_rq sc))) as [Hin|Hin];
        [ apply In_elements in Hin; contradiction | reflexivity ].
    + reflexivity.
  - split; intros c Hc.
    + apply ftv_ap_typ in Hc. destruct Hc as [[b [Hb Hc]]|[p [Hp Hc]]].
      * unfold inst_sub in Hc; cbn [sT] in Hc.
        destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))) as [Hin|Hin].
        -- simpl in Hc. apply AtomSetFacts.singleton_iff in Hc. subst. apply ev_ea.
        -- simpl in Hc. apply AtomSetFacts.singleton_iff in Hc. subst.
           apply Hf. unfold ftv_sch. apply AtomSetFacts.diff_iff. split; [exact Hb|].
           intro Hq0. apply Hin. apply In_elements. exact Hq0.
      * unfold inst_sub in Hc; cbn [sR] in Hc.
        destruct (in_dec Atom.eq_dec p (AtomSetImpl.elements (s_rq sc))); simpl in Hc; fsetdec.
    + apply frv_ap_typ in Hc. destruct Hc as [[b [Hb Hc]]|[p [Hp Hc]]].
      * unfold inst_sub in Hc; cbn [sT] in Hc.
        destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))); simpl in Hc; fsetdec.
      * unfold inst_sub in Hc; cbn [sR] in Hc.
        destruct (in_dec Atom.eq_dec p (AtomSetImpl.elements (s_rq sc))) as [Hin|Hin].
        -- simpl in Hc. apply AtomSetFacts.singleton_iff in Hc. subst. apply ev_ea.
        -- simpl in Hc. apply AtomSetFacts.singleton_iff in Hc. subst.
           apply Hfr. unfold frv_sch. apply AtomSetFacts.diff_iff. split; [exact Hp|].
           intro Hq0. apply Hin. apply In_elements. exact Hq0.
Qed.

(* ------------------------------------------------------------------ *)
(* Generalization                                                       *)
(* ------------------------------------------------------------------ *)

Section Gen.
Variables (G : ctx) (T : typ).

Let la := gen_vars_t G T.
Let lr := gen_vars_r G T.

Lemma In_la : forall a, In a la <-> a `in` ftv_typ T /\ a `notin` ftv_ctx G.
Proof.
  intros a. unfold la, gen_vars_t. rewrite In_elements, AtomSetFacts.diff_iff. tauto.
Qed.

Lemma In_lr : forall a, In a lr <-> a `in` frv_typ T /\ a `notin` frv_ctx G.
Proof.
  intros a. unfold lr, gen_vars_r. rewrite In_elements, AtomSetFacts.diff_iff. tauto.
Qed.

Lemma gen_ren_tq : forall a,
  a `in` s_tq (gen_ren G T) <-> exists b, In b la /\ a = oa (idx b la).
Proof.
  intros a. cbn [gen_ren s_tq]. fold la. rewrite aset_in, in_map_iff. split.
  - intros [b [Hb Hin]]. exists b. split; [exact Hin | symmetry; exact Hb].
  - intros [b [Hb Hin]]. exists b. split; [symmetry; exact Hin | exact Hb].
Qed.

Lemma gen_ren_rq : forall a,
  a `in` s_rq (gen_ren G T) <-> exists b, In b lr /\ a = oa (idx b lr).
Proof.
  intros a. cbn [gen_ren s_rq]. fold lr. rewrite aset_in, in_map_iff. split.
  - intros [b [Hb Hin]]. exists b. split; [exact Hin | symmetry; exact Hb].
  - intros [b [Hb Hin]]. exists b. split; [symmetry; exact Hin | exact Hb].
Qed.

Lemma gen_body : s_body (gen_ren G T) = ap_typ (rename_t la) (rename_r lr) T.
Proof. reflexivity. Qed.

(* Where the free variables of the renamed body come from. *)
Lemma body_ftv : forall a, a `in` ftv_typ (s_body (gen_ren G T)) ->
  a `in` s_tq (gen_ren G T) \/ (a `in` ftv_typ T /\ ~ In a la).
Proof.
  intros a Ha. rewrite gen_body in Ha. apply ftv_ap_typ in Ha.
  destruct Ha as [[b [Hb Ha]]|[p [Hp Ha]]].
  - unfold rename_t in Ha.
    destruct (in_dec Atom.eq_dec b la) as [Hin|Hin].
    + simpl in Ha. apply AtomSetFacts.singleton_iff in Ha. subst a. left.
      apply gen_ren_tq. exists b. split; auto.
    + simpl in Ha. apply AtomSetFacts.singleton_iff in Ha. subst a. right. split; auto.
  - unfold rename_r in Ha. destruct (in_dec Atom.eq_dec p lr); simpl in Ha; fsetdec.
Qed.

Lemma body_frv : forall a, a `in` frv_typ (s_body (gen_ren G T)) ->
  a `in` s_rq (gen_ren G T) \/ (a `in` frv_typ T /\ ~ In a lr).
Proof.
  intros a Ha. rewrite gen_body in Ha. apply frv_ap_typ in Ha.
  destruct Ha as [[b [Hb Ha]]|[p [Hp Ha]]].
  - unfold rename_t in Ha. destruct (in_dec Atom.eq_dec b la); simpl in Ha; fsetdec.
  - unfold rename_r in Ha.
    destruct (in_dec Atom.eq_dec p lr) as [Hin|Hin].
    + simpl in Ha. apply AtomSetFacts.singleton_iff in Ha. subst a. left.
      apply gen_ren_rq. exists p. split; auto.
    + simpl in Ha. apply AtomSetFacts.singleton_iff in Ha. subst a. right. split; auto.
Qed.

(* Every quantified atom is a free variable of the renamed body. *)
Lemma tq_in_body : forall a, a `in` s_tq (gen_ren G T) ->
  a `in` ftv_typ (s_body (gen_ren G T)).
Proof.
  intros a Ha. apply gen_ren_tq in Ha. destruct Ha as [b [Hb ->]].
  apply In_la in Hb. rewrite gen_body.
  eapply ftv_ap_in1; [ exact (proj1 Hb) | ].
  unfold rename_t. destruct (in_dec Atom.eq_dec b la) as [Hin|Hin];
    [ simpl; fsetdec | exfalso; apply Hin; apply In_la; exact Hb ].
Qed.

Lemma rq_in_body : forall a, a `in` s_rq (gen_ren G T) ->
  a `in` frv_typ (s_body (gen_ren G T)).
Proof.
  intros a Ha. apply gen_ren_rq in Ha. destruct Ha as [b [Hb ->]].
  apply In_lr in Hb. rewrite gen_body.
  eapply frv_ap_in2; [ exact (proj1 Hb) | ].
  unfold rename_r. destruct (in_dec Atom.eq_dec b lr) as [Hin|Hin];
    [ simpl; fsetdec | exfalso; apply Hin; apply In_lr; exact Hb ].
Qed.

Lemma gen_ren_od_t : forall a, a `in` s_tq (gen_ren G T) -> od a.
Proof. intros a Ha. apply gen_ren_tq in Ha. destruct Ha as [b [_ ->]]. apply od_oa. Qed.

Lemma gen_ren_od_r : forall a, a `in` s_rq (gen_ren G T) -> od a.
Proof. intros a Ha. apply gen_ren_rq in Ha. destruct Ha as [b [_ ->]]. apply od_oa. Qed.

Lemma gen_ren_wf : EvT T -> WfSch (gen_ren G T).
Proof.
  intros [HT1 HT2]. split; [exact gen_ren_od_t | split; [exact gen_ren_od_r | split]].
  - intros a Ha. unfold ftv_sch in Ha. apply AtomSetFacts.diff_iff in Ha. destruct Ha as [Ha Hnq].
    destruct (body_ftv a Ha) as [H|[H _]]; [contradiction | exact (HT1 a H)].
  - intros a Ha. unfold frv_sch in Ha. apply AtomSetFacts.diff_iff in Ha. destruct Ha as [Ha Hnq].
    destruct (body_frv a Ha) as [H|[H _]]; [contradiction | exact (HT2 a H)].
Qed.

(* A derivation for the type carries over to the renamed type. *)
Lemma typing_gen_ren : forall e,
  typing G e T -> typing G e (s_body (gen_ren G T)).
Proof.
  intros e Hty. rewrite gen_body. apply typing_tsubst_fix; [exact Hty | | ].
  - intros a Ha. unfold rename_t. destruct (in_dec Atom.eq_dec a la) as [Hin|Hin];
      [ apply In_la in Hin; destruct Hin as [_ Hin]; contradiction | reflexivity ].
  - intros a Ha. unfold rename_r. destruct (in_dec Atom.eq_dec a lr) as [Hin|Hin];
      [ apply In_lr in Hin; destruct Hin as [_ Hin]; contradiction | reflexivity ].
Qed.

(* Substituting after generalizing is generalizing after substituting. *)
Lemma gen_ren_equiv : forall s, OkS s -> WfCtx G -> EvT T ->
  sch_equiv (apS s (gen_ren G T))
            (gen (apC s G) (apT s (s_body (gen_ren G T)))).
Proof.
  intros s Hs HG HT.
  pose proof (tr_compat_apC s G Hs HG) as (C1 & C2 & C3 & C4).
  pose proof (WfCtx_ap s G Hs HG) as HG'.
  pose proof Hs as Hs0.
  destruct Hs as [_ [Ht [Hrw [Hfx Hfxr]]]].
  unfold sch_equiv, gen. cbn [apS s_tq s_rq s_body].
  split; [|split; [|reflexivity]].
  - intros a. split.
    + intros Ha. apply AtomSetFacts.diff_iff. split.
      * unfold apT. eapply ftv_ap_in1; [ apply tq_in_body; exact Ha | ].
        rewrite (Hfx a (not_ev_od a (gen_ren_od_t a Ha))). simpl. fsetdec.
      * intro Hc. exact (not_ev_od a (gen_ren_od_t a Ha) (ftv_ctx_even _ _ HG' Hc)).
    + intros Ha. apply AtomSetFacts.diff_iff in Ha. destruct Ha as [Ha Hnc].
      unfold apT in Ha. apply ftv_ap_typ in Ha. destruct Ha as [[c [Hc Ha]]|[p [Hp Ha]]].
      * destruct (body_ftv c Hc) as [Hq|[Hc1 Hc2]].
        -- rewrite (Hfx c (not_ev_od c (gen_ren_od_t c Hq))) in Ha. simpl in Ha.
           apply AtomSetFacts.singleton_iff in Ha. subst. exact Hq.
        -- exfalso. apply Hnc. apply (C1 c).
           ++ destruct (in_dec_set c (ftv_ctx G)) as [H|H]; [exact H|].
              exfalso. apply Hc2. apply In_la. split; auto.
           ++ exact Ha.
      * destruct (body_frv p Hp) as [Hq|[Hc1 Hc2]].
        -- rewrite (Hfxr p (not_ev_od p (gen_ren_od_r p Hq))) in Ha. simpl in Ha. fsetdec.
        -- exfalso. apply Hnc. apply (C3 p).
           ++ destruct (in_dec_set p (frv_ctx G)) as [H|H]; [exact H|].
              exfalso. apply Hc2. apply In_lr. split; auto.
           ++ exact Ha.
  - intros a. split.
    + intros Ha. apply AtomSetFacts.diff_iff. split.
      * unfold apT. eapply frv_ap_in2; [ apply rq_in_body; exact Ha | ].
        rewrite (Hfxr a (not_ev_od a (gen_ren_od_r a Ha))). simpl. fsetdec.
      * intro Hc. exact (not_ev_od a (gen_ren_od_r a Ha) (frv_ctx_even _ _ HG' Hc)).
    + intros Ha. apply AtomSetFacts.diff_iff in Ha. destruct Ha as [Ha Hnc].
      unfold apT in Ha. apply frv_ap_typ in Ha. destruct Ha as [[c [Hc Ha]]|[p [Hp Ha]]].
      * destruct (body_ftv c Hc) as [Hq|[Hc1 Hc2]].
        -- rewrite (Hfx c (not_ev_od c (gen_ren_od_t c Hq))) in Ha. simpl in Ha. fsetdec.
        -- exfalso. apply Hnc. apply (C2 c).
           ++ destruct (in_dec_set c (ftv_ctx G)) as [H|H]; [exact H|].
              exfalso. apply Hc2. apply In_la. split; auto.
           ++ exact Ha.
      * destruct (body_frv p Hp) as [Hq|[Hc1 Hc2]].
        -- rewrite (Hfxr p (not_ev_od p (gen_ren_od_r p Hq))) in Ha. simpl in Ha.
           apply AtomSetFacts.singleton_iff in Ha. subst. exact Hq.
        -- exfalso. apply Hnc. apply (C4 p).
           ++ destruct (in_dec_set p (frv_ctx G)) as [H|H]; [exact H|].
              exfalso. apply Hc2. apply In_lr. split; auto.
           ++ exact Ha.
Qed.

End Gen.
