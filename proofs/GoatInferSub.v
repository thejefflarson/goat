(* Substitutions and contexts for the soundness proof of algorithm W
   (GoatInfer.v): the even/odd discipline, the invariant [OkS] on the
   substitutions the algorithm builds, and how it acts on contexts. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Stdlib.Lists.List.
From Stdlib Require Import Lia.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Even and odd atoms                                                   *)
(* ------------------------------------------------------------------ *)

Lemma idx_atom_in_pre : forall m n, m < n -> In (idx_atom m) (pre n).
Proof.
  induction n as [|n IH]; intros H; [lia|].
  change (In (idx_atom m) (idx_atom n :: pre n)).
  destruct (Nat.eq_dec m n) as [->|Hne].
  - left; reflexivity.
  - right; apply IH; lia.
Qed.

Lemma idx_atom_inj : forall m n, idx_atom m = idx_atom n -> m = n.
Proof.
  assert (Hlt : forall m n, m < n -> idx_atom m <> idx_atom n).
  { intros m n Hmn Heq. pose proof (idx_atom_in_pre m n Hmn) as Hin.
    rewrite Heq in Hin. exact (fresh_not_in _ Hin). }
  intros m n H. destruct (lt_eq_lt_dec m n) as [[Hl|Heq]|Hg]; auto.
  - exfalso. exact (Hlt _ _ Hl H).
  - exfalso. exact (Hlt _ _ Hg (eq_sym H)).
Qed.

Definition ev (a : atom) : Prop := exists n, a = ea n.
Definition od (a : atom) : Prop := exists n, a = oa n.

Lemma ev_od : forall a, ev a -> od a -> False.
Proof.
  intros a [n Hn] [m Hm]. subst. unfold ea, oa in Hm.
  apply idx_atom_inj in Hm. lia.
Qed.

Lemma ev_ea : forall n, ev (ea n).
Proof. intros n; exists n; reflexivity. Qed.

Lemma od_oa : forall n, od (oa n).
Proof. intros n; exists n; reflexivity. Qed.

Lemma not_ev_od : forall a, od a -> ~ ev a.
Proof. intros a Ho He. exact (ev_od a He Ho). Qed.

Definition EvS (S : atoms) : Prop := forall a, a `in` S -> ev a.
Definition EvT (T : typ) : Prop := EvS (ftv_typ T) /\ EvS (frv_typ T).
Definition EvR (R : row) : Prop := EvS (ftv_row R) /\ EvS (frv_row R).

Lemma EvT_Record : forall R, EvT (typ_Record R) <-> EvR R.
Proof. intros R; unfold EvT, EvR; simpl; tauto. Qed.

(* ------------------------------------------------------------------ *)
(* The invariant on substitutions the algorithm builds                  *)
(* ------------------------------------------------------------------ *)

Definition OkS (s : sub) : Prop :=
  (exists A : atoms, tr_supp (sT s) (sR s) A) /\
  (forall a, ev a -> EvT (sT s a)) /\
  (forall r, ev r -> EvR (sR s r)) /\
  (forall a, ~ ev a -> sT s a = typ_Var a) /\
  (forall r, ~ ev r -> sR s r = row_Var r).

Lemma EvT_ap : forall s T, OkS s -> EvT T -> EvT (apT s T).
Proof.
  intros s T (_ & Ht & Hr & _ & _) [HT1 HT2]. split; intros a Ha.
  - apply ftv_ap_typ in Ha. destruct Ha as [[b [Hb Ha]]|[p [Hp Ha]]].
    + exact ((proj1 (Ht b (HT1 b Hb))) a Ha).
    + exact ((proj1 (Hr p (HT2 p Hp))) a Ha).
  - apply frv_ap_typ in Ha. destruct Ha as [[b [Hb Ha]]|[p [Hp Ha]]].
    + exact ((proj2 (Ht b (HT1 b Hb))) a Ha).
    + exact ((proj2 (Hr p (HT2 p Hp))) a Ha).
Qed.

Lemma EvR_ap : forall s R, OkS s -> EvR R -> EvR (apR s R).
Proof.
  intros s R Hs HR. apply EvT_Record. apply (EvT_ap s (typ_Record R) Hs).
  apply EvT_Record; exact HR.
Qed.

Lemma OkS_id : OkS sid.
Proof.
  split; [|split; [|split; [|split]]].
  - exists {}. split; intros; reflexivity.
  - intros a Ha. split; intros b Hb; unfold sid, idt in Hb; simpl in Hb.
    + apply AtomSetFacts.singleton_iff in Hb. subst. exact Ha.
    + fsetdec.
  - intros a Ha. split; intros b Hb; unfold sid, idr in Hb; simpl in Hb.
    + fsetdec.
    + apply AtomSetFacts.singleton_iff in Hb. subst. exact Ha.
  - intros a Ha. reflexivity.
  - intros a Ha. reflexivity.
Qed.

Lemma OkS_comp : forall s2 s1, OkS s2 -> OkS s1 -> OkS (scomp s2 s1).
Proof.
  intros s2 s1 Hok2 Hok1.
  pose proof Hok2 as Hok2'.
  destruct Hok2 as [[A2 Hsup2] [Ht2 [Hr2 [Hf2 Hfr2]]]].
  destruct Hok1 as [[A1 Hsup1] [Ht1 [Hr1 [Hf1 Hfr1]]]].
  split; [|split; [|split; [|split]]].
  - exists (A1 `union` A2). split.
    + intros a Ha. unfold scomp, tcomp; simpl.
      rewrite (proj1 Hsup1 a) by fsetdec.
      cbn [ap_typ]. apply (proj1 Hsup2 a). fsetdec.
    + intros r Hr. unfold scomp, rcomp; simpl.
      rewrite (proj2 Hsup1 r) by fsetdec.
      cbn [ap_row]. apply (proj2 Hsup2 r). fsetdec.
  - intros a Ha. unfold scomp, tcomp; simpl.
    apply (EvT_ap s2 (sT s1 a) Hok2'). apply Ht1; exact Ha.
  - intros r Hr. unfold scomp, rcomp; simpl.
    apply (EvR_ap s2 (sR s1 r) Hok2'). apply Hr1; exact Hr.
  - intros a Ha. unfold scomp, tcomp; simpl. rewrite Hf1 by exact Ha.
    cbn [ap_typ]. apply Hf2; exact Ha.
  - intros r Hr. unfold scomp, rcomp; simpl. rewrite Hfr1 by exact Hr.
    cbn [ap_row]. apply Hfr2; exact Hr.
Qed.

Lemma OkS_sbT : forall a T, ev a -> EvT T -> OkS (sbT a T).
Proof.
  intros a T Ha HT.
  split; [|split; [|split; [|split]]].
  - exists {{a}}. split.
    + intros b Hb. unfold sbT; simpl. destruct (Atom.eq_dec b a) as [->|]; [fsetdec | reflexivity].
    + intros r Hr. reflexivity.
  - intros b Hb. unfold sbT; simpl. destruct (Atom.eq_dec b a); [ exact HT | ].
    split; intros c Hin; simpl in Hin.
    + apply AtomSetFacts.singleton_iff in Hin. subst; exact Hb.
    + fsetdec.
  - intros r Hr. unfold sbT, idr; simpl. split; intros c Hin; simpl in Hin.
    + fsetdec.
    + apply AtomSetFacts.singleton_iff in Hin. subst; exact Hr.
  - intros b Hb. unfold sbT; simpl. destruct (Atom.eq_dec b a) as [->|]; [ contradiction | reflexivity ].
  - intros r Hr. reflexivity.
Qed.

Lemma OkS_sbR : forall r R, ev r -> EvR R -> OkS (sbR r R).
Proof.
  intros r R Hr HR.
  split; [|split; [|split; [|split]]].
  - exists {{r}}. split.
    + intros b Hb. reflexivity.
    + intros s Hs. unfold sbR; simpl. destruct (Atom.eq_dec s r) as [->|]; [fsetdec | reflexivity].
  - intros b Hb. unfold sbR, idt; simpl. split; intros c Hin; simpl in Hin.
    + apply AtomSetFacts.singleton_iff in Hin. subst; exact Hb.
    + fsetdec.
  - intros s Hs. unfold sbR; simpl. destruct (Atom.eq_dec s r); [ exact HR | ].
    split; intros c Hin; simpl in Hin.
    + fsetdec.
    + apply AtomSetFacts.singleton_iff in Hin. subst; exact Hs.
  - intros b Hb. reflexivity.
  - intros s Hs. unfold sbR; simpl. destruct (Atom.eq_dec s r) as [->|]; [ contradiction | reflexivity ].
Qed.

(* Applying a substitution after another is applying the composite. *)
Lemma apT_comp : forall s2 s1 T, apT s2 (apT s1 T) = apT (scomp s2 s1) T.
Proof. intros. unfold apT, scomp; simpl. apply ap_typ_comp. Qed.

Lemma apR_comp : forall s2 s1 R, apR s2 (apR s1 R) = apR (scomp s2 s1) R.
Proof. intros. unfold apR, scomp; simpl. apply (proj2 ap_comp_mut). Qed.

(* ------------------------------------------------------------------ *)
(* Schemes and contexts                                                 *)
(* ------------------------------------------------------------------ *)

Definition apS (s : sub) (sc : scheme) : scheme :=
  Sch (s_tq sc) (s_rq sc) (apT s (s_body sc)).

Lemma apC_map : forall s G, apC s G = List.map (fun p => (fst p, apS s (snd p))) G.
Proof. reflexivity. Qed.

Lemma dom_apC : forall s G, dom (apC s G) [=] dom G.
Proof. induction G as [|[x sc] G IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma uniq_apC : forall s G, uniq G -> uniq (apC s G).
Proof.
  induction G as [|[x sc] G IH]; intros Hu; simpl; auto.
  inversion Hu; subst. constructor; auto. rewrite dom_apC; auto.
Qed.

Lemma binds_apC : forall s x sc G, binds x sc G -> binds x (apS s sc) (apC s G).
Proof.
  intros s x sc G. induction G as [|[y sy] G IH]; intros Hb; [inversion Hb|].
  simpl. apply binds_cons_1 in Hb. destruct Hb as [[Hy Hs]|Hb].
  - subst. apply binds_cons_2; reflexivity.
  - apply binds_cons_3; auto.
Qed.

Lemma apC_app : forall s G1 G2, apC s (G1 ++ G2) = apC s G1 ++ apC s G2.
Proof. intros. unfold apC. apply List.map_app. Qed.

Lemma apC_single : forall s x sc, apC s (x ~ sc) = x ~ apS s sc.
Proof. reflexivity. Qed.

Lemma apS_comp : forall s2 s1 sc, apS s2 (apS s1 sc) = apS (scomp s2 s1) sc.
Proof. intros. unfold apS; simpl. rewrite apT_comp. reflexivity. Qed.

Lemma apC_comp : forall s2 s1 G, apC s2 (apC s1 G) = apC (scomp s2 s1) G.
Proof.
  induction G as [|[x sc] G IH]; simpl; [reflexivity|].
  f_equal; [ | exact IH ]. f_equal. apply apS_comp.
Qed.

Lemma in_dec_set : forall (a : atom) (S : atoms), {a `in` S} + {a `notin` S}.
Proof.
  intros a S. destruct (AtomSetImpl.mem a S) eqn:E;
    [ left; apply AtomSetFacts.mem_iff; auto | right; apply AtomSetFacts.not_mem_iff; auto ].
Qed.

Definition WfSch (s : scheme) : Prop :=
  (forall a, a `in` s_tq s -> od a) /\ (forall r, r `in` s_rq s -> od r) /\
  EvS (ftv_sch s) /\ EvS (frv_sch s).

Definition WfCtx (G : ctx) : Prop :=
  uniq G /\ forall x s, binds x s G -> WfSch s.

Lemma WfCtx_cons : forall x s G,
  WfCtx G -> x `notin` dom G -> WfSch s -> WfCtx ((x ~ s) ++ G).
Proof.
  intros x s G [Hu Hw] Hx Hs. split.
  - constructor; auto.
  - intros y sy Hb. apply binds_cons_1 in Hb. destruct Hb as [[Hy Hsy]|Hb].
    + subst; exact Hs.
    + exact (Hw _ _ Hb).
Qed.

Lemma WfSch_mono : forall T, EvT T -> WfSch (sch_mono T).
Proof.
  intros T [H1 H2]. repeat split; simpl; try (intros a Ha; fsetdec).
  - intros a Ha. unfold ftv_sch in Ha. simpl in Ha. apply H1. fsetdec.
  - intros a Ha. unfold frv_sch in Ha. simpl in Ha. apply H2. fsetdec.
Qed.

Lemma WfSch_ap : forall s sc, OkS s -> WfSch sc -> WfSch (apS s sc).
Proof.
  intros s sc Hs (Hq & Hr & Hf & Hfr).
  pose proof Hs as Hs0.
  destruct Hs as [_ [Ht [Hrw [Hfx Hfxr]]]].
  unfold WfSch, apS. simpl. split; [exact Hq|]. split; [exact Hr|]. split.
  - intros a Ha. unfold ftv_sch in Ha. simpl in Ha.
    apply AtomSetFacts.diff_iff in Ha. destruct Ha as [Ha Hnq].
    apply ftv_ap_typ in Ha. destruct Ha as [[b [Hb Ha]]|[p [Hp Ha]]].
    + destruct (in_dec_set b (s_tq sc)) as [Hbq|Hbq].
      * pose proof (Hq b Hbq) as Hodb.
        rewrite (Hfx b (not_ev_od b Hodb)) in Ha. simpl in Ha.
        apply AtomSetFacts.singleton_iff in Ha. subst. contradiction.
      * assert (Hb' : b `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; auto).
        exact (proj1 (Ht b (Hf b Hb')) a Ha).
    + destruct (in_dec_set p (s_rq sc)) as [Hpq|Hpq].
      * pose proof (Hr p Hpq) as Hodp.
        rewrite (Hfxr p (not_ev_od p Hodp)) in Ha. simpl in Ha. fsetdec.
      * assert (Hp' : p `in` frv_sch sc) by (unfold frv_sch; apply AtomSetFacts.diff_iff; auto).
        exact (proj1 (Hrw p (Hfr p Hp')) a Ha).
  - intros a Ha. unfold frv_sch in Ha. simpl in Ha.
    apply AtomSetFacts.diff_iff in Ha. destruct Ha as [Ha Hnq].
    apply frv_ap_typ in Ha. destruct Ha as [[b [Hb Ha]]|[p [Hp Ha]]].
    + destruct (in_dec_set b (s_tq sc)) as [Hbq|Hbq].
      * pose proof (Hq b Hbq) as Hodb.
        rewrite (Hfx b (not_ev_od b Hodb)) in Ha. simpl in Ha. fsetdec.
      * assert (Hb' : b `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; auto).
        exact (proj2 (Ht b (Hf b Hb')) a Ha).
    + destruct (in_dec_set p (s_rq sc)) as [Hpq|Hpq].
      * pose proof (Hr p Hpq) as Hodp.
        rewrite (Hfxr p (not_ev_od p Hodp)) in Ha. simpl in Ha.
        apply AtomSetFacts.singleton_iff in Ha. subst. contradiction.
      * assert (Hp' : p `in` frv_sch sc) by (unfold frv_sch; apply AtomSetFacts.diff_iff; auto).
        exact (proj2 (Hrw p (Hfr p Hp')) a Ha).
Qed.

Lemma binds_apC_inv : forall s x sc G,
  binds x sc (apC s G) -> exists sc0, binds x sc0 G /\ sc = apS s sc0.
Proof.
  intros s x sc G. induction G as [|[y sy] G IH]; intros Hb; [inversion Hb|].
  simpl in Hb. apply binds_cons_1 in Hb. destruct Hb as [[Hy Hs]|Hb].
  - subst. exists sy. split; [apply binds_cons_2; reflexivity | reflexivity].
  - destruct (IH Hb) as [sc0 [Hb0 Heq]]. exists sc0. split; [apply binds_cons_3; auto | auto].
Qed.

Lemma WfCtx_ap : forall s G, OkS s -> WfCtx G -> WfCtx (apC s G).
Proof.
  intros s G Hs [Hu Hw]. split.
  - apply uniq_apC; auto.
  - intros x sc Hb. destruct (binds_apC_inv _ _ _ _ Hb) as [sc0 [Hb0 ->]].
    apply WfSch_ap; auto. exact (Hw _ _ Hb0).
Qed.
