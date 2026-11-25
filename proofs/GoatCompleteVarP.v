(* Completeness of algorithm W, stage 7.8i: a variable at a scheme, over the
   fragment (docs/design/phase7-proof-plan.md).

   [var_sch_doneT] (GoatCompleteCoreW.v) is the variable case on record-free
   schemes.  Here the scheme's body is in the fragment ([pf]) and the scheme may
   quantify rows.  The run [infer] makes at [e_fvar_f x] instantiates the scheme
   ([instantiate]: fresh atoms for the quantified atoms, then fresh row
   variables) and re-holds the equations of the entries whose presence is one of
   those fresh atoms ([rh_t]).  A scheme of the context satisfies [GPsP]: every
   entry of its body is present under the substitution that fixes its
   quantifiers, so no entry's presence is a quantified atom, and [rh_t] has
   nothing to re-hold ([rh_t_inst_none]).  The extension [fsubP] sends the fresh
   atoms and the fresh rows to the images of the derivation's instance.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferGen.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferW.
Require Import Goat.GoatHeld.
Require Import Goat.GoatCompleteHeld.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteRewrite.
Require Import Goat.GoatCompleteInst.
Require Import Goat.GoatCompleteGen.
Require Import Goat.GoatCompleteMono.
Require Import Goat.GoatCompleteDrk.
Require Import Goat.GoatCompleteEr.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteLive.
Require Import Goat.GoatCompleteLiveRf.
Require Import Goat.GoatCompleteBound.
Require Import Goat.GoatCompleteSchT.
Require Import Goat.GoatCompleteMonoT.
Require Import Goat.GoatCompleteCtxT.
Require Import Goat.GoatCompleteCtxW.
Require Import Goat.GoatCompleteCtxP.
Require Import Goat.GoatCompleteCore.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the extension at an instance ---- *)

(* [Sg] with the fresh atoms [ea (n + i)] sent to the instance's images of the
   quantified atoms and the fresh rows after them sent to its images of the
   quantified rows. *)
Definition fsubP (Sg : sub) (n : nat) (lq lr : list atom) (st : tsub) (sr : rsub) : sub :=
  Sub (fun b => fold_right (fun a acc => if Atom.eq_dec b (ea (n + idx a lq)) then st a else acc) (sT Sg b) lq)
      (fun b => fold_right (fun r acc => if Atom.eq_dec b (ea (n + length lq + idx r lr)) then sr r else acc)
                           (sR Sg b) lr).

Lemma fsubP_at : forall Sg n lq lr st sr a, In a lq -> sT (fsubP Sg n lq lr st sr) (ea (n + idx a lq)) = st a.
Proof.
  intros Sg n lq lr st sr a Ha. cbn [fsubP sT].
  apply (sel_at (fun a => ea (n + idx a lq)) st (ea (n + idx a lq)) (sT Sg (ea (n + idx a lq))) lq a Ha eq_refl).
  intros a' Ha' E. apply ea_inj in E. assert (Hi : idx a' lq = idx a lq) by lia.
  rewrite (idx_inj a' a lq Ha' Ha Hi). reflexivity.
Qed.

Lemma fsubP_out : forall Sg n lq lr st sr b,
  (forall a, In a lq -> b <> ea (n + idx a lq)) -> sT (fsubP Sg n lq lr st sr) b = sT Sg b.
Proof.
  intros Sg n lq lr st sr b H. cbn [fsubP sT].
  exact (sel_out (fun a => ea (n + idx a lq)) st b (sT Sg b) lq H).
Qed.

Lemma fsubP_rat : forall Sg n lq lr st sr r, In r lr ->
  sR (fsubP Sg n lq lr st sr) (ea (n + length lq + idx r lr)) = sr r.
Proof.
  intros Sg n lq lr st sr r Hr. cbn [fsubP sR].
  apply (sel_at (fun r => ea (n + length lq + idx r lr)) sr (ea (n + length lq + idx r lr))
           (sR Sg (ea (n + length lq + idx r lr))) lr r Hr eq_refl).
  intros r' Hr' E. apply ea_inj in E. assert (Hi : idx r' lr = idx r lr) by lia.
  rewrite (idx_inj r' r lr Hr' Hr Hi). reflexivity.
Qed.

Lemma fsubP_rout : forall Sg n lq lr st sr b,
  (forall r, In r lr -> b <> ea (n + length lq + idx r lr)) -> sR (fsubP Sg n lq lr st sr) b = sR Sg b.
Proof.
  intros Sg n lq lr st sr b H. cbn [fsubP sR].
  exact (sel_out (fun r => ea (n + length lq + idx r lr)) sr b (sR Sg b) lr H).
Qed.

(* A substitution that fixes the atoms and rows of a type leaves it alone. *)
Lemma ap_fix_typ : forall T st sr,
  (forall a, a `in` ftv_typ T -> st a = typ_Var a) -> (forall r, r `in` frv_typ T -> sr r = row_Var r) ->
  ap_typ st sr T = T.
Proof.
  intros T st sr H1 H2. rewrite (ap_typ_ext T st sr (fun a => typ_Var a) (fun r => row_Var r) H1 H2).
  apply ap_typ_pointwise_id; reflexivity.
Qed.

Lemma ap_fix_row : forall R st sr,
  (forall a, a `in` ftv_row R -> st a = typ_Var a) -> (forall r, r `in` frv_row R -> sr r = row_Var r) ->
  ap_row st sr R = R.
Proof.
  intros R st sr H1 H2.
  rewrite (proj2 ap_ext_mut R st sr (fun a => typ_Var a) (fun r => row_Var r) H1 H2).
  exact (proj2 ap_pointwise_id_mut R _ _ (fun _ => eq_refl) (fun _ => eq_refl)).
Qed.

(* ---- a step that only extends the environment and the substitution ---- *)

Lemma SemW_ext : forall L LR (D1 Dd : denv) Sg S2 n n1,
  DOk D1 n1 -> Drow D1 -> n <= n1 -> LOld n L -> LOld n LR ->
  LiveG evA evA L LR D1 Dd S2 ->
  (forall x, x `in` L -> sT S2 x = sT Sg x) -> (forall q, q `in` LR -> sR S2 q = sR Sg q) ->
  SemW evA evA L LR Dd Sg n sid D1 n1 S2.
Proof.
  intros L LR D1 Dd Sg S2 n n1 Hd Hrow Hl Ho Hro HL Ex Er.
  assert (HT : limgT sid L LR [<=] L).
  { intros y Hy. apply limgT_in in Hy. destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)].
    - cbn [sT sid idt] in Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst y. exact Hx.
    - cbn [sR sid idr] in Hy. simpl in Hy. fsetdec. }
  assert (HR : limgR sid L LR [<=] LR).
  { intros y Hy. apply limgR_in in Hy. destruct Hy as [(x & Hx & Hy)|(q & Hq & Hy)].
    - cbn [sT sid idt] in Hy. simpl in Hy. fsetdec.
    - cbn [sR sid idr] in Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst y. exact Hq. }
  refine (conj Hd (conj Hrow (conj (LiveG_mono _ _ _ _ _ _ _ _ _ HT HR HL) (conj _ (conj _ (conj _ OkS_id)))))).
  - refine (conj Hl (conj _ _)).
    + intros x Hx. cbn [sT sid idt]. exact (conj I (conj (atT_V Dd n1 x (old_le n n1 x Hl (Ho x Hx))) I)).
    + intros q Hq. cbn [sR sid idr]. exact (conj I (conj (atR_V Dd n1 q (old_le n n1 q Hl (Hro q Hq))) I)).
  - intros x Hx. cbn [sid sT idt]. change (teq (sT Sg x) (sT S2 x)). rewrite (Ex x Hx). apply teq_refl.
  - intros q Hq. cbn [sid sR idr]. change (req (sR Sg q) (sR S2 q)). rewrite (Er q Hq). apply req_refl.
Qed.

(* ---- the instance of a scheme re-holds nothing ---- *)

Section InstNone.

Variables (sc : scheme) (Sg : sub) (n : nat).

Let inst := inst_sub sc n.

(* The presences of the instance are [Unit] or atoms below the supply. *)
Lemma inst_old_var : forall a, a `notin` s_tq sc -> sT inst a = typ_Var a.
Proof.
  intros a Ha. unfold inst, inst_sub. cbn [sT].
  destruct (in_dec Atom.eq_dec a (AtomSetImpl.elements (s_tq sc))) as [Hin|Hin]; [ | reflexivity ].
  exfalso. apply Ha. apply In_elements. exact Hin.
Qed.

Lemma rh_none_mut :
  (forall v, old n v -> ~ In v (inst_pres sc n)) ->
  (forall T, pf T -> ps (sfixS sc Sg) T -> (forall a, a `in` ftv_typ T -> a `notin` s_tq sc -> old n a) ->
     forall m, rh_t (inst_pres sc n) (apT inst T) m = (apT inst T, nil, m)) /\
  (forall R, prf R -> psr (sfixS sc Sg) R -> (forall a, a `in` ftv_row R -> a `notin` s_tq sc -> old n a) ->
     forall m, rh_r (inst_pres sc n) (apR inst R) m = (apR inst R, nil, m)).
Proof.
  intros HL.
  apply typ_row_mutind; cbn [pf prf ps psr]; try (intros; contradiction).
  - intros _ _ _ m. reflexivity.
  - intros _ _ _ m. reflexivity.
  - intros _ _ _ m. reflexivity.
  - intros _ _ _ m. reflexivity.
  - intros _ _ _ m. reflexivity.
  - intros A IHA B IHB [PA PB] [SA SB] Ho m. rewrite apT_Arrow. cbn [rh_t].
    rewrite (IHA PA SA (fun a Ha Hq => Ho a (proj2 (AtomSetFacts.union_iff _ _ _) (or_introl Ha)) Hq) m).
    rewrite (IHB PB SB (fun a Ha Hq => Ho a (proj2 (AtomSetFacts.union_iff _ _ _) (or_intror Ha)) Hq) m).
    reflexivity.
  - intros R IH HR PR Ho m. change (apT inst (typ_Record R)) with (typ_Record (apR inst R)).
    cbn [rh_t]. rewrite (IH HR PR Ho m). reflexivity.
  - intros a _ _ _ m. rewrite apT_Var. unfold inst, inst_sub. cbn [sT].
    destruct (in_dec Atom.eq_dec a (AtomSetImpl.elements (s_tq sc))); reflexivity.
  - intros w A IH [HA _] PA Ho m. change (apT inst (typ_Grp w A)) with (typ_Grp w (apT inst A)). reflexivity.
  - intros _ _ _ m. reflexivity.
  - intros r _ _ _ m. rewrite apR_Var. unfold inst, inst_sub. cbn [sR].
    destruct (in_dec Atom.eq_dec r (AtomSetImpl.elements (s_rq sc))); reflexivity.
  - intros l T IHT R IHR [HT HR] [PT PR] Ho m.
    change (apR inst (row_Ext l T R)) with (row_Ext l (apT inst T) (apR inst R)). cbn [rh_r].
    rewrite (IHT HT PT (fun a Ha Hq => Ho a (proj2 (AtomSetFacts.union_iff _ _ _) (or_introl Ha)) Hq) m).
    rewrite (IHR HR PR (fun a Ha Hq => Ho a (proj2 (AtomSetFacts.union_iff _ _ _) (or_intror Ha)) Hq) m).
    reflexivity.
  - intros l P IHP T IHT R IHR [HP [HT HR]] [PP [PT PR]] Ho m.
    change (apR inst (row_Maybe l P T R)) with (row_Maybe l (apT inst P) (apT inst T) (apR inst R)).
    cbn [rh_r].
    assert (HoT : forall a, a `in` ftv_typ T -> a `notin` s_tq sc -> old n a)
      by (intros a Ha Hq; apply (Ho a); [ simpl; fsetdec | exact Hq ]).
    assert (HoR : forall a, a `in` ftv_row R -> a `notin` s_tq sc -> old n a)
      by (intros a Ha Hq; apply (Ho a); [ simpl; fsetdec | exact Hq ]).
    rewrite (IHT HT PT HoT m).
    rewrite (IHR HR PR HoR m).
    assert (Hfp : fresh_pres (inst_pres sc n) (apT inst P) = false).
    { destruct (pres_shape (sfixS sc Sg) P HP PP) as [->|(v & -> & Hv)].
      - reflexivity.
      - assert (Hvq : v `notin` s_tq sc).
        { intro Hq. rewrite (sfixS_tin sc Sg v Hq) in Hv. discriminate Hv. }
        assert (Hvo : old n v) by (apply (Ho v); [ simpl; fsetdec | exact Hvq ]).
        rewrite apT_Var, (inst_old_var v Hvq). unfold fresh_pres.
        destruct (in_dec Atom.eq_dec v (inst_pres sc n)) as [Hin|Hin]; [ | reflexivity ].
        exfalso. exact (HL v Hvo Hin). }
    rewrite Hfp. reflexivity.
Qed.

End InstNone.

(* The instance's entries are present under an extension of [Sg] when the body's
   are present under [Sg] with the quantifiers fixed. *)
Section InstPs.

Variables (sc : scheme) (Sg S2 : sub) (n : nat).

Lemma ps_inst_mut :
  (forall b, old n b -> sT S2 b = sT Sg b) ->
  (forall T, pf T -> ps (sfixS sc Sg) T -> (forall a, a `in` ftv_typ T -> a `notin` s_tq sc -> old n a) ->
     ps S2 (apT (inst_sub sc n) T)) /\
  (forall R, prf R -> psr (sfixS sc Sg) R -> (forall a, a `in` ftv_row R -> a `notin` s_tq sc -> old n a) ->
     psr S2 (apR (inst_sub sc n) R)).
Proof.
  intros HS2.
  apply typ_row_mutind; cbn [pf prf ps psr]; try (intros; contradiction).
  - intros _ _ _. exact I.
  - intros _ _ _. exact I.
  - intros _ _ _. exact I.
  - intros _ _ _. exact I.
  - intros _ _ _. exact I.
  - intros A IHA B IHB [PA PB] [SA SB] Ho. rewrite apT_Arrow. cbn [ps]. split.
    + exact (IHA PA SA (fun a Ha Hq => Ho a (proj2 (AtomSetFacts.union_iff _ _ _) (or_introl Ha)) Hq)).
    + exact (IHB PB SB (fun a Ha Hq => Ho a (proj2 (AtomSetFacts.union_iff _ _ _) (or_intror Ha)) Hq)).
  - intros R IH HR PR Ho. change (apT (inst_sub sc n) (typ_Record R)) with (typ_Record (apR (inst_sub sc n) R)).
    cbn [ps]. exact (IH HR PR Ho).
  - intros a _ _ _. rewrite apT_Var. unfold inst_sub. cbn [sT].
    destruct (in_dec Atom.eq_dec a (AtomSetImpl.elements (s_tq sc))); exact I.
  - intros w A IH [HA _] PA Ho.
    change (apT (inst_sub sc n) (typ_Grp w A)) with (typ_Grp w (apT (inst_sub sc n) A)). cbn [ps].
    exact (IH HA PA Ho).
  - intros _ _ _. exact I.
  - intros r _ _ _. rewrite apR_Var. unfold inst_sub. cbn [sR].
    destruct (in_dec Atom.eq_dec r (AtomSetImpl.elements (s_rq sc))); exact I.
  - intros l T IHT R IHR [HT HR] [PT PR] Ho.
    change (apR (inst_sub sc n) (row_Ext l T R)) with (row_Ext l (apT (inst_sub sc n) T) (apR (inst_sub sc n) R)).
    cbn [psr]. split.
    + exact (IHT HT PT (fun a Ha Hq => Ho a (proj2 (AtomSetFacts.union_iff _ _ _) (or_introl Ha)) Hq)).
    + exact (IHR HR PR (fun a Ha Hq => Ho a (proj2 (AtomSetFacts.union_iff _ _ _) (or_intror Ha)) Hq)).
  - intros l P IHP T IHT R IHR [HP [HT HR]] [PP [PT PR]] Ho.
    change (apR (inst_sub sc n) (row_Maybe l P T R))
      with (row_Maybe l (apT (inst_sub sc n) P) (apT (inst_sub sc n) T) (apR (inst_sub sc n) R)).
    cbn [psr]. refine (conj _ (conj _ _)).
    + destruct (pres_shape (sfixS sc Sg) P HP PP) as [->|(v & -> & Hv)].
      * reflexivity.
      * assert (Hvq : v `notin` s_tq sc).
        { intro Hq. rewrite (sfixS_tin sc Sg v Hq) in Hv. discriminate Hv. }
        assert (Hvo : old n v) by (apply (Ho v); [ simpl; fsetdec | exact Hvq ]).
        rewrite (sfixS_tout sc Sg v Hvq) in Hv.
        unfold inst_sub. rewrite apT_Var. cbn [sT].
        destruct (in_dec Atom.eq_dec v (AtomSetImpl.elements (s_tq sc))) as [Hin|Hin].
        -- exfalso. apply Hvq. apply In_elements. exact Hin.
        -- rewrite apT_Var. rewrite (HS2 v Hvo). exact Hv.
    + exact (IHT HT PT (fun a Ha Hq => Ho a ltac:(simpl; fsetdec) Hq)).
    + exact (IHR HR PR (fun a Ha Hq => Ho a ltac:(simpl; fsetdec) Hq)).
Qed.

End InstPs.

(* ---- a variable at a scheme ---- *)

(* The algorithm's context binds [x] to [sc], whose entries are present under
   the derivation's substitution with the quantifiers fixed ([GPsP]).  The
   derivation reads [sc] at an instance [st], [sr], whose images are even, satisfy
   the sorts and kinds [sc] records, and keep the atoms that [Numeric] and
   [Quot] atoms stand for out of records.  The run instantiates [sc] at fresh
   atoms and rows and re-holds nothing; the extension sends the fresh atoms and
   rows to the instance. *)
Lemma var_sch_doneP : forall (Pt : typ -> Prop) L LR Dd D G n Sg x sc (st : tsub) (sr : rsub) T,
  (forall X, Pt X -> EvT X) ->
  DOk D n -> Drow D -> LOld n L -> LOld n LR -> LiveG evA evA L LR D Dd Sg ->
  GOkP n G -> GLiveP L LR G -> lookup x G = Some sc -> ps (sfixS sc Sg) (s_body sc) ->
  (forall r, r `in` s_rq sc -> rk_sort (s_rk sc r) = k_Any \/ rk_sort (s_rk sc r) = k_Eq) ->
  (forall a, a `notin` s_tq sc -> st a = typ_Var a) ->
  (forall r, r `notin` s_rq sc -> sr r = row_Var r) ->
  (forall a, a `in` s_tq sc -> sat Dd (s_sk sc a) (st a)) ->
  (forall r, r `in` s_rq sc -> rkok Dd (s_rk sc r) (sr r)) ->
  (forall a, a `in` s_tq sc -> Pt (st a)) ->
  (forall r, r `in` s_rq sc -> EvR (sr r)) ->
  (forall a, a `in` s_tq sc -> NQ (s_sk sc a) -> forall R, st a <> typ_Record R) ->
  teq T (ap_typ st sr (apT (sfixS sc Sg) (s_body sc))) ->
  DoneP L LR Dd G (e_fvar_f x) D n Sg T.
Proof.
  intros Pt L LR Dd D G n Sg x sc st sr T HPt Hd Hrow HLo HLRo HLv HG HGL Hlk HPS HRK Ht1 Ht2 Ht4 Ht5 Ht7 Ht8 HNN Heq.
  pose proof (GOkP_lookup n G x sc HG Hlk) as Hso.
  pose proof Hso as (Hw & Hpf & Hold & Holdr).
  pose proof (GLiveP_lookup L LR G x sc HGL Hlk) as (Hfl & Hfr).
  pose proof Hw as (Hq & Hrq & _).
  set (lq := AtomSetImpl.elements (s_tq sc)) in *.
  set (lr := AtomSetImpl.elements (s_rq sc)) in *.
  set (S2 := fsubP Sg n lq lr st sr).
  set (T0 := apT (inst_sub sc n) (s_body sc)).
  set (D1 := inst_den D sc n).
  set (n1 := n + length lq + length lr).
  assert (Hinst : instantiate D sc n = (T0, D1, n1)) by reflexivity.
  destruct (instantiate_sound D sc n T0 D1 n1 Hinst Hw Hd) as (_ & HE0 & Hd1 & _).
  assert (HoldD : forall b, old n b -> forall a, In a lq -> b <> ea (n + idx a lq)).
  { intros b Hb a Ha E. exact (Hb (n + idx a lq) (Nat.le_add_r n (idx a lq)) E). }
  assert (HoldR : forall b, old n b -> forall r, In r lr -> b <> ea (n + length lq + idx r lr)).
  { intros b Hb r Hr E. refine (Hb (n + length lq + idx r lr) _ E). lia. }
  assert (F2 : forall b, old n b -> sT S2 b = sT Sg b)
    by (intros b Hb; exact (fsubP_out Sg n lq lr st sr b (HoldD b Hb))).
  assert (F2R : forall b, old n b -> sR S2 b = sR Sg b)
    by (intros b Hb; exact (fsubP_rout Sg n lq lr st sr b (HoldR b Hb))).
  assert (HD1o : forall b, old n b -> D1 b = D b)
    by (intros b Hb; exact (inst_den_out D sc n b (HoldD b Hb))).
  assert (HD1r : forall b, old n b -> drk D1 b = drk D b)
    by (intros b Hb; exact (inst_rden_out D sc n b (HoldR b Hb))).
  assert (Hrow1 : Drow D1).
  { intros r. destruct (key_dec (fun r0 => ea (n + length lq + idx r0 lr)) r lr) as [[r' [Hr' Hb]]|Hn].
    - rewrite Hb. pose proof (inst_rden_at D sc n r' Hr') as E.
      exact (eq_ind _ (fun K => rk_sort K = k_Any \/ rk_sort K = k_Eq)
               (HRK r' (proj1 (In_elements r' (s_rq sc)) Hr')) _ (eq_sym E)).
    - pose proof (inst_rden_out D sc n r Hn) as E.
      exact (eq_ind _ (fun K => rk_sort K = k_Any \/ rk_sort K = k_Eq) (Hrow r) _ (eq_sym E)). }
  assert (Hbody : forall y, y `in` ftv_typ T0 ->
            (exists a, In a lq /\ y = ea (n + idx a lq)) \/ y `in` ftv_sch sc).
  { intros y Hy. unfold T0, apT in Hy. destruct (ftv_ap_typ _ _ _ _ Hy) as [(b & Hb & Hyb)|(p & Hp & Hyp)].
    - destruct (in_dec_set b (s_tq sc)) as [Hbq|Hbq].
      + left. exists b. split; [ apply In_elements; exact Hbq | ].
        cbn [inst_sub sT] in Hyb. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))) as [Hin|Hin].
        * simpl in Hyb. apply AtomSetFacts.singleton_iff in Hyb. exact (eq_sym Hyb).
        * exfalso. apply Hin. apply In_elements. exact Hbq.
      + right. cbn [inst_sub sT] in Hyb. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))) as [Hin|Hin].
        * exfalso. apply Hbq. apply In_elements. exact Hin.
        * simpl in Hyb. apply AtomSetFacts.singleton_iff in Hyb. subst y.
          unfold ftv_sch. apply AtomSetFacts.diff_iff. split; assumption.
    - exfalso. cbn [inst_sub sR] in Hyp.
      destruct (in_dec Atom.eq_dec p (AtomSetImpl.elements (s_rq sc))); simpl in Hyp; fsetdec. }
  assert (Hbodyr : forall y, y `in` frv_typ T0 ->
            (exists r, In r lr /\ y = ea (n + length lq + idx r lr)) \/ y `in` frv_sch sc).
  { intros y Hy. unfold T0, apT in Hy. destruct (frv_ap_typ _ _ _ _ Hy) as [(b & Hb & Hyb)|(p & Hp & Hyp)].
    - exfalso. cbn [inst_sub sT] in Hyb.
      destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))); simpl in Hyb; fsetdec.
    - destruct (in_dec_set p (s_rq sc)) as [Hpq|Hpq].
      + left. exists p. split; [ apply In_elements; exact Hpq | ].
        cbn [inst_sub sR] in Hyp. destruct (in_dec Atom.eq_dec p (AtomSetImpl.elements (s_rq sc))) as [Hin|Hin].
        * simpl in Hyp. apply AtomSetFacts.singleton_iff in Hyp. exact (eq_sym Hyp).
        * exfalso. apply Hin. apply In_elements. exact Hpq.
      + right. cbn [inst_sub sR] in Hyp. destruct (in_dec Atom.eq_dec p (AtomSetImpl.elements (s_rq sc))) as [Hin|Hin].
        * exfalso. apply Hpq. apply In_elements. exact Hin.
        * simpl in Hyp. apply AtomSetFacts.singleton_iff in Hyp. subst y.
          unfold frv_sch. apply AtomSetFacts.diff_iff. split; assumption. }
  assert (Hold' : forall a, a `in` ftv_typ (s_body sc) -> a `notin` s_tq sc -> old n a).
  { intros a Ha Haq. apply Hold. unfold ftv_sch. apply AtomSetFacts.diff_iff. split; assumption. }
  assert (HL : forall v, old n v -> ~ In v (inst_pres sc n)).
  { intros v Hv Hin. unfold inst_pres in Hin. apply in_map_iff in Hin. destruct Hin as (i & Ei & _).
    exact (Hv (n + i) (Nat.le_add_r n i) (eq_sym Ei)). }
  assert (Hrh : rh_t (inst_pres sc n) T0 n1 = (T0, nil, n1))
    by exact (proj1 (rh_none_mut sc Sg n HL) _ Hpf HPS Hold' n1).
  assert (HpfT0 : pf T0).
  { unfold T0. apply (proj1 (pf_ap (inst_sub sc n))); [ exact Hpf | | ].
    - intros x0 _. cbn [inst_sub sT]. destruct (in_dec Atom.eq_dec x0 (AtomSetImpl.elements (s_tq sc))); exact I.
    - intros q0 _. cbn [inst_sub sR]. destruct (in_dec Atom.eq_dec q0 (AtomSetImpl.elements (s_rq sc))); exact I. }
  assert (HatT0 : atT n1 T0).
  { split.
    - intros y Hy. destruct (Hbody y Hy) as [(a & Ha & ->)|Hf].
      + apply old_ea. pose proof (idx_lt a lq Ha). unfold n1. lia.
      + exact (old_le n n1 y ltac:(unfold n1; lia) (Hold y Hf)).
    - intros y Hy. destruct (Hbodyr y Hy) as [(r & Hr & ->)|Hf].
      + apply old_ea. pose proof (idx_lt r lr Hr). unfold n1. lia.
      + exact (old_le n n1 y ltac:(unfold n1; lia) (Holdr y Hf)). }
  assert (HpsT0 : ps S2 T0)
    by exact (proj1 (ps_inst_mut sc Sg S2 n F2) _ Hpf HPS Hold').
  assert (P4 : apT S2 T0 = ap_typ st sr (apT (sfixS sc Sg) (s_body sc))).
  { unfold T0. rewrite apT_comp.
    change (ap_typ st sr (apT (sfixS sc Sg) (s_body sc))) with (apT (Sub st sr) (apT (sfixS sc Sg) (s_body sc))).
    rewrite apT_comp. unfold apT. apply ap_typ_ext.
    - intros b Hb.
      change (apT S2 (sT (inst_sub sc n) b) = apT (Sub st sr) (sT (sfixS sc Sg) b)).
      destruct (in_dec_set b (s_tq sc)) as [Hbq|Hbq].
      + rewrite (sfixS_tin sc Sg b Hbq).
        assert (Hr : sT (inst_sub sc n) b = typ_Var (ea (n + idx b lq))).
        { cbn [inst_sub sT]. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))) as [H|H];
            [ reflexivity | exfalso; apply H; apply In_elements; exact Hbq ]. }
        rewrite Hr, !apT_Var. change (sT S2 (ea (n + idx b lq)) = st b).
        exact (fsubP_at Sg n lq lr st sr b (proj2 (In_elements b (s_tq sc)) Hbq)).
      + rewrite (sfixS_tout sc Sg b Hbq).
        assert (Hbf : b `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
        assert (Hr : sT (inst_sub sc n) b = typ_Var b) by exact (inst_old_var sc n b Hbq).
        rewrite Hr, apT_Var, (F2 b (Hold b Hbf)).
        pose proof (proj1 (proj1 (proj2 (proj2 HLv))) b (Hfl b Hbf)) as (HEb & HRb).
        symmetry. apply ap_fix_typ.
        * intros c Hc. apply Ht1. intro Hcq. exact (ev_od c (HEb c Hc) (Hq c Hcq)).
        * intros c Hc. apply Ht2. intro Hcq. exact (ev_od c (HRb c Hc) (Hrq c Hcq)).
    - intros b Hb.
      change (apR S2 (sR (inst_sub sc n) b) = apR (Sub st sr) (sR (sfixS sc Sg) b)).
      destruct (in_dec_set b (s_rq sc)) as [Hbq|Hbq].
      + rewrite (sfixS_rin sc Sg b Hbq).
        assert (Hr : sR (inst_sub sc n) b = row_Var (ea (n + length lq + idx b lr))).
        { cbn [inst_sub sR]. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_rq sc))) as [H|H];
            [ reflexivity | exfalso; apply H; apply In_elements; exact Hbq ]. }
        rewrite Hr, !apR_Var. change (sR S2 (ea (n + length lq + idx b lr)) = sr b).
        exact (fsubP_rat Sg n lq lr st sr b (proj2 (In_elements b (s_rq sc)) Hbq)).
      + rewrite (sfixS_rout sc Sg b Hbq).
        assert (Hbf : b `in` frv_sch sc) by (unfold frv_sch; apply AtomSetFacts.diff_iff; split; assumption).
        assert (Hr : sR (inst_sub sc n) b = row_Var b).
        { cbn [inst_sub sR]. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_rq sc))) as [H|H];
            [ exfalso; apply Hbq; apply In_elements; exact H | reflexivity ]. }
        rewrite Hr, apR_Var, (F2R b (Holdr b Hbf)).
        pose proof (proj2 (proj1 (proj2 (proj2 HLv))) b (Hfr b Hbf)) as (HEb & HRb).
        change (sR Sg b = apR (Sub st sr) (sR Sg b)). symmetry. apply ap_fix_row.
        * intros c Hc. apply Ht1. intro Hcq. exact (ev_od c (HEb c Hc) (Hq c Hcq)).
        * intros c Hc. apply Ht2. intro Hcq. exact (ev_od c (HRb c Hc) (Hrq c Hcq)). }
  assert (HLv1 : LiveG evA evA L LR D1 Dd S2).
  { pose proof (LiveG_env evA evA L LR D D1 Dd Sg HLv (fun a Ha => HD1o a (HLo a Ha))
                  (fun q Hq0 => HD1r q (HLRo q Hq0))) as H1.
    exact (LiveG_agree evA evA L LR D1 Dd Sg S2 H1 (fun a Ha => F2 a (HLo a Ha)) (fun q Hq0 => F2R q (HLRo q Hq0))). }
  assert (Eat : forall a, In a lq -> D1 (ea (n + idx a lq)) = s_sk sc a)
    by (intros a Ha; exact (inst_den_at D sc n a Ha)).
  assert (Erat : forall r, In r lr -> drk D1 (ea (n + length lq + idx r lr)) = s_rk sc r)
    by (intros r Hr; exact (inst_rden_at D sc n r Hr)).
  assert (Sat : forall a, In a lq -> sT S2 (ea (n + idx a lq)) = st a)
    by (intros a Ha; exact (fsubP_at Sg n lq lr st sr a Ha)).
  assert (Srat : forall r, In r lr -> sR S2 (ea (n + length lq + idx r lr)) = sr r)
    by (intros r Hr; exact (fsubP_rat Sg n lq lr st sr r Hr)).
  assert (HLvT : LiveG evA evA (ftv_typ T0) (frv_typ T0) D1 Dd S2).
  { destruct HLv1 as (SL & RL & (BT & BR) & NL).
    refine (conj _ (conj _ (conj (conj _ _) _))).
    - intros y Hy. destruct (Hbody y Hy) as [(a & Ha & ->)|Hf].
      + assert (Haq : a `in` s_tq sc) by (apply In_elements; exact Ha).
        rewrite (Eat a Ha), (Sat a Ha). exact (Ht4 a Haq).
      + exact (SL y (Hfl y Hf)).
    - intros q Hy. destruct (Hbodyr q Hy) as [(r & Hr & ->)|Hf].
      + assert (Hrq' : r `in` s_rq sc) by (apply In_elements; exact Hr).
        rewrite (Erat r Hr), (Srat r Hr). exact (Ht5 r Hrq').
      + exact (RL q (Hfr q Hf)).
    - intros y Hy. destruct (Hbody y Hy) as [(a & Ha & ->)|Hf].
      + assert (Haq : a `in` s_tq sc) by (apply In_elements; exact Ha).
        rewrite (Sat a Ha). exact (HPt _ (Ht7 a Haq)).
      + exact (BT y (Hfl y Hf)).
    - intros q Hy. destruct (Hbodyr q Hy) as [(r & Hr & ->)|Hf].
      + assert (Hrq' : r `in` s_rq sc) by (apply In_elements; exact Hr).
        rewrite (Srat r Hr). exact (Ht8 r Hrq').
      + exact (BR q (Hfr q Hf)).
    - intros y Hy. destruct (Hbody y Hy) as [(a & Ha & ->)|Hf].
      + assert (Haq : a `in` s_tq sc) by (apply In_elements; exact Ha).
        rewrite (Eat a Ha), (Sat a Ha). exact (HNN a Haq).
      + exact (NL y (Hfl y Hf)). }
  exists sid, D1, n1, S2, T0, (e_fvar_f x), nil.
  refine (conj _ (conj _ (conj HpfT0 (conj HatT0 (conj HpsT0 (conj HE0 (conj HLvT (conj (Forall_nil _)
            (conj _ (conj eq_refl eq_refl))))))))))
  .
  - exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
    cbn [infer]. rewrite Hlk, Hinst, Hrh. reflexivity.
  - exact (SemW_ext L LR D1 Dd Sg S2 n n1 Hd1 Hrow1 ltac:(unfold n1; lia) HLo HLRo HLv1
             (fun a Ha => F2 a (HLo a Ha)) (fun q Hq0 => F2R q (HLRo q Hq0))).
  - rewrite P4. apply teq_sym. exact Heq.
Qed.
