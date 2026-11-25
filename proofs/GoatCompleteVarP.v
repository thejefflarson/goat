(* Completeness of algorithm W, stage 7.8j: a variable at a scheme, over the
   fragment (docs/design/phase7-proof-plan.md).

   [var_sch_doneT] (GoatCompleteCoreW.v) is the variable case on record-free
   schemes.  Here the scheme's body is in the fragment ([pf]) and the scheme may
   quantify rows and presences.  The run [infer] makes at [e_fvar_f x]
   instantiates the scheme ([instantiate]: fresh atoms for the quantified atoms,
   then fresh row variables) and re-holds an equation for each entry whose
   presence is one of those fresh atoms ([rh_t]), giving the entry a field
   variable of its own.  A scheme of the context satisfies [GPsP]: every entry
   of its body whose presence is not a quantified atom is present under the
   substitution that fixes its quantifiers.  The extension [fsubP] sends the
   fresh atoms and rows to the images of the derivation's instance, and [fvx]
   (GoatCompleteRehold.v) sends each field variable to the image of the field
   it replaced, which solves every re-held equation ([rh_teq]).  The result is
   a [DoneQ]: the equations' types are packed with the result type, so their
   atoms are live.

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
Require Import Goat.GoatCompleteSchQ.
Require Import Goat.GoatCompleteRehold.
Require Import Goat.GoatCompleteCtxP.
Require Import Goat.GoatCompleteDoneQ.
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


(* ---- the instance of a scheme ---- *)

Lemma inst_old_var : forall sc n a, a `notin` s_tq sc -> sT (inst_sub sc n) a = typ_Var a.
Proof.
  intros sc n a Ha. unfold inst_sub. cbn [sT].
  destruct (in_dec Atom.eq_dec a (AtomSetImpl.elements (s_tq sc))) as [Hin|Hin]; [ | reflexivity ].
  exfalso. apply Ha. apply In_elements. exact Hin.
Qed.

(* The instance's entries are present under an extension of [Sg] when the body's
   are present under [Sg] with the quantifiers sent to [Unit]: an entry whose
   presence is a quantified atom is present because the instance sends the atom
   to [Unit]. *)
Section InstPs.

Variables (sc : scheme) (Sg S1 : sub) (n : nat).

Lemma ps_inst_mut :
  (forall b, old n b -> sT S1 b = sT Sg b) ->
  (forall T, pf T -> ps (sfixU sc Sg) T -> (forall a, a `in` ftv_typ T -> a `notin` s_tq sc -> old n a) ->
     (forall v, v `in` s_tq sc -> qprT v T -> sT S1 (ea (n + idx v (AtomSetImpl.elements (s_tq sc)))) = typ_Unit) ->
     ps S1 (apT (inst_sub sc n) T)) /\
  (forall R, prf R -> psr (sfixU sc Sg) R -> (forall a, a `in` ftv_row R -> a `notin` s_tq sc -> old n a) ->
     (forall v, v `in` s_tq sc -> qprR v R -> sT S1 (ea (n + idx v (AtomSetImpl.elements (s_tq sc)))) = typ_Unit) ->
     psr S1 (apR (inst_sub sc n) R)).
Proof.
  intros HS2.
  apply typ_row_mutind; cbn [pf prf ps psr]; try (intros; contradiction).
  - intros _ _ _ _. exact I.
  - intros _ _ _ _. exact I.
  - intros _ _ _ _. exact I.
  - intros _ _ _ _. exact I.
  - intros _ _ _ _. exact I.
  - intros A IHA B IHB [PA PB] [SA SB] Ho HU. rewrite apT_Arrow. cbn [ps]. split.
    + exact (IHA PA SA (fun a Ha Hq => Ho a (proj2 (AtomSetFacts.union_iff _ _ _) (or_introl Ha)) Hq)
               (fun v Hv Hq => HU v Hv (or_introl Hq))).
    + exact (IHB PB SB (fun a Ha Hq => Ho a (proj2 (AtomSetFacts.union_iff _ _ _) (or_intror Ha)) Hq)
               (fun v Hv Hq => HU v Hv (or_intror Hq))).
  - intros R IH HR PR Ho HU. change (apT (inst_sub sc n) (typ_Record R)) with (typ_Record (apR (inst_sub sc n) R)).
    cbn [ps]. exact (IH HR PR Ho HU).
  - intros a _ _ _ _. rewrite apT_Var. unfold inst_sub. cbn [sT].
    destruct (in_dec Atom.eq_dec a (AtomSetImpl.elements (s_tq sc))); exact I.
  - intros w A IH [HA _] PA Ho HU.
    change (apT (inst_sub sc n) (typ_Grp w A)) with (typ_Grp w (apT (inst_sub sc n) A)). cbn [ps].
    exact (IH HA PA Ho HU).
  - intros _ _ _ _. exact I.
  - intros r _ _ _ _. rewrite apR_Var. unfold inst_sub. cbn [sR].
    destruct (in_dec Atom.eq_dec r (AtomSetImpl.elements (s_rq sc))); exact I.
  - intros l T IHT R IHR [HT HR] [PT PR] Ho HU.
    change (apR (inst_sub sc n) (row_Ext l T R)) with (row_Ext l (apT (inst_sub sc n) T) (apR (inst_sub sc n) R)).
    cbn [psr]. split.
    + exact (IHT HT PT (fun a Ha Hq => Ho a (proj2 (AtomSetFacts.union_iff _ _ _) (or_introl Ha)) Hq)
               (fun v Hv Hq => HU v Hv (or_introl Hq))).
    + exact (IHR HR PR (fun a Ha Hq => Ho a (proj2 (AtomSetFacts.union_iff _ _ _) (or_intror Ha)) Hq)
               (fun v Hv Hq => HU v Hv (or_intror Hq))).
  - intros l P IHP T IHT R IHR [HP [HT HR]] [PP [PT PR]] Ho HU.
    change (apR (inst_sub sc n) (row_Maybe l P T R))
      with (row_Maybe l (apT (inst_sub sc n) P) (apT (inst_sub sc n) T) (apR (inst_sub sc n) R)).
    cbn [psr]. refine (conj _ (conj _ _)).
    + destruct (pres_shape (sfixU sc Sg) P HP PP) as [->|(v & -> & Hv)].
      * reflexivity.
      * destruct (in_dec_set v (s_tq sc)) as [Hvq|Hvq].
        -- rewrite apT_Var. cbn [inst_sub sT].
           destruct (in_dec Atom.eq_dec v (AtomSetImpl.elements (s_tq sc))) as [Hin|Hin].
           ++ rewrite apT_Var. exact (HU v Hvq (or_introl eq_refl)).
           ++ exfalso. apply Hin. apply In_elements. exact Hvq.
        -- assert (Hvo : old n v) by (apply (Ho v); [ simpl; fsetdec | exact Hvq ]).
           rewrite (sfixU_tout sc Sg v Hvq) in Hv.
           rewrite apT_Var, (inst_old_var sc n v Hvq), apT_Var. rewrite (HS2 v Hvo). exact Hv.
    + exact (IHT HT PT (fun a Ha Hq => Ho a ltac:(simpl; fsetdec) Hq)
               (fun v Hv Hq => HU v Hv (or_intror (or_introl Hq)))).
    + exact (IHR HR PR (fun a Ha Hq => Ho a ltac:(simpl; fsetdec) Hq)
               (fun v Hv Hq => HU v Hv (or_intror (or_intror Hq)))).
Qed.

End InstPs.

(* ---- a variable at a scheme ---- *)

(* The algorithm's context binds [x] to [sc], whose entries are present under
   the derivation's substitution with the quantifiers sent to [Unit] ([GPsP]).
   The derivation reads [sc] at an instance [st], [sr], whose images are even,
   satisfy the sorts and kinds [sc] records, send the quantified presence atoms
   to [Unit] and keep the atoms that [Numeric] and [Quot] atoms stand for out of
   records ([RowSorts] and [NNI], recorded by [instQ], GoatCompleteSchQ.v).  The
   run instantiates [sc] at fresh atoms and rows and re-holds one equation per
   entry with a quantified presence; the extension sends the fresh atoms and
   rows to the instance and each field variable to the field it replaced. *)
Lemma var_sch_doneQ : forall (Pt : typ -> Prop) L LR Dd D G n Sg x sc (st : tsub) (sr : rsub) T,
  (forall X, Pt X -> EvT X) ->
  DOk D n -> Drow D -> LOld n L -> LOld n LR -> LiveG evA evA L LR D Dd Sg ->
  GOkP n G -> GLiveP L LR G -> lookup x G = Some sc -> ps (sfixU sc Sg) (s_body sc) ->
  RowSorts sc -> NNI sc st ->
  (forall a, a `in` s_tq sc -> qprT a (s_body sc) -> st a = typ_Unit) ->
  (forall a, a `notin` s_tq sc -> st a = typ_Var a) ->
  (forall r, r `notin` s_rq sc -> sr r = row_Var r) ->
  (forall a, a `in` s_tq sc -> sat Dd (s_sk sc a) (st a)) ->
  (forall r, r `in` s_rq sc -> rkok Dd (s_rk sc r) (sr r)) ->
  (forall a, a `in` s_tq sc -> Pt (st a)) ->
  (forall r, r `in` s_rq sc -> EvR (sr r)) ->
  teq T (ap_typ st sr (apT (sfixS sc Sg) (s_body sc))) ->
  DoneQ L LR Dd G (e_fvar_f x) D n Sg T.
Proof.
  intros Pt L LR Dd D G n Sg x sc st sr T HPt Hd Hrow HLo HLRo HLv HG HGL Hlk HPS HRK HNN HPU Ht1 Ht2 Ht4 Ht5 Ht7 Ht8 Heq.
  pose proof (GOkP_lookup n G x sc HG Hlk) as Hso.
  pose proof Hso as (Hw & Hpf & Hold & Holdr).
  pose proof (GLiveP_lookup L LR G x sc HGL Hlk) as (Hfl & Hfr).
  pose proof Hw as (Hq & Hrq & _).
  set (lq := AtomSetImpl.elements (s_tq sc)) in *.
  set (lr := AtomSetImpl.elements (s_rq sc)) in *.
  set (S1 := fsubP Sg n lq lr st sr).
  set (T0 := apT (inst_sub sc n) (s_body sc)).
  set (D1 := inst_den D sc n).
  set (n1 := n + length lq + length lr).
  assert (Hinst : instantiate D sc n = (T0, D1, n1)) by reflexivity.
  destruct (instantiate_sound D sc n T0 D1 n1 Hinst Hw Hd) as (_ & HE0 & Hd1 & _).
  assert (HoldD : forall b, old n b -> forall a, In a lq -> b <> ea (n + idx a lq)).
  { intros b Hb a Ha E. exact (Hb (n + idx a lq) (Nat.le_add_r n (idx a lq)) E). }
  assert (HoldR : forall b, old n b -> forall r, In r lr -> b <> ea (n + length lq + idx r lr)).
  { intros b Hb r Hr E. refine (Hb (n + length lq + idx r lr) _ E). lia. }
  assert (F2 : forall b, old n b -> sT S1 b = sT Sg b)
    by (intros b Hb; exact (fsubP_out Sg n lq lr st sr b (HoldD b Hb))).
  assert (F2R : forall b, old n b -> sR S1 b = sR Sg b)
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
  assert (Sat : forall a, In a lq -> sT S1 (ea (n + idx a lq)) = st a)
    by (intros a Ha; exact (fsubP_at Sg n lq lr st sr a Ha)).
  assert (Srat : forall r, In r lr -> sR S1 (ea (n + length lq + idx r lr)) = sr r)
    by (intros r Hr; exact (fsubP_rat Sg n lq lr st sr r Hr)).
  assert (HpsT1 : ps S1 T0).
  { refine (proj1 (ps_inst_mut sc Sg S1 n F2) _ Hpf HPS Hold' _).
    intros v Hv Hqv. change (sT S1 (ea (n + idx v lq)) = typ_Unit). rewrite (Sat v (proj2 (In_elements v (s_tq sc)) Hv)). exact (HPU v Hv Hqv). }
  assert (P4 : apT S1 T0 = ap_typ st sr (apT (sfixS sc Sg) (s_body sc))).
  { unfold T0. rewrite apT_comp.
    change (ap_typ st sr (apT (sfixS sc Sg) (s_body sc))) with (apT (Sub st sr) (apT (sfixS sc Sg) (s_body sc))).
    rewrite apT_comp. unfold apT. apply ap_typ_ext.
    - intros b Hb.
      change (apT S1 (sT (inst_sub sc n) b) = apT (Sub st sr) (sT (sfixS sc Sg) b)).
      destruct (in_dec_set b (s_tq sc)) as [Hbq|Hbq].
      + rewrite (sfixS_tin sc Sg b Hbq).
        assert (Hr : sT (inst_sub sc n) b = typ_Var (ea (n + idx b lq))).
        { cbn [inst_sub sT]. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))) as [H|H];
            [ reflexivity | exfalso; apply H; apply In_elements; exact Hbq ]. }
        rewrite Hr, !apT_Var. change (sT S1 (ea (n + idx b lq)) = st b).
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
      change (apR S1 (sR (inst_sub sc n) b) = apR (Sub st sr) (sR (sfixS sc Sg) b)).
      destruct (in_dec_set b (s_rq sc)) as [Hbq|Hbq].
      + rewrite (sfixS_rin sc Sg b Hbq).
        assert (Hr : sR (inst_sub sc n) b = row_Var (ea (n + length lq + idx b lr))).
        { cbn [inst_sub sR]. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_rq sc))) as [H|H];
            [ reflexivity | exfalso; apply H; apply In_elements; exact Hbq ]. }
        rewrite Hr, !apR_Var. change (sR S1 (ea (n + length lq + idx b lr)) = sr b).
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
  assert (HLv1 : LiveG evA evA L LR D1 Dd S1).
  { pose proof (LiveG_env evA evA L LR D D1 Dd Sg HLv (fun a Ha => HD1o a (HLo a Ha))
                  (fun q Hq0 => HD1r q (HLRo q Hq0))) as H1.
    exact (LiveG_agree evA evA L LR D1 Dd Sg S1 H1 (fun a Ha => F2 a (HLo a Ha)) (fun q Hq0 => F2R q (HLRo q Hq0))). }
  assert (Eat : forall a, In a lq -> D1 (ea (n + idx a lq)) = s_sk sc a)
    by (intros a Ha; exact (inst_den_at D sc n a Ha)).
  assert (Erat : forall r, In r lr -> drk D1 (ea (n + length lq + idx r lr)) = s_rk sc r)
    by (intros r Hr; exact (inst_rden_at D sc n r Hr)).
  assert (HLvT : LiveG evA evA (ftv_typ T0) (frv_typ T0) D1 Dd S1).
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
  (* the equations the run re-holds *)
  destruct (rh_t (inst_pres sc n) T0 n1) as [[T' H] n2] eqn:Hrh.
  pose proof (proj1 (rh_len (inst_pres sc n)) T0 n1) as Hlen. rewrite Hrh in Hlen. simpl in Hlen.
  destruct Hlen as [Hn2 HlH].
  set (S2 := fvx S1 n1 (rhf_t (inst_pres sc n) T0 n1)).
  assert (HO2 : forall b, old n1 b -> sT S2 b = sT S1 b).
  { intros b Hb. cbn [S2 fvx sT]. apply fvt_out. intros j Hj E. exact (Hb (n1 + j) (Nat.le_add_r n1 j) E). }
  assert (HOr2 : forall r, sR S2 r = sR S1 r) by reflexivity.
  set (Tab := fun k => nth (k - n1) (rhf_t (inst_pres sc n) T0 n1) typ_Unit).
  assert (HF2 : forall k, n1 <= k -> k < n2 -> sT S2 (ea k) = apT S1 (Tab k)).
  { intros k Hk1 Hk2. assert (Hk : k = n1 + (k - n1)) by lia. cbn [S2 fvx sT]. rewrite Hk at 1.
    rewrite fvt_at by lia. unfold Tab. reflexivity. }
  assert (Htab : forall j, j < length (rhf_t (inst_pres sc n) T0 n1) ->
                   Tab (n1 + j) = nth j (rhf_t (inst_pres sc n) T0 n1) typ_Unit).
  { intros j Hj. unfold Tab. replace (n1 + j - n1) with j by lia. reflexivity. }
  destruct (rh_teq (inst_pres sc n) S1 S2 n1 n2 Tab HO2 HOr2 HF2) as [RT _].
  destruct (RT T0 HpfT0 HatT0 n1 (le_n n1) ltac:(lia) Htab) as [TT TF].
  rewrite Hrh in TT, TF. simpl in TT, TF.
  assert (HpsT0 : ps S2 T0).
  { refine (proj1 (ps_agree S1 S2) T0 HpfT0 _ HpsT1).
    intros y Hy. symmetry. apply HO2. exact (proj1 HatT0 y Hy). }
  destruct (proj1 (rh_struct (inst_pres sc n) S2) T0 HpfT0 HpsT0 n1) as (pT' & psT' & le12 & AtC' & frv' & Fh).
  rewrite Hrh in pT', psT', le12, AtC', frv', Fh. simpl in pT', psT', le12, AtC', frv', Fh.
  assert (Hin : forall b, b `in` ftv_typ (pack T' H) ->
            b `in` ftv_typ T0 \/ exists k, n1 <= k /\ k < n2 /\ b = ea k).
  { intros b Hb. apply AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|Hb]; [ exact (AtC' b Hb) | ].
    destruct (ftv_heqs H b Hb) as (h & Hh & Hb').
    destruct (proj1 (Forall_forall _ _) Fh h Hh) as (_ & _ & _ & (k & K1 & K2 & Ef) & AV & _).
    destruct Hb' as [Hb'|Hb'].
    - right. exists k. rewrite Ef in Hb'. simpl in Hb'. apply AtomSetFacts.singleton_iff in Hb'.
      repeat split; try lia. symmetry. exact Hb'.
    - exact (AV b Hb'). }
  assert (Hinr : forall q, q `in` frv_typ (pack T' H) -> q `in` frv_typ T0).
  { intros q Hq0. apply AtomSetFacts.union_iff in Hq0. destruct Hq0 as [Hq0|Hq0]; [ exact (frv' q Hq0) | ].
    destruct (frv_heqs H q Hq0) as (h & Hh & Hq').
    destruct (proj1 (Forall_forall _ _) Fh h Hh) as (_ & _ & _ & (k & K1 & K2 & Ef) & _ & FV).
    destruct Hq' as [Hq'|Hq'].
    - rewrite Ef in Hq'. simpl in Hq'. fsetdec.
    - exact (FV q Hq'). }
  assert (HLvT0 : LiveG evA evA (ftv_typ T0) (frv_typ T0) D1 Dd S2).
  { refine (LiveG_agree evA evA _ _ D1 Dd S1 S2 HLvT _ (fun q _ => eq_refl)).
    intros a Ha. apply HO2. exact (proj1 HatT0 a Ha). }
  assert (Hfr1 : forall k, n1 <= k -> k < n2 ->
            sat Dd (D1 (ea k)) (sT S2 (ea k)) /\
            ((forall c, c `in` ftv_typ (sT S2 (ea k)) -> evA c) /\ (forall c, c `in` frv_typ (sT S2 (ea k)) -> evA c)) /\
            (NQ (D1 (ea k)) -> forall R, sT S2 (ea k) <> typ_Record R)).
  { intros k K1 K2. rewrite (HF2 k K1 K2). rewrite (DOk_ea D1 n1 k Hd1 K1).
    pose proof (rhf_atoms (inst_pres sc n)) as (RA & _).
    assert (HFin : In (Tab k) (rhf_t (inst_pres sc n) T0 n1)).
    { unfold Tab. apply nth_In. lia. }
    destruct (RA T0 n1 _ HFin) as [A1 A2].
    destruct HLvT as (_ & _ & (BT & BR) & _).
    refine (conj (sat_any _ _) (conj (conj _ _) _)).
    - intros c Hc. destruct (ftv_ap_typ _ _ _ _ Hc) as [(b & Hb & Hcb)|(p & Hp & Hcp)].
      + exact (proj1 (BT b (A1 b Hb)) c Hcb).
      + exact (proj1 (BR p (A2 p Hp)) c Hcp).
    - intros c Hc. destruct (frv_ap_typ _ _ _ _ Hc) as [(b & Hb & Hcb)|(p & Hp & Hcp)].
      + exact (proj2 (BT b (A1 b Hb)) c Hcb).
      + exact (proj2 (BR p (A2 p Hp)) c Hcp).
    - intros HQ. exfalso. destruct HQ as [E|E]; discriminate E. }
  assert (HLpk : LiveG evA evA (ftv_typ (pack T' H)) (frv_typ (pack T' H)) D1 Dd S2).
  { destruct HLvT0 as (SL & RL & (BT & BR) & NL).
    refine (conj _ (conj _ (conj (conj _ _) _))).
    - intros b Hb. destruct (Hin b Hb) as [Hb0|(k & K1 & K2 & ->)]; [ exact (SL b Hb0) | exact (proj1 (Hfr1 k K1 K2)) ].
    - intros q Hq0. exact (RL q (Hinr q Hq0)).
    - intros b Hb. destruct (Hin b Hb) as [Hb0|(k & K1 & K2 & ->)]; [ exact (BT b Hb0) | exact (proj1 (proj2 (Hfr1 k K1 K2))) ].
    - intros q Hq0. exact (BR q (Hinr q Hq0)).
    - intros b Hb. destruct (Hin b Hb) as [Hb0|(k & K1 & K2 & ->)]; [ exact (NL b Hb0) | exact (proj2 (proj2 (Hfr1 k K1 K2))) ]. }
  assert (Hatpk : atT n2 (pack T' H)).
  { split.
    - intros b Hb. destruct (Hin b Hb) as [Hb0|(k & K1 & K2 & ->)];
        [ exact (old_le n1 n2 b le12 (proj1 HatT0 b Hb0)) | exact (old_ea n2 k K2) ].
    - intros q Hq0. exact (old_le n1 n2 q le12 (proj2 HatT0 q (Hinr q Hq0))). }
  assert (Hevpk : EvT (pack T' H)).
  { split.
    - intros b Hb. destruct (Hin b Hb) as [Hb0|(k & K1 & K2 & ->)]; [ exact (proj1 HE0 b Hb0) | exact (ev_ea k) ].
    - intros q Hq0. exact (proj2 HE0 q (Hinr q Hq0)). }
  assert (Hpfpk : pf (pack T' H)).
  { split; [ exact pT' | ]. apply pf_heqs. eapply Forall_impl; [ | exact Fh ].
    intros h (A & B & _). exact (conj A B). }
  assert (Hpspk : ps S2 (pack T' H)).
  { split; [ exact psT' | ]. apply ps_heqs. eapply Forall_impl; [ | exact Fh ].
    intros h (_ & _ & C & (k & _ & _ & Ef) & _). split; [ rewrite Ef; exact I | exact C ]. }
  assert (HOk : HOkC S2 n2 H).
  { unfold HOkC. apply Forall_forall. intros h Hh _.
    destruct (proj1 (Forall_forall _ _) Fh h Hh) as (pF & pV & psV & (k & K1 & K2 & Ef) & AV & FV).
    pose proof (proj1 (Forall_forall _ _) TF h Hh) as Teqh.
    refine (conj pF (conj pV (conj _ (conj _ (conj _ (conj psV Teqh)))))).
    - rewrite Ef. split.
      + intros y Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. rewrite <- Hy. exact (old_ea n2 k K2).
      + intros y Hy. simpl in Hy. fsetdec.
    - split.
      + intros y Hy. destruct (AV y Hy) as [Hx0|(k0 & J1 & J2 & ->)];
          [ exact (old_le n1 n2 y le12 (proj1 HatT0 y Hx0)) | exact (old_ea n2 k0 J2) ].
      + intros y Hy. exact (old_le n1 n2 y le12 (proj2 HatT0 y (FV y Hy))).
    - rewrite Ef. exact I. }
  assert (Ex : forall a, a `in` L -> sT S2 a = sT Sg a).
  { intros a Ha. rewrite (HO2 a (old_le n n1 a ltac:(unfold n1; lia) (HLo a Ha))). exact (F2 a (HLo a Ha)). }
  assert (HLv2 : LiveG evA evA L LR D1 Dd S2).
  { refine (LiveG_agree evA evA L LR D1 Dd S1 S2 HLv1 _ (fun q _ => eq_refl)).
    intros a Ha. apply HO2. exact (old_le n n1 a ltac:(unfold n1; lia) (HLo a Ha)). }
  exists sid, D1, n2, S2, T', (e_fvar_f x), H.
  refine (conj _ (conj _ (conj Hpfpk (conj Hatpk (conj Hpspk (conj Hevpk (conj HLpk (conj HOk (conj _ (conj eq_refl eq_refl)))))))))).
  - exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
    cbn [infer]. rewrite Hlk, Hinst, Hrh. reflexivity.
  - exact (SemW_ext L LR D1 Dd Sg S2 n n2 (DOk_mono D1 n1 n2 Hd1 le12) Hrow1 ltac:(unfold n1 in le12; lia) HLo HLRo HLv2
             Ex (fun q Hq0 => F2R q (HLRo q Hq0))).
  - eapply teq_trans; [ exact TT | ]. rewrite P4. apply teq_sym. exact Heq.
Qed.

(* What an instance of the comparison's scheme [apS (sfixS sc Sg) sc] records,
   read on [sc]: the quantifiers, sorts and kinds are [sc]'s, and a presence atom
   of [sc]'s body is one of the comparison scheme's. *)
Lemma instQ_cls : forall Pt D T sc Sg,
  instQ Pt D T (apS (sfixS sc Sg) sc) ->
  exists st sr, instAt Pt D T (apS (sfixS sc Sg) sc) st sr /\
    RowSorts sc /\ NNI sc st /\ PresI sc st.
Proof.
  intros Pt D T sc Sg (st & sr & Hi & Hrs & Hnn & Hpi).
  exists st, sr. refine (conj Hi (conj Hrs (conj Hnn _))).
  intros a Ha Hq. apply (Hpi a Ha). cbn [apS s_body].
  exact (proj1 (qpr_ap_fwd (sfixS sc Sg) a (sfixS_tin sc Sg a Ha)) _ Hq).
Qed.
