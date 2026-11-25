(* Completeness of algorithm W, stage 7.7g: even derivations and the conversion
   (docs/design/phase7-proof-plan.md).

   [ctyping] (GoatCompleteCore.v) demands that each type a rule invents be
   [PEv]: over even atoms and record-free.  A derivation of [typing] invents
   its types freely, so the conversion renames them: at each premise that
   introduces a type, a finite swap of atoms sends the type's atoms that the
   judgement does not already hold to fresh even atoms, and the premises are
   renamed by it.

   The derivations converted are [rtyping]: the monomorphic core, with every
   type record-free.  A call's parameter type, an operand's type and a bound
   variable's type are chosen by the derivation, and [typing] lets it choose a
   record type for any of them, which no record-free derivation can use; the
   record-free condition is therefore a hypothesis on the derivation, stated by
   the class.  A [let] of a value generalizes, and its conversion renames the
   generalized atoms and the instances through schemes; it is not here.

   [rtyping_ren] renames a whole derivation by an atom map (the kinding
   environment is [d_any], where every atom is sorted [Any], so no sort
   obligation arises).  [rtyping_ctyping] is the conversion, by induction on the
   size of the term because the premise it converts is the renamed one.

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
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferW.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatClose.
Require Import Goat.GoatElab.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteFresh.
Require Import Goat.GoatCompleteMono.
Require Import Goat.GoatCompleteNf.
Require Import Goat.GoatCompleteCtx.
Require Import Goat.GoatCompleteCore.
Require Import Goat.GoatCompleteCoreW.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Import ListNotations.

(* ---- renaming the atoms of a record-free type ---- *)

Definition rn (g : atom -> atom) : tsub := fun a => typ_Var (g a).
Definition rnT (g : atom -> atom) (T : typ) : typ := ap_typ (rn g) idr T.

Lemma rnT_arrow : forall g A B, rnT g (typ_Arrow A B) = typ_Arrow (rnT g A) (rnT g B).
Proof. reflexivity. Qed.

Lemma rf_rnT : forall g T, rf T -> rf (rnT g T).
Proof. intros g T H. exact (rf_ap (Sub (rn g) idr) T H (fun x _ => I)). Qed.

Lemma ev_rnT : forall g T, rf T -> (forall a, a `in` ftv_typ T -> ev (g a)) -> EvT (rnT g T).
Proof.
  intros g T. induction T; simpl; intros Hrf Hev; try contradiction;
    try (split; intros a Ha; unfold rnT in Ha; simpl in Ha; exfalso; revert Ha; fsetdec).
  - destruct Hrf as [H1 H2].
    destruct (IHT1 H1 (fun a Ha => Hev a ltac:(fsetdec))) as [A1 A2].
    destruct (IHT2 H2 (fun a Ha => Hev a ltac:(fsetdec))) as [B1 B2].
    split; intros a Ha; unfold rnT in Ha; simpl in Ha; apply AtomSetFacts.union_iff in Ha; destruct Ha as [Ha|Ha];
      first [ exact (A1 a Ha) | exact (B1 a Ha) | exact (A2 a Ha) | exact (B2 a Ha) ].
  - split; intros c Hc; unfold rnT in Hc; simpl in Hc.
    + apply AtomSetFacts.singleton_iff in Hc. subst c. apply Hev. simpl. fsetdec.
    + exfalso. revert Hc. fsetdec.
Qed.

Lemma fix_rnT : forall g T, rf T -> (forall a, a `in` ftv_typ T -> g a = a) -> rnT g T = T.
Proof.
  intros g T. induction T; simpl; intros Hrf Hfix; try contradiction; try reflexivity.
  - destruct Hrf as [H1 H2]. unfold rnT in *. simpl.
    rewrite (IHT1 H1 (fun a Ha => Hfix a ltac:(fsetdec))), (IHT2 H2 (fun a Ha => Hfix a ltac:(fsetdec))).
    reflexivity.
  - unfold rnT. simpl. unfold rn. rewrite (Hfix a ltac:(fsetdec)). reflexivity.
Qed.

Lemma PEv_arrow : forall A B, PEv A -> PEv B -> PEv (typ_Arrow A B).
Proof.
  intros A B [[A1 A2] A3] [[B1 B2] B3]. refine (conj (conj _ _) (conj A3 B3));
    intros a Ha; simpl in Ha; apply AtomSetFacts.union_iff in Ha; destruct Ha as [Ha|Ha];
    first [ exact (A1 a Ha) | exact (B1 a Ha) | exact (A2 a Ha) | exact (B2 a Ha) ].
Qed.

Lemma PEv_arrow_inv : forall A B, PEv (typ_Arrow A B) -> PEv A /\ PEv B.
Proof.
  intros A B [[H1 H2] [H3 H4]]. split.
  - refine (conj (conj _ _) H3); [ intros a Ha; apply H1 | intros a Ha; apply H2 ]; simpl; fsetdec.
  - refine (conj (conj _ _) H4); [ intros a Ha; apply H1 | intros a Ha; apply H2 ]; simpl; fsetdec.
Qed.

(* A finite swap that makes a record-free type even while fixing a given set,
   whose atoms in that set are even already. *)
Lemma even_swap : forall (T : typ) (B : atoms), rf T ->
  (forall a, a `in` ftv_typ T -> a `in` B -> ev a) ->
  exists g, (forall a, a `in` B -> g a = a) /\ PEv (rnT g T).
Proof.
  intros T B Hrf Hev.
  destruct (mk_rename_even (AtomSetImpl.diff (ftv_typ T) B) (B `union` ftv_typ T))
    as (f & N & _ & HNB & HNV & HVN & Hfix & HNev).
  exists f. split.
  - intros a Ha. apply Hfix.
    + intros Hd. apply AtomSetFacts.diff_iff in Hd. exact (proj2 Hd Ha).
    + intros Hn. apply (HNB a Hn). fsetdec.
  - split; [ | apply rf_rnT; exact Hrf ].
    apply ev_rnT; [ exact Hrf | ]. intros a Ha.
    destruct (AtomSetImpl.mem a B) eqn:Hm.
    + apply AtomSetFacts.mem_iff in Hm. rename Hm into Hb. rewrite (Hfix a); [ exact (Hev a Ha Hb) | | ].
      * intros Hd. apply AtomSetFacts.diff_iff in Hd. exact (proj2 Hd Hb).
      * intros Hn. apply (HNB a Hn). fsetdec.
    + assert (Hb : a `notin` B) by (intros Hb; apply AtomSetFacts.mem_iff in Hb; rewrite Hm in Hb; discriminate).
      apply HNev. apply HVN. apply AtomSetFacts.diff_iff. split; assumption.
Qed.

(* ---- monomorphic contexts ---- *)

Definition mctx (Gm : list (atom * typ)) : ctx := List.map (fun p => (fst p, sch_mono (snd p))) Gm.
Definition mren (g : atom -> atom) (Gm : list (atom * typ)) : list (atom * typ) :=
  List.map (fun p => (fst p, rnT g (snd p))) Gm.

Fixpoint mats (Gm : list (atom * typ)) : atoms :=
  match Gm with
  | nil => {}
  | (_, T) :: Gm' => ftv_typ T `union` mats Gm'
  end.

Definition GEv (Gm : list (atom * typ)) : Prop := forall x T, In (x, T) Gm -> PEv T.

Lemma mats_in : forall Gm x T a, In (x, T) Gm -> a `in` ftv_typ T -> a `in` mats Gm.
Proof.
  induction Gm as [|[y U] Gm IH]; intros x T a Hin Ha; [ inversion Hin | ].
  simpl. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. fsetdec.
  - specialize (IH x T a Hin Ha). fsetdec.
Qed.

Lemma mats_ev : forall Gm, GEv Gm -> forall a, a `in` mats Gm -> ev a.
Proof.
  induction Gm as [|[y U] Gm IH]; intros HG a Ha; simpl in Ha; [ exfalso; revert Ha; fsetdec | ].
  apply AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha].
  - exact (proj1 (proj1 (HG y U (or_introl eq_refl))) a Ha).
  - apply IH; [ | exact Ha ]. intros x T Hin. apply (HG x T). right. exact Hin.
Qed.

Lemma mren_fix : forall g Gm, (forall a, a `in` mats Gm -> g a = a) -> GEv Gm -> mren g Gm = Gm.
Proof.
  intros g. induction Gm as [|[y U] Gm IH]; intros Hf Hrf; [ reflexivity | ].
  unfold mren in *. simpl. f_equal.
  - f_equal. apply fix_rnT; [ exact (proj2 (Hrf y U (or_introl eq_refl))) | intros a Ha; apply Hf; simpl; fsetdec ].
  - apply IH; [ intros a Ha; apply Hf; simpl; fsetdec | intros x T Hin; apply (Hrf x T); right; exact Hin ].
Qed.

Lemma mctx_mren : forall g Gm, mctx (mren g Gm) = apC (Sub (rn g) idr) (mctx Gm).
Proof. intros g. induction Gm as [|[y U] Gm IH]; [ reflexivity | ]. simpl. f_equal. exact IH. Qed.

Lemma dom_mctx_mren : forall g Gm, dom (mctx (mren g Gm)) [=] dom (mctx Gm).
Proof. intros g Gm. rewrite mctx_mren. apply dom_apC. Qed.

Lemma uniq_mctx_mren : forall g Gm, uniq (mctx Gm) -> uniq (mctx (mren g Gm)).
Proof. intros g Gm H. rewrite mctx_mren. apply uniq_apC. exact H. Qed.

Lemma binds_mctx : forall Gm x T, In (x, T) Gm -> binds x (sch_mono T) (mctx Gm).
Proof.
  intros Gm x T H. unfold binds. change (x, sch_mono T) with ((fun p => (fst p, sch_mono (snd p))) (x, T)).
  apply in_map. exact H.
Qed.

(* ---- the derivations: the monomorphic core over record-free types ---- *)

Inductive rtyping : list (atom * typ) -> exp -> typ -> Prop :=
  | R_Var : forall Gm x T, uniq (mctx Gm) -> In (x, T) Gm -> rf T -> rtyping Gm (e_fvar_f x) T
  | R_Num : forall Gm i T, uniq (mctx Gm) -> sat d_any k_Literal T -> rf T -> rtyping Gm (e_num i) T
  | R_Dec : forall Gm d, uniq (mctx Gm) -> rtyping Gm (e_dec d) typ_Float
  | R_True : forall Gm, uniq (mctx Gm) -> rtyping Gm e_true typ_Bool
  | R_False : forall Gm, uniq (mctx Gm) -> rtyping Gm e_false typ_Bool
  | R_Unit : forall Gm, uniq (mctx Gm) -> rtyping Gm e_unit typ_Unit
  | R_Str : forall Gm q, uniq (mctx Gm) -> rtyping Gm (e_str q) typ_String
  | R_Abs : forall Gm e T1 T2, rf T1 -> rf T2 ->
      (forall x, x `notin` dom (mctx Gm) `union` fv_exp e ->
         rtyping ((x, T1) :: Gm) (open_exp_wrt_exp e (e_fvar_f x)) T2) ->
      rtyping Gm (e_abs e) (typ_Arrow T1 T2)
  | R_App : forall Gm e1 e2 T1 T2, rf T1 -> rf T2 ->
      rtyping Gm e1 (typ_Arrow T1 T2) -> rtyping Gm e2 T1 -> rtyping Gm (e_app e1 e2) T2
  | R_If : forall Gm e1 e2 e3 T,
      rtyping Gm e1 typ_Bool -> rtyping Gm e2 T -> rtyping Gm e3 T -> rtyping Gm (e_ite e1 e2 e3) T
  | R_ToFloat : forall Gm e A, rf A -> sat d_any k_Literal A ->
      rtyping Gm e A -> rtyping Gm (e_tofloat e) typ_Float
  | R_Arith : forall Gm e1 o e2 A, kind o <> k_cmp -> sat d_any (generic_sort o) A -> rf A ->
      rtyping Gm e1 A -> rtyping Gm e2 A -> rtyping Gm (e_bin e1 o e2) A
  | R_Cmp : forall Gm e1 o e2 A, kind o = k_cmp -> sat d_any k_Eq A -> rf A ->
      rtyping Gm e1 A -> rtyping Gm e2 A -> rtyping Gm (e_bin e1 o e2) typ_Bool
  | R_LetMono : forall Gm e1 e2 T1 T2, is_gen_value e1 = false -> rf T1 -> rf T2 ->
      rtyping Gm e1 T1 ->
      (forall x, x `notin` dom (mctx Gm) `union` fv_exp e2 ->
         rtyping ((x, T1) :: Gm) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
      rtyping Gm (e_let e1 e2) T2.

Lemma rtyping_rf : forall Gm e T, rtyping Gm e T -> rf T.
Proof.
  intros Gm e T H. induction H; simpl; try exact I; try assumption; try (split; assumption).
Qed.

(* The class is a restriction of [typing]. *)
Theorem rtyping_typing : forall Gm e T, rtyping Gm e T -> typing d_any (mctx Gm) e T.
Proof.
  intros Gm e T H. induction H.
  - eapply T_Var; [ assumption | apply binds_mctx; eassumption | apply inst_mono_self ].
  - apply T_Num; assumption.
  - apply T_Dec; assumption.
  - apply T_True; assumption.
  - apply T_False; assumption.
  - apply T_Unit; assumption.
  - apply T_Str; assumption.
  - apply T_Abs with (L := dom (mctx Gm) `union` fv_exp e). exact H2.
  - eapply T_App; eassumption.
  - apply T_If; assumption.
  - eapply T_ToFloat; eassumption.
  - eapply T_Bin; [ exact IHrtyping1 | exact IHrtyping2 | ].
    unfold generic_sort in H0. destruct (kind o) eqn:Ek; try contradiction.
    + apply sig_ring; assumption.
    + assert (Ho : o = bop_div) by (destruct o; first [ reflexivity | discriminate Ek ]).
      rewrite Ho. apply sig_quot. assumption.
    + apply sig_whole; assumption.
  - eapply T_Bin; [ exact IHrtyping1 | exact IHrtyping2 | ]. apply sig_cmp; assumption.
  - apply T_LetMono with (L := dom (mctx Gm) `union` fv_exp e2) (T1 := T1); [ exact IHrtyping | assumption ].
Qed.

(* ---- renaming a derivation ---- *)

Lemma kres_any : forall g, kres d_any d_any (rn g).
Proof. intros g a. apply sat_any. Qed.

Lemma rkres_any : rkres d_any d_any idr.
Proof. intros r. apply rkok_any. Qed.

Lemma sat_rnT : forall g k T, sat d_any k T -> sat d_any k (rnT g T).
Proof. intros g k T H. exact (sat_ap d_any d_any k T (rn g) idr (kres_any g) rkres_any H). Qed.

Theorem rtyping_ren : forall Gm e T, rtyping Gm e T -> forall g, rtyping (mren g Gm) e (rnT g T).
Proof.
  intros Gm e T H. induction H; intros g.
  - apply R_Var; [ apply uniq_mctx_mren; assumption | | apply rf_rnT; assumption ].
    unfold mren. change (x, rnT g T) with ((fun p => (fst p, rnT g (snd p))) (x, T)). apply in_map. assumption.
  - apply R_Num; [ apply uniq_mctx_mren; assumption | apply sat_rnT; assumption | apply rf_rnT; assumption ].
  - apply R_Dec. apply uniq_mctx_mren; assumption.
  - apply R_True. apply uniq_mctx_mren; assumption.
  - apply R_False. apply uniq_mctx_mren; assumption.
  - apply R_Unit. apply uniq_mctx_mren; assumption.
  - apply R_Str. apply uniq_mctx_mren; assumption.
  - rewrite rnT_arrow. apply R_Abs; [ apply rf_rnT; assumption | apply rf_rnT; assumption | ].
    intros x Hx. rewrite dom_mctx_mren in Hx. exact (H2 x Hx g).
  - eapply R_App; [ apply (rf_rnT g _ H) | apply (rf_rnT g _ H0) | | ].
    + exact (IHrtyping1 g).
    + exact (IHrtyping2 g).
  - apply R_If; [ exact (IHrtyping1 g) | exact (IHrtyping2 g) | exact (IHrtyping3 g) ].
  - apply R_ToFloat with (A := rnT g A); [ apply rf_rnT; assumption | apply sat_rnT; assumption | exact (IHrtyping g) ].
  - apply R_Arith; [ assumption | apply sat_rnT; assumption | apply rf_rnT; assumption
                   | exact (IHrtyping1 g) | exact (IHrtyping2 g) ].
  - apply R_Cmp with (A := rnT g A); [ assumption | apply sat_rnT; assumption | apply rf_rnT; assumption
                   | exact (IHrtyping1 g) | exact (IHrtyping2 g) ].
  - apply R_LetMono with (T1 := rnT g T1); [ assumption | apply rf_rnT; assumption | apply rf_rnT; assumption
                   | exact (IHrtyping g) | ].
    intros x Hx. rewrite dom_mctx_mren in Hx. exact (H4 x Hx g).
Qed.

(* ---- the conversion ---- *)

Lemma GEv_cons : forall Gm x T, PEv T -> GEv Gm -> GEv ((x, T) :: Gm).
Proof.
  intros Gm x T HT HG y U Hin. destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. exact HT.
  - exact (HG y U Hin).
Qed.

Lemma PEv_ats : forall T, PEv T -> forall a, a `in` ats T -> ev a.
Proof.
  intros T [[H1 H2] _] a Ha. unfold ats in Ha. apply AtomSetFacts.union_iff in Ha.
  destruct Ha as [Ha|Ha]; [ exact (H1 a Ha) | exact (H2 a Ha) ].
Qed.

(* The swap at a premise that introduces a type [T1]: it fixes the context and the
   judgement's own type [Tc], and makes [T1] even. *)
Lemma swap_even : forall Gm Tc T1, GEv Gm -> PEv Tc -> rf T1 ->
  exists g, rnT g Tc = Tc /\ mren g Gm = Gm /\ PEv (rnT g T1).
Proof.
  intros Gm Tc T1 HG HTc Hrf.
  destruct (even_swap T1 (mats Gm `union` ats Tc) Hrf) as (g & Hg & HP).
  - intros a _ Hb. apply AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|Hb];
      [ exact (mats_ev Gm HG a Hb) | exact (PEv_ats Tc HTc a Hb) ].
  - exists g. refine (conj _ (conj _ HP)).
    + apply fix_rnT; [ exact (proj2 HTc) | intros a Ha; apply Hg; unfold ats; fsetdec ].
    + apply mren_fix; [ intros a Ha; apply Hg; fsetdec | exact HG ].
Qed.

Lemma rtyping_ctyping_n : forall n e, esz e < n -> forall Gm T, rtyping Gm e T ->
  GEv Gm -> PEv T -> forall Av, ctyping Av d_any (mctx Gm) e T.
Proof.
  induction n as [|n IH]; [ intros e Hs; lia | ].
  intros e Hs Gm T Hr HG HT Av.
  destruct Hr as [G0 x T0 Hu Hin Hrf | G0 i T0 Hu Hs0 Hrf | G0 d Hu | G0 Hu | G0 Hu | G0 Hu | G0 q Hu
                 | G0 e0 T1 T2 Hf1 Hf2 Hb | G0 e1 e2 T1 T2 Hf1 Hf2 Hr1 Hr2 | G0 e1 e2 e3 T0 Hr1 Hr2 Hr3
                 | G0 e0 A Hf Hs0 Hr1 | G0 e1 o e2 A Hk Hs0 Hf Hr1 Hr2 | G0 e1 o e2 A Hk Hs0 Hf Hr1 Hr2
                 | G0 e1 e2 T1 T2 Hg Hf1 Hf2 Hr1 Hb]; simpl in Hs.
  - eapply C_Var; [ eassumption | apply binds_mctx; eassumption | cbn [sch_mono s_rq]; fsetdec
                  | apply instP_mono; exact HT ].
  - apply C_Num; assumption.
  - apply C_Dec; assumption.
  - apply C_True; assumption.
  - apply C_False; assumption.
  - apply C_Unit; assumption.
  - apply C_Str; assumption.
  - destruct (PEv_arrow_inv _ _ HT) as [HP1 HP2].
    apply C_Abs; [ exact HP1 | ]. intros x Hx.
    refine (IH _ _ _ _ (Hb x Hx) (GEv_cons _ _ _ HP1 HG) HP2 _).
    rewrite esz_open. lia.
  - destruct (swap_even G0 T2 T1 HG HT Hf1) as (g & hT & hm & HP1).
    pose proof (rtyping_ren _ _ _ Hr1 g) as H1'. rewrite hm, rnT_arrow, hT in H1'.
    pose proof (rtyping_ren _ _ _ Hr2 g) as H2'. rewrite hm in H2'.
    eapply C_App with (T1 := rnT g T1); [ exact HT | | ].
    + exact (IH e1 ltac:(lia) _ _ H1' HG (PEv_arrow _ _ HP1 HT) _).
    + exact (IH e2 ltac:(lia) _ _ H2' HG HP1 _).
  - assert (HB : PEv typ_Bool) by (apply PEv_scalar; tauto).
    apply C_If.
    + exact (IH e1 ltac:(lia) _ _ Hr1 HG HB _).
    + exact (IH e2 ltac:(lia) _ _ Hr2 HG HT _).
    + exact (IH e3 ltac:(lia) _ _ Hr3 HG HT _).
  - destruct (swap_even G0 typ_Float A HG PEv_float Hf) as (g & hT & hm & HP1).
    pose proof (rtyping_ren _ _ _ Hr1 g) as H1'. rewrite hm in H1'.
    eapply C_ToFloat with (A := rnT g A); [ | apply sat_rnT; assumption | exact HP1 ].
    exact (IH e0 ltac:(lia) _ _ H1' HG HP1 _).
  - apply C_Arith; [ assumption | assumption | exact HT | | ].
    + exact (IH e1 ltac:(lia) _ _ Hr1 HG HT _).
    + exact (IH e2 ltac:(lia) _ _ Hr2 HG HT _).
  - assert (HB : PEv typ_Bool) by (apply PEv_scalar; tauto).
    destruct (swap_even G0 typ_Bool A HG HB Hf) as (g & hT & hm & HP1).
    pose proof (rtyping_ren _ _ _ Hr1 g) as H1'. rewrite hm in H1'.
    pose proof (rtyping_ren _ _ _ Hr2 g) as H2'. rewrite hm in H2'.
    eapply C_Cmp with (A := rnT g A); [ assumption | apply sat_rnT; assumption | exact HP1 | | ].
    + exact (IH e1 ltac:(lia) _ _ H1' HG HP1 _).
    + exact (IH e2 ltac:(lia) _ _ H2' HG HP1 _).
  - destruct (swap_even G0 T2 T1 HG HT Hf1) as (g & hT & hm & HP1).
    pose proof (rtyping_ren _ _ _ Hr1 g) as H1'. rewrite hm in H1'.
    eapply C_LetMono with (T1 := rnT g T1); [ assumption | | ].
    + exact (IH e1 ltac:(lia) _ _ H1' HG HP1 _).
    + intros x Hx.
      pose proof (rtyping_ren _ _ _ (Hb x Hx) g) as H2'.
      change (mren g ((x, T1) :: G0)) with ((x, rnT g T1) :: mren g G0) in H2'. rewrite hm, hT in H2'.
      refine (IH _ _ _ _ H2' (GEv_cons _ _ _ HP1 HG) HT _).
      rewrite esz_open. lia.
Qed.

Theorem rtyping_ctyping : forall Gm e T, rtyping Gm e T -> GEv Gm -> PEv T ->
  forall Av, ctyping Av d_any (mctx Gm) e T.
Proof. intros Gm e T H HG HT Av. exact (rtyping_ctyping_n (Datatypes.S (esz e)) e (Nat.lt_succ_diag_r _) Gm T H HG HT Av). Qed.

(* The closed program: a record-free derivation of a monomorphic core program
   gives a run of the closed entry point whose result is a principal type of the
   derivation's, up to a renaming of the type's atoms to even ones. *)
Theorem infer_complete_core_mono : forall e T, rtyping nil e T ->
  exists g D T' e' S2, PEv (rnT g T) /\
    Stable (fun f => infer_closed_elab f e = Some (D, T', e')) /\ erase e' = e /\
    Live PEv (ftv_typ T') D d_any S2 /\ rkres D d_any (sR S2) /\
    teqD d_any (apT S2 T') (rnT g T) /\ rf T'.
Proof.
  intros e T H.
  destruct (even_swap T {} (rtyping_rf _ _ _ H) (fun a _ Hb => ltac:(exfalso; revert Hb; fsetdec)))
    as (g & _ & HP).
  pose proof (rtyping_ren _ _ _ H g) as H'.
  change (mren g nil) with (@nil (atom * typ)) in H'.
  pose proof (rtyping_ctyping _ _ _ H' (fun x U Hin => match Hin with end) HP {}) as Hc.
  destruct (infer_complete_core_closed e (rnT g T) Hc) as (D & T' & e' & S2 & Hs & He & Hl & Hr & Ht & Hf).
  exists g, D, T', e', S2. exact (conj HP (conj Hs (conj He (conj Hl (conj Hr (conj Ht Hf)))))).
Qed.

