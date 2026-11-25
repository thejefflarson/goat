(* Completeness of algorithm W, stage 7.7: the core constructs
   (docs/design/phase7-proof-plan.md).

   L3 for the constructs whose types are base types, variables and arrows:
   variables, constants, [program], a call, [if], the operators, a comparison,
   [float(e)], and [let] (of a value, which generalizes, and of anything else,
   which does not).  A derivation [ctyping Av D1 G1 e T1] of one of them, a
   context [G] of the algorithm that [G1] instantiates ([CI], GoatCompleteCtx.v),
   a set [L] of live atoms (the ones [G] and the pending types mention) and a
   substitution [Sg] that respects the sorts on [L] ([Live PEv L D D1 Sg]) give a
   run of [infer] that succeeds from some fuel on and a step [SemL] to the
   derivation's side: the extension [S2] of [Sg] respects the sorts the run ends
   with on the images of the live atoms, [Sg] factors through the run's
   substitution at [teqD D1] on [L], and the type the run returns is [teqD D1]
   to the derivation's under [S2].

   [ctyping] follows the normal form of GoatCompleteNf.v ([ntyping]): each rule
   hands its premises the atoms of its own judgement and of its siblings' types
   ([bg]), and a [let] of a value generalizes atoms that are even and outside
   that set.  The induction carries the same set as [Avoid]: the images of the
   live atoms stay inside it, so the premise of a generalizing [let], read at an
   environment that re-sorts the generalized atoms, sees the same sorts on
   everything the run holds live.  What a binder generalizes is dead afterwards:
   the body is compared with the live atoms that are not generalized
   ([gen_mono_let], GoatCompleteLet.v).

   Types here are record-free ([PEv]): a derivation's instances, and the types
   its rules invent, are over even atoms.  [letrec] and records are 7.8.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatSubst.
Require Import Goat.GoatMu.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferGen.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferW.
Require Import Goat.GoatHeld.
Require Import Goat.GoatHeldInst.
Require Import Goat.GoatInferSound.
Require Import Goat.GoatHeldSound.
Require Import Goat.GoatInferHeld.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatClose.
Require Import Goat.GoatElab.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteRfRows.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteInst.
Require Import Goat.GoatCompleteGen.
Require Import Goat.GoatCompleteMono.
Require Import Goat.GoatCompleteLet.
Require Import Goat.GoatCompleteNf.
Require Import Goat.GoatCompleteDrk.
Require Import Goat.GoatCompleteCtx.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the derivations of the core constructs ---- *)

Lemma PEv_scalar : forall c,
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) -> PEv c.
Proof.
  intros c Hc. split.
  - split; intros a Ha; exfalso; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; simpl in Ha; revert Ha; fsetdec.
  - destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; exact I.
Qed.

(* [typing] restricted to the constructs here, in the normal form of
   GoatCompleteNf.v: a binder's premise at every name fresh for the context and
   the term (the algorithm opens a binder at the one name it chose), the
   operators of one sort ([generic_sort]: [Numeric], and [Quot] for [/]); the
   core's types hold no record, so a [Quot] type here is a [Float].  A
   variable's type is an instance whose images are [PEv], and so is each type a
   rule invents (a parameter's, a numeral's, a call's result, an operator's). *)
Inductive ctyping : atoms -> denv -> ctx -> exp -> typ -> Prop :=
  | C_Var : forall Av Dd Gd x s T,
      uniq Gd -> binds x s Gd -> s_rq s [=] {} -> instP Dd T s -> ctyping Av Dd Gd (e_fvar_f x) T
  | C_Num : forall Av Dd Gd i T, uniq Gd -> sat Dd k_Literal T -> PEv T -> ctyping Av Dd Gd (e_num i) T
  | C_Dec : forall Av Dd Gd d, uniq Gd -> ctyping Av Dd Gd (e_dec d) typ_Float
  | C_True : forall Av Dd Gd, uniq Gd -> ctyping Av Dd Gd e_true typ_Bool
  | C_False : forall Av Dd Gd, uniq Gd -> ctyping Av Dd Gd e_false typ_Bool
  | C_Unit : forall Av Dd Gd, uniq Gd -> ctyping Av Dd Gd e_unit typ_Unit
  | C_Str : forall Av Dd Gd q, uniq Gd -> ctyping Av Dd Gd (e_str q) typ_String
  | C_Abs : forall Av Dd Gd e T1 T2, PEv T1 ->
      (forall x, x `notin` dom Gd `union` fv_exp e ->
         ctyping (bg Av Gd (typ_Arrow T1 T2)) Dd ((x ~ sch_mono T1) ++ Gd)
                 (open_exp_wrt_exp e (e_fvar_f x)) T2) ->
      ctyping Av Dd Gd (e_abs e) (typ_Arrow T1 T2)
  | C_App : forall Av Dd Gd e1 e2 T1 T2, PEv T2 ->
      ctyping (bg Av Gd T2 `union` ats T1) Dd Gd e1 (typ_Arrow T1 T2) ->
      ctyping (bg Av Gd T2 `union` ats T1) Dd Gd e2 T1 ->
      ctyping Av Dd Gd (e_app e1 e2) T2
  | C_If : forall Av Dd Gd e1 e2 e3 T,
      ctyping (bg Av Gd T) Dd Gd e1 typ_Bool -> ctyping (bg Av Gd T) Dd Gd e2 T ->
      ctyping (bg Av Gd T) Dd Gd e3 T ->
      ctyping Av Dd Gd (e_ite e1 e2 e3) T
  | C_ToFloat : forall Av Dd Gd e A,
      ctyping (bg Av Gd typ_Float `union` ats A) Dd Gd e A -> sat Dd k_Literal A -> PEv A ->
      ctyping Av Dd Gd (e_tofloat e) typ_Float
  | C_Arith : forall Av Dd Gd e1 o e2 A,
      kind o <> k_cmp -> sat Dd (generic_sort o) A -> PEv A ->
      ctyping (bg Av Gd A `union` ats A `union` ats A) Dd Gd e1 A ->
      ctyping (bg Av Gd A `union` ats A `union` ats A) Dd Gd e2 A ->
      ctyping Av Dd Gd (e_bin e1 o e2) A
  | C_Cmp : forall Av Dd Gd e1 o e2 A,
      kind o = k_cmp -> sat Dd k_Eq A -> PEv A ->
      ctyping (bg Av Gd typ_Bool `union` ats A `union` ats A) Dd Gd e1 A ->
      ctyping (bg Av Gd typ_Bool `union` ats A `union` ats A) Dd Gd e2 A ->
      ctyping Av Dd Gd (e_bin e1 o e2) typ_Bool
  | C_LetMono : forall Av Dd Gd e1 e2 T1 T2,
      is_gen_value e1 = false ->
      ctyping (bg Av Gd T2 `union` ats T1) Dd Gd e1 T1 ->
      (forall x, x `notin` dom Gd `union` fv_exp e2 ->
         ctyping (bg Av Gd T2 `union` ats T1) Dd ((x ~ sch_mono T1) ++ Gd)
                 (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
      ctyping Av Dd Gd (e_let e1 e2) T2
  | C_Let : forall Av Dd Gd e1 e2 T1 T2 (k : sort_fn) (rk : rkind_fn) (Tm : typ),
      is_gen_value e1 = true -> rf T1 ->
      lit_pinned e1 (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm Gd))) k ->
      (forall a, a `in` AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm Gd)) ->
         ev a /\ a `notin` bg Av Gd T2) ->
      ctyping (bg Av Gd T2)
        (extr (ext Dd (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm Gd))) k)
              (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm Gd))) rk) Gd e1 T1 ->
      (forall x, x `notin` dom Gd `union` fv_exp e2 ->
         ctyping (bg Av Gd T2) Dd ((x ~ gen (pin_ctx Tm Gd) T1 k rk) ++ Gd)
                 (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
      ctyping Av Dd Gd (e_let e1 e2) T2
  | C_Conv : forall Av Dd Gd e T T',
      ctyping (bg Av Gd T' `union` ats T) Dd Gd e T -> teqD Dd T T' ->
      ctyping Av Dd Gd e T'.

Theorem ctyping_typing : forall Av D G e T, ctyping Av D G e T -> typing D G e T.
Proof.
  intros Av D G e T H. induction H.
  - eapply T_Var; [ exact H | exact H0 | exact (instP_inst _ _ _ H2) ].
  - apply T_Num; assumption.
  - apply T_Dec; assumption.
  - apply T_True; assumption.
  - apply T_False; assumption.
  - apply T_Unit; assumption.
  - apply T_Str; assumption.
  - apply T_Abs with (L := dom Gd `union` fv_exp e). exact H1.
  - eapply T_App; eassumption.
  - apply T_If; assumption.
  - eapply T_ToFloat; eassumption.
  - eapply T_Bin; [ exact IHctyping1 | exact IHctyping2 | ].
    unfold generic_sort in H0. destruct (kind o) eqn:Ek; try contradiction.
    + apply sig_ring; assumption.
    + assert (Ho : o = bop_div) by (destruct o; first [ reflexivity | discriminate Ek ]).
      rewrite Ho. apply sig_quot. assumption.
    + apply sig_whole; assumption.
  - eapply T_Bin; [ exact IHctyping1 | exact IHctyping2 | ].
    apply sig_cmp; assumption.
  - apply T_LetMono with (L := dom Gd `union` fv_exp e2) (T1 := T1); [ exact IHctyping | exact H2 ].
  - apply T_Let with (L := dom Gd `union` fv_exp e2) (T1 := T1) (k := k) (rk := rk) (Tm := Tm); assumption.
  - eapply T_ConvD; eassumption.
Qed.

(* ---- what each case of the induction uses ---- *)

Lemma bg_av : forall Av G T, Av [<=] bg Av G T.
Proof. intros Av G T. unfold bg. fsetdec. Qed.

Lemma bg_ats : forall Av G T, ats T [<=] bg Av G T.
Proof. intros Av G T. unfold bg. fsetdec. Qed.

Lemma bg_ftv : forall Av G T, ftv_typ T [<=] bg Av G T.
Proof. intros Av G T. unfold bg, ats. fsetdec. Qed.

Lemma ats_ftv : forall T, ftv_typ T [<=] ats T.
Proof. intros T. unfold ats. fsetdec. Qed.

Lemma GOk_lookup : forall n G x sc, GOk n G -> lookup x G = Some sc -> SOk n sc.
Proof.
  intros n G x sc H. induction H as [|[y s0] G Hb _ IH]; intros Hl; [ discriminate Hl | ].
  cbn [lookup] in Hl. destruct (Atom.eq_dec x y) as [_|_].
  - injection Hl as Hl. subst s0. exact Hb.
  - exact (IH Hl).
Qed.

Lemma elements_none : forall V : atoms, (forall q, q `notin` V) -> AtomSetImpl.elements V = nil.
Proof. exact elements_empty_of. Qed.

Lemma instantiate_mono : forall D T n, instantiate D (sch_mono T) n = (T, D, n).
Proof.
  intros D T n. unfold instantiate.
  assert (E : AtomSetImpl.elements (s_tq (sch_mono T)) = nil)
    by (apply elements_none; intros q; cbn [sch_mono s_tq]; fsetdec).
  assert (E' : AtomSetImpl.elements (s_rq (sch_mono T)) = nil)
    by (apply elements_none; intros q; cbn [sch_mono s_rq]; fsetdec).
  assert (Ei : apT (inst_sub (sch_mono T) n) (s_body (sch_mono T)) = T).
  { unfold apT. cbn [s_body]. apply ap_typ_pointwise_id.
    - intros a. unfold inst_sub. cbn [sT]. rewrite E. reflexivity.
    - intros r. unfold inst_sub. cbn [sR]. rewrite E'. reflexivity. }
  assert (Ed : inst_den D (sch_mono T) n = D).
  { unfold inst_den. rewrite E, E'. destruct D. reflexivity. }
  rewrite Ei, Ed, E, E'. simpl. repeat rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma inst_pres_mono : forall T n, inst_pres (sch_mono T) n = nil.
Proof.
  intros T n. unfold inst_pres.
  assert (E : AtomSetImpl.elements (s_tq (sch_mono T)) = nil)
    by (apply elements_none; intros q; cbn [sch_mono s_tq]; fsetdec).
  rewrite E. reflexivity.
Qed.

Lemma rf_rf_ty : forall T, rf T -> rf_ty T.
Proof.
  induction T; cbn [rf rf_ty]; intros H; try contradiction; try exact I;
    try (split; [ apply IHT1 | apply IHT2 ]; tauto).
Qed.

Lemma is_cmp_op_true : forall o, kind o = k_cmp -> is_cmp_op o = true.
Proof. intros o H. unfold is_cmp_op. rewrite H. reflexivity. Qed.

Lemma is_cmp_op_false : forall o, kind o <> k_cmp -> is_cmp_op o = false.
Proof. intros o H. unfold is_cmp_op. destruct (kind o); try reflexivity. contradiction. Qed.

(* A step followed by the identity step is the same step, as far as the
   semantics sees: the generalizing [let] composes the discharge of its
   equations, which is the identity when it holds none. *)
Lemma SemL_sid_after : forall P L DT Sg n s D1 n1 S1,
  LOld n L -> SemL P L DT Sg n s D1 n1 S1 ->
  SemL P L DT Sg n (scomp sid s) D1 n1 S1 /\ limg (scomp sid s) L [<=] limg s L.
Proof.
  intros P L DT Sg n s D1 n1 S1 Ho H. split.
  - exact (SemL_comp P L (limg s L) DT Sg n s D1 n1 S1 sid D1 n1 S1 Ho H (fun y Hy => Hy)
             (SemL_id P (limg s L) DT S1 D1 n1 (SemL_rk H)
                (SemL_live H) (SemL_DOk H))).
  - intros y Hy. apply (limg_sid (limg s L)).
    exact (limg_scomp n n1 s sid L Ho (SemL_SI H) y Hy).
Qed.

(* What a run ends with. *)
Definition Done (L : atoms) (D1 : denv) (G : ctx) (e : exp) (D : denv) (n : nat)
  (Sg : sub) (T1 : typ) : Prop :=
  exists s D' n' S2 T e',
    Stable (fun f => infer f D G e n = Some (s, D', T, n', e', nil)) /\
    SemL PEv L D1 Sg n s D' n' S2 /\ TOk n' T /\ EvT T /\ Live PEv (ftv_typ T) D' D1 S2 /\
    RA D' /\ teqD D1 (apT S2 T) T1 /\ is_gen_value e' = is_gen_value e /\ let_open e' = let_open e.

Lemma EvT_scalar : forall c,
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) -> EvT c.
Proof. intros c Hc. exact (proj1 (PEv_scalar c Hc)). Qed.

Lemma Done_const : forall L D1 G e D n Sg T1 c,
  (forall f, infer (S f) D G e n = Some (sid, D, c, n, e, nil)) ->
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) ->
  DOk D n -> RA D -> Live PEv L D D1 Sg -> teqD D1 c T1 -> Done L D1 G e D n Sg T1.
Proof.
  intros L D1 G e D n Sg T1 c Hi Hc Hd HRA HL Hteq.
  exists sid, D, n, Sg, c, e.
  refine (conj _ (conj (SemL_id PEv L D1 Sg D n (rkres_RA D D1 (sR Sg) HRA) HL Hd) (conj (TOk_scalar n c Hc)
    (conj (EvT_scalar c Hc) (conj (Live_scalar PEv c D D1 Sg Hc) (conj HRA (conj _ (conj eq_refl eq_refl)))))))).
  - exists 1. intros f Hf. destruct f as [|f]; [ lia | exact (Hi f) ].
  - destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; exact Hteq.
Qed.

Lemma bin_res_arith : forall o A, kind o <> k_cmp -> bin_res o A = A.
Proof. intros o A H. unfold bin_res. destruct (kind o); try reflexivity. contradiction. Qed.

Ltac stable_run H :=
  eapply Stable_mono; [ | exact H ];
  intros [|f] Hf; [ contradiction | ].

Lemma ftv_arrow_sub : forall A B L, ftv_typ A [<=] L -> ftv_typ B [<=] L -> ftv_typ (typ_Arrow A B) [<=] L.
Proof. intros A B L H1 H2 y Hy. simpl in Hy. apply AtomSetFacts.union_iff in Hy. destruct Hy as [Hy|Hy]; [ apply H1 | apply H2 ]; exact Hy. Qed.

Lemma sub_ul : forall A B C : atoms, A [<=] B -> A [<=] B `union` C.
Proof. intros A B C H y Hy. apply AtomSetFacts.union_iff. left. exact (H y Hy). Qed.

Lemma in_fresh : forall (n : nat) (L : atoms), ea n `in` L `union` {{ ea n }}.
Proof. intros n L. apply AtomSetFacts.union_iff. right. apply AtomSetFacts.singleton_iff. reflexivity. Qed.

Lemma ftv_var_fresh : forall (n : nat) (L : atoms), ftv_typ (typ_Var (ea n)) [<=] L `union` {{ ea n }}.
Proof. intros n L y Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst y. apply in_fresh. Qed.

Lemma sub_scalar : forall (c : typ) (L : atoms),
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) -> ftv_typ c [<=] L.
Proof.
  intros c L Hc y Hy. exfalso. destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; simpl in Hy; revert Hy; fsetdec.
Qed.

Lemma EvT_var_ea : forall n, EvT (typ_Var (ea n)).
Proof. intros n. apply EvT_var. apply ev_ea. Qed.

(* ---- a variable bound to a scheme ---- *)

(* The extension of [Sg] that sends the fresh atoms [ea (n + i)], one per
   quantified atom, to the instance's images. *)
Definition fsub (Sg : sub) (n : nat) (lq : list atom) (st : tsub) : sub :=
  Sub (fun b => fold_right (fun a acc => if Atom.eq_dec b (ea (n + idx a lq)) then st a else acc) (sT Sg b) lq)
      (sR Sg).

Lemma fsub_at : forall Sg n lq st a, In a lq -> sT (fsub Sg n lq st) (ea (n + idx a lq)) = st a.
Proof.
  intros Sg n lq st a Ha. cbn [fsub sT].
  apply (sel_at (fun a => ea (n + idx a lq)) st (ea (n + idx a lq)) (sT Sg (ea (n + idx a lq))) lq a Ha eq_refl).
  intros a' Ha' E. apply ea_inj in E. assert (Hi : idx a' lq = idx a lq) by lia.
  rewrite (idx_inj a' a lq Ha' Ha Hi). reflexivity.
Qed.

Lemma fsub_out : forall Sg n lq st b,
  (forall a, In a lq -> b <> ea (n + idx a lq)) -> sT (fsub Sg n lq st) b = sT Sg b.
Proof.
  intros Sg n lq st b H. cbn [fsub sT].
  exact (sel_out (fun a => ea (n + idx a lq)) st b (sT Sg b) lq H).
Qed.

Lemma inst_den_at : forall D sc n a, In a (AtomSetImpl.elements (s_tq sc)) ->
  inst_den D sc n (ea (n + idx a (AtomSetImpl.elements (s_tq sc)))) = s_sk sc a.
Proof.
  intros D sc n a Ha. unfold inst_den. cbn [dsort].
  apply (sel_at (fun a => ea (n + idx a (AtomSetImpl.elements (s_tq sc)))) (s_sk sc)
           (ea (n + idx a (AtomSetImpl.elements (s_tq sc)))) _ _ a Ha eq_refl).
  intros a' Ha' E. apply ea_inj in E.
  assert (Hi : idx a' (AtomSetImpl.elements (s_tq sc)) = idx a (AtomSetImpl.elements (s_tq sc))) by lia.
  rewrite (idx_inj a' a _ Ha' Ha Hi). reflexivity.
Qed.

Lemma inst_den_out : forall D sc n b,
  (forall a, In a (AtomSetImpl.elements (s_tq sc)) -> b <> ea (n + idx a (AtomSetImpl.elements (s_tq sc)))) ->
  inst_den D sc n b = D b.
Proof.
  intros D sc n b H. unfold inst_den. cbn [dsort].
  exact (sel_out (fun a => ea (n + idx a (AtomSetImpl.elements (s_tq sc)))) (s_sk sc) b (D b) _ H).
Qed.

Lemma apT_sid : forall T, apT sid T = T.
Proof. intros T. unfold apT, sid. cbn [sT sR]. apply ap_typ_pointwise_id; reflexivity. Qed.

(* A variable the algorithm's context binds to a scheme, which the derivation's
   scheme instantiates: the algorithm instantiates at fresh atoms, and the
   extension sends those to the derivation's instance. *)
Lemma var_sch_done : forall L Dd D G n Sg x sd sc T,
  DOk D n -> RA D -> LOld n L -> LEv L -> Live PEv L D Dd Sg -> GOk n G -> GLive L G ->
  lookup x G = Some sc -> SchI Dd Sg sd sc -> instP Dd T sd ->
  Done L Dd G (e_fvar_f x) D n Sg T.
Proof.
  intros L Dd D G n Sg x sd sc T Hd HRA HLo HLE HLv HG HGL Hlk Hsch Hi.
  pose proof (GOk_lookup n G x sc HG Hlk) as Hso.
  pose proof Hso as (Hw & Hrq & Hrf & Hold).
  pose proof (GLive_lookup L G x sc HGL Hlk) as Hfl.
  pose proof (proj2 (proj2 Hsch) Dd (fun _ _ => eq_refl) (fun _ _ => eq_refl) T Hi) as Hi2.
  destruct Hi2 as (st & sr & t1 & t2 & t3 & t4 & t5 & t6 & t7 & t8).
  cbn [apS s_tq s_rq s_sk s_rk s_body] in t1, t2, t3, t4, t5, t7, t8.
  set (lq := AtomSetImpl.elements (s_tq sc)) in *.
  set (S2 := fsub Sg n lq st).
  set (T0 := apT (inst_sub sc n) (s_body sc)).
  set (D1 := inst_den D sc n).
  set (n1 := n + length lq + length (AtomSetImpl.elements (s_rq sc))).
  assert (Hinst : instantiate D sc n = (T0, D1, n1)) by reflexivity.
  destruct (instantiate_sound D sc n T0 D1 n1 Hinst Hw Hd) as (_ & HE0 & Hd1 & _).
  assert (Hlr : AtomSetImpl.elements (s_rq sc) = nil)
    by (apply elements_none; intros q Hq; apply Hrq in Hq; revert Hq; fsetdec).
  assert (Hn1 : n1 = n + length lq) by (unfold n1; rewrite Hlr; simpl; lia).
  assert (HRA1 : RA D1) by (intros r; unfold D1, inst_den; cbn [drk]; rewrite Hlr; simpl; exact (HRA r)).
  assert (HoldD : forall b, old n b -> forall a, In a lq -> b <> ea (n + idx a lq)).
  { intros b Hb a Ha E. exact (Hb (n + idx a lq) (Nat.le_add_r n (idx a lq)) E). }
  assert (F2 : forall b, old n b -> sT S2 b = sT Sg b)
    by (intros b Hb; exact (fsub_out Sg n lq st b (HoldD b Hb))).
  assert (HD1o : forall b, old n b -> D1 b = D b)
    by (intros b Hb; exact (inst_den_out D sc n b (HoldD b Hb))).
  assert (Hbody : forall y, y `in` ftv_typ T0 ->
            (exists a, In a lq /\ y = ea (n + idx a lq)) \/ y `in` ftv_sch sc).
  { intros y Hy. unfold T0 in Hy. destruct (ftv_ap_rf (inst_sub sc n) _ y Hrf Hy) as (b & Hb & Hyb).
    destruct (in_dec_set b (s_tq sc)) as [Hq|Hq].
    - left. exists b. split; [ apply In_elements; exact Hq | ].
      cbn [inst_sub sT] in Hyb. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))) as [Hin|Hin].
      + simpl in Hyb. apply AtomSetFacts.singleton_iff in Hyb. exact (eq_sym Hyb).
      + exfalso. apply Hin. apply In_elements. exact Hq.
    - right. cbn [inst_sub sT] in Hyb. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))) as [Hin|Hin].
      + exfalso. apply Hq. apply In_elements. exact Hin.
      + simpl in Hyb. apply AtomSetFacts.singleton_iff in Hyb. subst y.
        unfold ftv_sch. apply AtomSetFacts.diff_iff. split; assumption. }
  assert (P4 : apT S2 T0 = T).
  { unfold T0. rewrite apT_comp. rewrite t3.
    change (ap_typ st sr (apT (sfix (s_tq sc) Sg) (s_body sc)))
      with (apT (Sub st sr) (apT (sfix (s_tq sc) Sg) (s_body sc))).
    rewrite apT_comp. apply apT_agree; [ exact Hrf | ].
    intros b Hb.
    change (sT (scomp S2 (inst_sub sc n)) b) with (apT S2 (sT (inst_sub sc n) b)).
    change (sT (scomp (Sub st sr) (sfix (s_tq sc) Sg)) b) with (apT (Sub st sr) (sT (sfix (s_tq sc) Sg) b)).
    destruct (in_dec_set b (s_tq sc)) as [Hq|Hq].
    - rewrite sfix_in by exact Hq.
      assert (Hin : In b lq) by (apply In_elements; exact Hq).
      assert (Hr : sT (inst_sub sc n) b = typ_Var (ea (n + idx b lq))).
      { cbn [inst_sub sT]. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))) as [H|H];
          [ reflexivity | contradiction ]. }
      rewrite Hr. change (sT S2 (ea (n + idx b lq)) = st b). exact (fsub_at Sg n lq st b Hin).
    - rewrite sfix_out by exact Hq.
      assert (Hbf : b `in` ftv_sch sc) by (unfold ftv_sch; apply AtomSetFacts.diff_iff; split; assumption).
      assert (Hr : sT (inst_sub sc n) b = typ_Var b).
      { cbn [inst_sub sT]. destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))) as [H|H];
          [ exfalso; apply Hq; apply In_elements; exact H | reflexivity ]. }
      rewrite Hr. change (sT S2 b = apT (Sub st sr) (sT Sg b)).
      rewrite (F2 b (Hold b Hbf)).
      pose proof (HLv b (Hfl b Hbf)) as [_ [HEb HRb]].
      assert (Hag : apT (Sub st sr) (sT Sg b) = apT sid (sT Sg b)).
      { apply apT_agree; [ exact HRb | ]. intros c Hc. cbn [sT sid idt]. apply t1. intro Hcq.
        exact (ev_od c (proj1 HEb c Hc) ((proj1 Hw) c Hcq)). }
      rewrite Hag. rewrite apT_sid. reflexivity. }
  assert (HrfT0 : rf T0).
  { unfold T0. apply rf_ap; [ exact Hrf | ]. intros b _. cbn [inst_sub sT].
    destruct (in_dec Atom.eq_dec b (AtomSetImpl.elements (s_tq sc))); exact I. }
  assert (HTo : TOk n1 T0).
  { split; [ exact HrfT0 | ]. intros y Hy. destruct (Hbody y Hy) as [(a & Ha & ->)|Hf].
    - intros m Hm E. apply ea_inj in E. pose proof (idx_lt a lq Ha). lia.
    - exact (old_le n n1 y ltac:(lia) (Hold y Hf)). }
  exists sid, D1, n1, S2, T0, (e_fvar_f x).
  refine (conj _ (conj _ (conj HTo (conj HE0 (conj _ (conj HRA1 (conj _ (conj eq_refl eq_refl)))))))).
  - exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
    cbn [infer]. rewrite Hlk. rewrite Hinst. rewrite (rh_rf _ _ _ (rf_rf_ty _ HrfT0)). reflexivity.
  - refine (conj (rkres_RA D1 Dd (sR S2) HRA1) (conj _ (conj Hd1 (conj (SI_id_le n n1 ltac:(lia)) (conj _ (conj _ OkS_id)))))).
    + intros a Ha. pose proof (limg_sid L a Ha) as Ha'.
      rewrite (HD1o a (HLo a Ha')). rewrite (F2 a (HLo a Ha')). exact (HLv a Ha').
    + intros x0 Hx. cbn [sid sT idt]. change (teqD Dd (sT Sg x0) (sT S2 x0)).
      rewrite (F2 x0 (HLo x0 Hx)). apply teqD_refl.
    + intros q _. reflexivity.
  - intros y Hy. destruct (Hbody y Hy) as [(a & Ha & ->)|Hf].
    + assert (Haq : a `in` s_tq sc) by (apply In_elements; exact Ha).
      change (sat Dd (D1 (ea (n + idx a lq))) (sT S2 (ea (n + idx a lq))) /\ PEv (sT S2 (ea (n + idx a lq)))).
      assert (E1 : D1 (ea (n + idx a lq)) = s_sk sc a) by exact (inst_den_at D sc n a Ha).
      assert (E2 : sT S2 (ea (n + idx a lq)) = st a) by exact (fsub_at Sg n lq st a Ha).
      rewrite E1, E2.
      exact (conj (t4 a Haq) (t7 a Haq)).
    + pose proof (Hfl y Hf) as HyL.
      change (sat Dd (D1 y) (sT S2 y) /\ PEv (sT S2 y)).
      rewrite (HD1o y (HLo y HyL)). rewrite (F2 y (HLo y HyL)). exact (HLv y HyL).
  - rewrite P4. apply teqD_refl.
Qed.

(* ---- reading the derivation at another environment ---- *)

(* A [let] re-sorts the atoms it generalizes in its first premise, and leaves every
   row kind alone; conversion between types reads the environment only through
   the row kinds. *)
Lemma rlacksD_drk : forall D D2 l R, (forall r, drk D r = drk D2 r) -> rlacksD D l R = rlacksD D2 l R.
Proof.
  intros D D2 l R Hr. induction R as [|r|l' T R IH|l' P T R IH]; simpl; auto;
    [ rewrite Hr; reflexivity | rewrite IH; reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma nf_drk_mut : forall D D2, (forall r, drk D r = drk D2 r) ->
  (forall T, nfT D T = nfT D2 T) /\ (forall R, nfR D R = nfR D2 R).
Proof.
  intros D D2 H. apply typ_row_mutind; intros; try reflexivity.
  - cbn [nfT]. rewrite H0, H1. reflexivity.
  - cbn [nfT]. rewrite H0. reflexivity.
  - rewrite !nfR_ext, H0, H1. reflexivity.
  - rewrite !nfR_maybe, H0, H1, H2, (rlacksD_drk D D2 l _ H). reflexivity.
Qed.

Lemma teqD_drk : forall D D2 T T', (forall r, drk D r = drk D2 r) -> teqD D T T' -> teqD D2 T T'.
Proof.
  intros D D2 T T' H Ht. unfold teqD in *.
  rewrite <- (proj1 (nf_drk_mut D D2 H)), <- (proj1 (nf_drk_mut D D2 H)). exact Ht.
Qed.

Lemma sch_leP_env : forall (D D2 : denv) s s',
  (forall a, a `in` ftv_sch s -> D2 a = D a) ->
  (forall r, r `in` frv_sch s -> drk D2 r = drk D r) ->
  sch_leP D s s' -> sch_leP D2 s s'.
Proof.
  intros D D2 s s' Hv Hr (A & B & C). split; [ exact A | split; [ exact B | ] ].
  intros D' Hd Hdr T H. apply (C D'); [ | | exact H ].
  - intros a Ha. rewrite (Hd a Ha). apply Hv. exact Ha.
  - intros r Hrr. rewrite (Hdr r Hrr). apply Hr. exact Hrr.
Qed.

Lemma CI_env : forall (Dd Dg : denv) Sg G1 G, CI Dd Sg G1 G ->
  (forall a, a `in` ftv_ctx G1 -> Dg a = Dd a) -> (forall r, drk Dg r = drk Dd r) ->
  CI Dg Sg G1 G.
Proof.
  intros Dd Dg Sg G1 G H Hs Hr.
  induction H as [|[x s1] [y sc] G1 G [Hk Hrel] _ IH]; [ constructor | ].
  constructor.
  - simpl in *. split; [ exact Hk | ]. destruct Hrel as [(T1 & T & E1 & E2 & Ht)|Hsch].
    + left. exists T1, T. split; [ exact E1 | split; [ exact E2 | ] ].
      exact (teqD_drk Dd Dg _ _ (fun r => eq_sym (Hr r)) Ht).
    + right. refine (sch_leP_env Dd Dg _ _ _ _ Hsch).
      * intros a Ha. apply Hs. apply AtomSetFacts.union_iff. left. exact Ha.
      * intros r Hrr. apply Hr.
  - apply IH. intros a Ha. apply Hs. simpl. apply AtomSetFacts.union_iff. right. exact Ha.
Qed.

Lemma Live_env : forall L (D Dd Dg : denv) Sg, Live PEv L D Dd Sg ->
  (forall x, x `in` L -> forall c, c `in` ftv_typ (sT Sg x) -> Dg c = Dd c) ->
  (forall r, drk Dg r = drk Dd r) -> Live PEv L D Dg Sg.
Proof.
  intros L D Dd Dg Sg H Hs Hr a Ha. destruct (H a Ha) as [Hsat HP]. split; [ | exact HP ].
  eapply sat_loc; [ intros c Hc; exact (Hs a Ha c Hc) | intros r _; exact (Hr r) | exact Hsat ].
Qed.

(* A step read at the extended environment. *)
Lemma SemL_env : forall L (Dg Dd : denv) Sg n s (D' : denv) n' S2, SemL PEv L Dg Sg n s D' n' S2 -> RA D' ->
  (forall x, x `in` limg s L -> forall c, c `in` ftv_typ (sT S2 x) -> Dd c = Dg c) ->
  (forall r, drk Dd r = drk Dg r) -> SemL PEv L Dd Sg n s D' n' S2.
Proof.
  intros L Dg Dd Sg n s D' n' S2 (R & V & Hd & HI & F & Q & Ok) HRA Hs Hr.
  refine (conj (rkres_RA D' Dd (sR S2) HRA) (conj _ (conj Hd (conj HI (conj _ (conj Q Ok)))))).
  - intros a Ha. destruct (V a Ha) as [Hsat HP]. split; [ | exact HP ].
    eapply sat_loc; [ intros c Hc; exact (Hs a Ha c Hc) | intros r _; exact (Hr r) | exact Hsat ].
  - intros x Hx. exact (teqD_drk Dg Dd _ _ (fun r => eq_sym (Hr r)) (F x Hx)).
Qed.

(* The step's extension may change at atoms the step does not read. *)
Lemma SemL_agree : forall P L DT Sg n s D' n' S2 S2', LOld n L ->
  SemL P L DT Sg n s D' n' S2 ->
  (forall y, y `in` limg s L -> sT S2' y = sT S2 y) -> sR S2' = sR S2 ->
  SemL P L DT Sg n s D' n' S2'.
Proof.
  intros P L DT Sg n s D' n' S2 S2' Ho (R & V & Hd & HI & F & Q & Ok) Hag HsR.
  refine (conj _ (conj _ (conj Hd (conj HI (conj _ (conj _ Ok)))))).
  - intros r. rewrite HsR. exact (R r).
  - intros a Ha. rewrite (Hag a Ha). exact (V a Ha).
  - intros x Hx. pose proof (proj1 (proj1 (proj2 HI) x (Ho x Hx))) as Hrf.
    pose proof (F x Hx) as F'.
    assert (Hea : apT S2' (sT s x) = apT S2 (sT s x)).
    { apply apT_agree; [ exact Hrf | ]. intros y Hy. apply Hag. apply limg_in. exists x. split; assumption. }
    rewrite Hea. exact F'.
  - intros q Hq. rewrite HsR. exact (Q q Hq).
Qed.

Lemma GOk_frv : forall n G, GOk n G -> forall r, r `notin` frv_ctx G.
Proof.
  intros n G H. induction H as [|[x s] G Hb _ IH]; intros r; simpl; [ fsetdec | ].
  destruct Hb as (_ & _ & Hrf & _). pose proof (IH r) as Hn.
  assert (Hs : r `notin` frv_sch s).
  { unfold frv_sch. intro Hr. apply AtomSetFacts.diff_iff in Hr. destruct Hr as [Hr _].
    exact (proj1 (proj2 (proj2 (rf_facts _ Hrf))) r Hr). }
  fsetdec.
Qed.

(* The derivation's context holds every atom the images of the algorithm's
   context mention. *)
Lemma CI_ftv : forall (D1 : denv) Sg G1 G n L (Dx : denv), CI D1 Sg G1 G -> GOk n G -> GLive L G -> Live PEv L Dx D1 Sg ->
  forall a, a `in` ftv_ctx G -> ftv_typ (sT Sg a) [<=] ftv_ctx G1.
Proof.
  intros D1 Sg G1 G n L Dx H. induction H as [|[x s1] [y sc] G1 G [Hk Hrel] _ IH]; intros HO HG HLv a Ha.
  - simpl in Ha. fsetdec.
  - inversion HO as [|b G' Hsc HO' Eb]; subst. inversion HG as [|b2 G2 HL2 HG' Eb2]; subst.
    simpl in *. subst y. apply AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha].
    + intros c Hc. apply AtomSetFacts.union_iff. left.
      destruct Hrel as [(T1 & T & E1 & E2 & Ht)|Hsch].
      * subst s1 sc. pose proof (SOk_mono_inv _ _ Hsc) as HT.
        assert (Haf : a `in` ftv_typ T) by exact (proj1 (ftv_sch_mono T a) Ha).
        pose proof (HLv a (HL2 a Ha)) as [_ [_ Hra]].
        assert (HrfA : rf (apT Sg T)).
        { apply rf_ap; [ exact (proj1 HT) | intros w Hw; exact (proj2 (proj2 (HLv w (HL2 w (proj2 (ftv_sch_mono T w) Hw))))) ]. }
        rewrite (teqD_rf_eq _ _ _ HrfA Ht) in *. apply (proj2 (ftv_sch_mono _ c)).
        exact (ftv_ap_in1 (sT Sg) (sR Sg) T c a Haf Hc).
      * destruct Hsc as (Hw & Hr & Hrf & Hold).
        destruct Hsch as (A & _ & _). apply A.
        unfold ftv_sch. cbn [apS s_body s_tq]. apply AtomSetFacts.diff_iff. split.
        -- assert (Haf : a `in` ftv_typ (s_body sc))
             by (unfold ftv_sch in Ha; apply AtomSetFacts.diff_iff in Ha; exact (proj1 Ha)).
           assert (Haq : a `notin` s_tq sc)
             by (unfold ftv_sch in Ha; apply AtomSetFacts.diff_iff in Ha; exact (proj2 Ha)).
           assert (Hs : sT (sfix (s_tq sc) Sg) a = sT Sg a) by (apply sfix_out; exact Haq).
           assert (Hc' : c `in` ftv_typ (sT (sfix (s_tq sc) Sg) a)) by (rewrite Hs; exact Hc).
           exact (ftv_ap_in1 (sT (sfix (s_tq sc) Sg)) (sR (sfix (s_tq sc) Sg)) (s_body sc) c a Haf Hc').
        -- intro Hcq. pose proof (HLv a (HL2 a Ha)) as [_ [HEa _]].
           exact (ev_od c (proj1 HEa c Hc) ((proj1 Hw) c Hcq)).
    + intros c Hc. apply AtomSetFacts.union_iff. right. exact (IH HO' HG' HLv a Ha c Hc).
Qed.

Lemma ats_arrow_eq : forall A B, ats (typ_Arrow A B) [=] ats A `union` ats B.
Proof. intros A B. unfold ats. simpl. fsetdec. Qed.

Lemma Avoid_limg : forall B L D DT Sg n s D' n' S2, LOld n L -> Avoid B L Sg -> Live PEv L D DT Sg ->
  SemL PEv L DT Sg n s D' n' S2 -> Avoid B (limg s L) S2.
Proof.
  intros B L D DT Sg n s D' n' S2 Ho HAv HLv Hs x Hx.
  apply limg_in in Hx. destruct Hx as (y & Hy & Hxy).
  pose proof (SemL_F Hs y Hy) as Hf. pose proof (proj2 (HLv y Hy)) as Hpy.
  assert (Heq2 : apT S2 (sT s y) = sT Sg y) by exact (teqD_rf_eq _ _ _ (proj2 Hpy) Hf).
  intros z Hz. apply (HAv y Hy). rewrite <- Heq2.
  exact (ftv_ap_in1 (sT S2) (sR S2) (sT s y) z x Hxy Hz).
Qed.

Lemma sub_ur : forall A B C : atoms, A [<=] C -> A [<=] B `union` C.
Proof. intros A B C H y Hy. apply AtomSetFacts.union_iff. right. exact (H y Hy). Qed.

Lemma ftv_sch_in_bg : forall X x s G T, ftv_sch s [<=] bg X ((x ~ s) ++ G) T.
Proof. intros X x s G T y Hy. unfold bg, atc. simpl. fsetdec. Qed.

Lemma fresh_notin_Gd : forall (D1 : denv) Sg Gd G s e2, CI D1 Sg Gd G ->
  fresh_var (apC s G) e2 `notin` dom Gd `union` fv_exp e2.
Proof.
  intros D1 Sg Gd G s e2 HC. rewrite (CI_dom _ _ _ _ HC). pose proof (dom_apC s G).
  pose proof (fresh_var_notin_dom (apC s G) e2). pose proof (fresh_var_notin_fv (apC s G) e2). fsetdec.
Qed.

Lemma sub_id : forall A : atoms, A [<=] A.
Proof. intros A y Hy. exact Hy. Qed.

Lemma ftv_arrow_in_X : forall Av Gd T1 T2,
  ftv_typ (typ_Arrow T1 T2) [<=] bg Av Gd T2 `union` ats T1.
Proof.
  intros Av Gd T1 T2 y Hy. pose proof (ats_arrow_eq T1 T2). pose proof (ats_ftv (typ_Arrow T1 T2) y Hy).
  unfold bg. fsetdec.
Qed.

Lemma bg_ats_in : forall Av G T, ats T [<=] bg Av G T.
Proof. exact bg_ats. Qed.

Lemma GLive_ftv_ctx : forall L G, GLive L G -> ftv_ctx G [<=] L.
Proof.
  intros L G H. induction H as [|[x s] G Hs _ IH]; simpl; [ fsetdec | ].
  intros a Ha. apply AtomSetFacts.union_iff in Ha.
  destruct Ha as [Ha|Ha]; [ exact (Hs a Ha) | exact (IH a Ha) ].
Qed.

(* What the algorithm's generalization of an even, record-free type is. *)
Lemma gen_ren_sc : forall D G Ta n, TOk n Ta -> EvT Ta ->
  SOk n (gen_ren D G Ta) /\ ftv_sch (gen_ren D G Ta) [<=] ftv_typ Ta /\
  (forall a, a `in` ftv_sch (gen_ren D G Ta) -> a `in` ftv_ctx G).
Proof.
  intros D G Ta n [Hrf Hold] HE.
  assert (Hfrv : forall q, q `notin` frv_typ Ta) by exact (proj1 (proj2 (proj2 (rf_facts Ta Hrf)))).
  assert (Hfs : forall a, a `in` ftv_sch (gen_ren D G Ta) -> a `in` ftv_typ Ta /\ a `in` ftv_ctx G).
  { intros a Ha. unfold ftv_sch in Ha. apply AtomSetFacts.diff_iff in Ha. destruct Ha as [Ha Hn].
    destruct (body_ftv D G Ta a Ha) as [Hq|[Hb Hnl]]; [ contradiction | ].
    split; [ exact Hb | ]. destruct (in_dec_set a (ftv_ctx G)) as [H|H]; [ exact H | exfalso; apply Hnl; apply In_la; auto ]. }
  refine (conj (conj (gen_ren_wf D G Ta HE) (conj _ (conj _ _))) (conj _ _)).
  - intros a; split.
    + intro Ha. apply gen_ren_rq in Ha. destruct Ha as (b & Hb & _). apply In_lr in Hb.
      exfalso. exact (Hfrv b (proj1 Hb)).
    + intro Ha. exfalso. revert Ha. fsetdec.
  - rewrite gen_body. refine (rf_ap (Sub (rename_t _) (rename_r _)) Ta Hrf _).
    intros x _. cbn [sT]. unfold rename_t. destruct (in_dec Atom.eq_dec x _); exact I.
  - intros a Ha. exact (Hold a (proj1 (Hfs a Ha))).
  - intros a Ha. exact (proj1 (Hfs a Ha)).
  - intros a Ha. exact (proj2 (Hfs a Ha)).
Qed.

Lemma apS_sfix_fixed : forall sc S, rf (s_body sc) -> (forall q, q `in` s_tq sc -> sT S q = typ_Var q) ->
  apS (sfix (s_tq sc) S) sc = apS S sc.
Proof.
  intros sc S Hrf Hfix. unfold apS. cbn [s_tq s_rq s_sk s_rk s_body]. f_equal.
  apply apT_agree; [ exact Hrf | ].
  intros b Hb. destruct (in_dec_set b (s_tq sc)) as [Hq|Hq].
  - rewrite sfix_in by exact Hq. symmetry. exact (Hfix b Hq).
  - rewrite sfix_out by exact Hq. reflexivity.
Qed.

(* ---- the induction ---- *)

Theorem infer_complete_core : forall Av D1 G1 e T1, ctyping Av D1 G1 e T1 ->
  forall D G n Sg L, DOk D n -> RA D -> LOld n L -> LEv L -> Live PEv L D D1 Sg ->
    Avoid (bg Av G1 T1) L Sg -> GOk n G -> GLive L G -> CI D1 Sg G1 G ->
    Done L D1 G e D n Sg T1.
Proof.
  intros Av Dd Gd e T1 H.
  induction H as
    [ Av Dd Gd x s T Hu Hb Hrq Hi
    | Av Dd Gd i T Hu Hs HPT
    | Av Dd Gd d Hu | Av Dd Gd Hu | Av Dd Gd Hu | Av Dd Gd Hu | Av Dd Gd q Hu
    | Av Dd Gd b T1 T2 HPT1 Hb IH
    | Av Dd Gd e1 e2 T1 T2 HPT2 H1 IH1 H2 IH2
    | Av Dd Gd e1 e2 e3 T H1 IH1 H2 IH2 H3 IH3
    | Av Dd Gd e A H1 IH1 Hs HPA
    | Av Dd Gd e1 o e2 A Hk1 Hs HPA H1 IH1 H2 IH2
    | Av Dd Gd e1 o e2 A Hk Hs HPA H1 IH1 H2 IH2
    | Av Dd Gd e1 e2 T1 T2 Hv H1 IH1 H2 IH2
    | Av Dd Gd e1 e2 T1 T2 k rk Tm Hgv Hrf1 Hlit HevA H1 IH1 Hb IHb
    | Av Dd Gd e T T' H1 IH1 Hteq ];
    intros D G n Sg L Hd HRA HLo HLE HLv HAv HG HGL HC.
  - (* variable *)
    destruct (CI_lookup Dd Sg Gd G x s HC Hu Hb) as (sc & Hlk & [(T1' & T' & E1 & E2 & Hc) | Hsch]).
    + subst s sc.
      pose proof (inst_mono_eq _ _ _ (instP_inst _ _ _ Hi)) as ET. subst T.
      pose proof (GOk_lookup n G x _ HG Hlk) as Hso.
      pose proof (SOk_mono_inv _ _ Hso) as HTo. pose proof (SOk_mono_ev _ _ Hso) as HTe.
      pose proof (GLive_lookup L G x _ HGL Hlk) as Hsub.
      exists sid, D, n, Sg, T', (e_fvar_f x).
      refine (conj _ (conj (SemL_id PEv L Dd Sg D n (rkres_RA D Dd (sR Sg) HRA) HLv Hd)
                (conj HTo (conj HTe (conj _ (conj HRA (conj Hc (conj eq_refl eq_refl)))))))).
      * exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
        cbn [infer]. rewrite Hlk, instantiate_mono, inst_pres_mono, rh_t_nil. reflexivity.
      * exact (Live_mono PEv _ _ D Dd Sg (fun a Ha => Hsub a (proj2 (ftv_sch_mono T' a) Ha)) HLv).
    + exact (var_sch_done L Dd D G n Sg x s sc T Hd HRA HLo HLE HLv HG HGL Hlk Hsch Hi).
  - (* numeral *)
    exists sid, (upd D (ea n) k_Literal), (S n), (supd Sg (ea n) T), (typ_Var (ea n)), (e_num i).
    refine (conj _ (conj (SemL_fresh PEv L Dd D Sg n k_Literal T (rkres_RA D Dd (sR Sg) HRA) HLv Hd HLo)
              (conj _ (conj (EvT_var_ea n) (conj _ (conj (RA_upd D (ea n) k_Literal HRA) (conj _ (conj eq_refl eq_refl)))))))).
    + exists 1. intros f Hf. destruct f as [|f]; [ lia | reflexivity ].
    + apply TOk_var. apply old_ea. lia.
    + apply Live_var; rewrite ?upd_same, ?supd_same; assumption.
    + rewrite apT_Var, supd_same. apply teqD_refl.
  - (* float literal *)
    apply (Done_const L Dd G (e_dec d) D n Sg typ_Float typ_Float); try assumption;
      [ intros f; reflexivity | right; left; reflexivity | apply teqD_refl ].
  - apply (Done_const L Dd G e_true D n Sg typ_Bool typ_Bool); try assumption;
      [ intros f; reflexivity | right; right; left; reflexivity | apply teqD_refl ].
  - apply (Done_const L Dd G e_false D n Sg typ_Bool typ_Bool); try assumption;
      [ intros f; reflexivity | right; right; left; reflexivity | apply teqD_refl ].
  - apply (Done_const L Dd G e_unit D n Sg typ_Unit typ_Unit); try assumption;
      [ intros f; reflexivity | right; right; right; left; reflexivity | apply teqD_refl ].
  - apply (Done_const L Dd G (e_str q) D n Sg typ_String typ_String); try assumption;
      [ intros f; reflexivity | right; right; right; right; reflexivity | apply teqD_refl ].
  - (* program *)
    set (x := fresh_var G b).
    assert (Hx : x `notin` dom Gd `union` fv_exp b).
    { rewrite (CI_dom _ _ _ _ HC). pose proof (fresh_var_notin_dom G b). pose proof (fresh_var_notin_fv G b).
      fsetdec. }
    set (Sg' := supd Sg (ea n) T1).
    set (L' := L `union` {{ ea n }}).
    assert (Hsat : sat Dd (D (ea n)) T1) by (rewrite (DOk_ea D n n Hd (le_n n)); apply sat_any).
    assert (HTb : TOk (S n) (typ_Var (ea n))) by (apply TOk_var; apply old_ea; lia).
    assert (HsL : L [<=] L') by (intros y Hy; apply AtomSetFacts.union_iff; left; exact Hy).
    assert (HsV : ftv_typ (typ_Var (ea n)) [<=] L') by exact (ftv_var_fresh n L).
    assert (Hag : forall a, a `in` L -> sT Sg' a = sT Sg a).
    { intros a Ha. unfold Sg'. apply supd_other. intro E. exact (HLo a Ha n (le_n n) E). }
    assert (HLv' : Live PEv L' D Dd Sg').
    { exact (Live_fresh PEv L D D Dd Sg n (D (ea n)) T1 HLo HLv Hsat HPT1 eq_refl (fun _ _ => eq_refl)). }
    assert (HAv' : Avoid (bg (bg Av Gd (typ_Arrow T1 T2)) ((x ~ sch_mono T1) ++ Gd) T2) L' Sg').
    { apply Avoid_fresh; [ exact HLo | exact (Avoid_mono _ _ _ _ (bg_av _ _ _) HAv) | ].
      intros y Hy. apply bg_av. apply bg_ftv. simpl. apply AtomSetFacts.union_iff. left. exact Hy. }
    destruct (IH x Hx D ((x ~ sch_mono (typ_Var (ea n))) ++ G) (S n) Sg' L'
                (DOk_mono D n (S n) Hd (Nat.le_succ_diag_r n)) HRA (LOld_fresh n L HLo) (LEv_fresh n L HLE)
                HLv' HAv'
                (GOk_cons (S n) x _ G HTb (EvT_var_ea n) (GOk_mono n (S n) G (Nat.le_succ_diag_r n) HG))
                (GLive_cons L' x _ G HsV (GLive_mono L L' G HsL HGL))
                (CI_cons Dd Sg' Gd G x T1 _ (CI_agree Dd Sg Sg' Gd G L n HC HG HGL Hag)
                   ltac:(unfold Sg'; rewrite apT_Var, supd_same; apply teqD_refl)))
      as (s & D' & n' & S2 & T & e' & Hst & Hsem & HT & HE & LvT & HRA' & Heq & HgHeq & HlHeq).
    exists s, D', n', S2, (typ_Arrow (apT s (typ_Var (ea n))) T), (e_abs (cl 0 x e')).
    pose proof (SemL_weaken PEv L Dd Sg Sg' n (S n) s D' n' S2 (Nat.le_succ_diag_r n) HLo
      (SemL_mono PEv L L' Dd Sg' (S n) s D' n' S2 HsL Hsem) Hag (fun _ _ => eq_refl)) as Hsem0.
    refine (conj _ (conj Hsem0 (conj _ (conj _ (conj _ (conj HRA' (conj _ (conj _ _)))))))).
    + pose proof (Stable_below _ Hst) as HSt. stable_run HSt.
      cbn [infer]. change (fresh_var G b) with x. rewrite Hf. reflexivity.
    + apply TOk_arrow; [ exact (TOk_ap _ _ _ _ (SemL_SI Hsem) HTb) | exact HT ].
    + exact (EvT_arrow _ _ (EvT_ap s _ (SemL_OkS Hsem) (EvT_var_ea n)) HE).
    + cbn [ftv_typ]. apply Live_union; [ | exact LvT ].
      refine (SemL_live_ap PEv L' Dd Sg' (S n) s D' n' S2 (typ_Var (ea n)) Hsem I _).
      exact HsV.
    + rewrite apT_Arrow. apply teqD_Arrow; [ | exact Heq ].
      pose proof (SemL_F Hsem (ea n) (in_fresh n L)) as F.
      unfold Sg' in F. rewrite supd_same in F. apply teqD_sym. exact F.
    + reflexivity.
    + reflexivity.
  - (* call *)
    assert (HAvX : Avoid (bg Av Gd T2 `union` ats T1) L Sg)
      by exact (Avoid_mono _ _ _ _ (sub_ul _ _ _ (sub_id _)) HAv).
    assert (HAv1 : Avoid (bg (bg Av Gd T2 `union` ats T1) Gd (typ_Arrow T1 T2)) L Sg)
      by exact (Avoid_mono _ _ _ _ (bg_av _ _ _) HAvX).
    destruct (IH1 D G n Sg L Hd HRA HLo HLE HLv HAv1 HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & HEa & LvTa & HRA1 & Heq1 & HgHeq1 & HlHeq1).
    destruct (next_facts Dd Gd D Sg n L s1 D1a n1 Sa Ta G HLo HLE HLv Sem1 HTa HEa LvTa HG HGL HC)
      as (HLo1 & HLE1 & HLv1 & HG1 & HGL1 & HC1).
    set (L2 := lnext s1 L Ta) in *.
    assert (HAv2 : Avoid (bg (bg Av Gd T2 `union` ats T1) Gd T1) L2 Sa).
    { refine (Avoid_mono _ _ _ _ (bg_av _ _ _) _).
      exact (Avoid_next _ _ L D Dd Sg n s1 D1a n1 Sa Ta (typ_Arrow T1 T2) HLo HAvX HLv Sem1 HTa LvTa Heq1
                (sub_id _) (ftv_arrow_in_X Av Gd T1 T2)). }
    destruct (IH2 D1a (apC s1 G) n1 Sa L2 (SemL_DOk Sem1) HRA1 HLo1 HLE1 HLv1 HAv2 HG1 HGL1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & HEb & LvTb & HRA2 & Heq2 & HgHeq2 & HlHeq2).
    destruct (next_facts Dd Gd D1a Sa n1 L2 s2 D2 n2 Sb Tb (apC s1 G) HLo1 HLE1 HLv1 Sem2 HTb HEb LvTb HG1 HGL1 HC1)
      as (HLo2 & HLE2 & HLv2 & _ & _ & _).
    set (Ln := lnext s2 L2 Tb) in *.
    pose proof (SemL_DOk Sem2) as Hd2.
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem2) HTa) as HTa2.
    assert (Hle : n2 <= S n2) by lia.
    assert (HTv : TOk (S n2) (typ_Var (ea n2))) by (apply TOk_var; apply old_ea; lia).
    assert (HTarr : TOk (S n2) (typ_Arrow Tb (typ_Var (ea n2))))
      by (apply TOk_arrow; [ exact (TOk_mono _ _ _ Hle HTb) | exact HTv ]).
    assert (HsubTa : ftv_typ Ta [<=] L2) by exact (ftv_lnext s1 L Ta).
    assert (HsubTb : ftv_typ Tb [<=] Ln) by exact (ftv_lnext s2 L2 Tb).
    assert (HsubTa2 : ftv_typ (apT s2 Ta) [<=] Ln)
      by (intros y Hy; exact (limg_lnext s2 L2 Tb y (limg_ap s2 Ta L2 (proj1 HTa) HsubTa y Hy))).
    set (Lu := Ln `union` {{ ea n2 }}).
    assert (HLv3 : Live PEv Lu D2 Dd (supd Sb (ea n2) T2)).
    { exact (Live_fresh PEv Ln D2 D2 Dd Sb n2 k_Any T2 HLo2 HLv2 (sat_any _ _) HPT2
               (DOk_ea D2 n2 n2 Hd2 (le_n n2)) (fun _ _ => eq_refl)). }
    assert (Heq : teqD Dd (apT (supd Sb (ea n2) T2) (apT s2 Ta))
                          (apT (supd Sb (ea n2) T2) (typ_Arrow Tb (typ_Var (ea n2))))).
    { rewrite (apT_supd Sb (ea n2) T2 _ (proj1 HTa2) (fun Hin => proj2 HTa2 _ Hin n2 (le_n n2) eq_refl)).
      rewrite apT_Arrow, (apT_supd Sb (ea n2) T2 Tb (proj1 HTb) (fun Hin => proj2 HTb _ Hin n2 (le_n n2) eq_refl)),
        apT_Var, supd_same.
      eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor PEv L2 Dd Sa n1 s2 D2 n2 Sb Ta Sem2 (proj1 HTa) HsubTa) | ].
      eapply teqD_trans; [ exact Heq1 | ]. apply teqD_Arrow; [ apply teqD_sym; exact Heq2 | apply teqD_refl ]. }
    destruct (unify_stepL PEv Dd D2 (supd Sb (ea n2) T2) Lu (apT s2 Ta) (typ_Arrow Tb (typ_Var (ea n2))) (S n2)
                PEv_float (DOk_mono D2 n2 (S n2) Hd2 Hle) HRA2 (LOld_fresh n2 Ln HLo2) (LEv_fresh n2 Ln HLE2) HLv3
                (proj1 HTa2) (conj (proj1 HTb) I)
                (sub_ul _ _ _ HsubTa2)
                (ftv_arrow_sub _ _ _ (sub_ul _ _ _ HsubTb) (ftv_var_fresh n2 Ln)) Heq)
      as (s3 & D3 & n3 & S3 & St3 & Sem3 & HRA3).
    pose proof (SemL_unfresh PEv Ln Dd Sb n2 T2 s3 D3 n3 S3 HLo2 Sem3) as Sem3'.
    pose proof (SemL_comp PEv L L2 Dd Sg n s1 D1a n1 Sa s2 D2 n2 Sb HLo Sem1 (limg_lnext s1 L Ta) Sem2) as Sem12.
    pose proof (limg_chain n n1 s1 s2 L L2 Ln HLo (SemL_SI Sem1) (limg_lnext s1 L Ta) (limg_lnext s2 L2 Tb)) as Hc2.
    exists (scomp s3 (scomp s2 s1)), D3, n3, S3, (apT s3 (typ_Var (ea n2))), (e_app e1' e2').
    refine (conj _ (conj (SemL_comp PEv L Ln Dd Sg n (scomp s2 s1) D2 n2 Sb s3 D3 n3 S3 HLo Sem12 Hc2 Sem3')
              (conj _ (conj _ (conj _ (conj HRA3 (conj _ (conj _ _)))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 St3))) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2 & E3). cbn [infer]. rewrite E1, E2, E3. reflexivity.
    + exact (TOk_ap _ _ _ _ (SemL_SI Sem3) HTv).
    + exact (EvT_ap s3 _ (SemL_OkS Sem3) (EvT_var_ea n2)).
    + refine (SemL_live_ap PEv Lu Dd _ (S n2) s3 D3 n3 S3 (typ_Var (ea n2)) Sem3 I _).
      exact (ftv_var_fresh n2 Ln).
    + pose proof (SemL_F Sem3 (ea n2) (in_fresh n2 Ln)) as F.
      rewrite supd_same in F. apply teqD_sym. exact F.
    + cbn [is_gen_value]; try reflexivity; try assumption.
    + cbn [let_open]; reflexivity.
  - (* if *)
    assert (HAv1 : Avoid (bg (bg Av Gd T) Gd typ_Bool) L Sg).
    { refine (Avoid_mono _ _ _ _ (bg_av _ _ _) HAv). }
    destruct (IH1 D G n Sg L Hd HRA HLo HLE HLv HAv1 HG HGL HC)
      as (s1 & D1a & n1 & Sa & Tc & c' & St1 & Sem1 & HTc & HEc & LvTc & HRA1 & Heq1 & HgHeq1 & HlHeq1).
    destruct (next_facts Dd Gd D Sg n L s1 D1a n1 Sa Tc G HLo HLE HLv Sem1 HTc HEc LvTc HG HGL HC)
      as (HLo1 & HLE1 & HLv1 & HG1 & HGL1 & HC1).
    set (L1 := lnext s1 L Tc) in *.
    destruct (unify_stepL PEv Dd D1a Sa L1 Tc typ_Bool n1 PEv_float (SemL_DOk Sem1) HRA1 HLo1 HLE1 HLv1
                (proj1 HTc) I (ftv_lnext s1 L Tc) (sub_scalar typ_Bool L1 (or_intror (or_intror (or_introl eq_refl)))) Heq1)
      as (s2 & D1b & n2 & Sb & St2 & Sem2 & HRA2).
    destruct (CI_stepL L1 D1a Dd Sa n1 s2 D1b n2 Sb Gd (apC s1 G) Sem2 HLv1 HLE1 HC1 HG1 HGL1) as (HC2 & HG2 & HGL2).
    set (Lb := limg s2 L1).
    assert (HLob : LOld n2 Lb) by exact (limg_old _ _ _ _ HLo1 (SemL_SI Sem2)).
    assert (HLEb : LEv Lb) by exact (limg_ev s2 L1 (SemL_OkS Sem2) HLE1).
    assert (HAvA : Avoid (bg Av Gd T) L1 Sa).
    { refine (Avoid_next (bg Av Gd T) (bg Av Gd T) L D Dd Sg n s1 D1a n1 Sa Tc typ_Bool HLo
                (Avoid_mono _ _ _ _ (fun y Hy => Hy) HAv) HLv Sem1 HTc LvTc Heq1 (fun y Hy => Hy) _).
      intros y Hy. simpl in Hy. apply AtomSetFacts.empty_iff in Hy. contradiction. }
    assert (HAvb : Avoid (bg Av Gd T) Lb Sb)
      by exact (Avoid_limg _ L1 D1a Dd Sa n1 s2 D1b n2 Sb HLo1 HAvA HLv1 Sem2).
    destruct (IH2 D1b (apC s2 (apC s1 G)) n2 Sb Lb (SemL_DOk Sem2) HRA2 HLob HLEb (SemL_live Sem2)
                (Avoid_mono _ _ _ _ (bg_av _ _ _) HAvb) HG2 HGL2 HC2)
      as (s3 & D3 & n3 & Sc & Ta & a' & St3 & Sem3 & HTa & HEa & LvTa & HRA3 & Heq2 & HgHeq2 & HlHeq2).
    destruct (next_facts Dd Gd D1b Sb n2 Lb s3 D3 n3 Sc Ta (apC s2 (apC s1 G)) HLob HLEb (SemL_live Sem2) Sem3 HTa HEa LvTa
                HG2 HGL2 HC2)
      as (HLo3 & HLE3 & HLv3 & HG3 & HGL3 & HC3).
    set (L3 := lnext s3 Lb Ta) in *.
    assert (HAv3 : Avoid (bg Av Gd T) L3 Sc).
    { refine (Avoid_next (bg Av Gd T) (bg Av Gd T) Lb D1b Dd Sb n2 s3 D3 n3 Sc Ta T HLob HAvb (SemL_live Sem2) Sem3 HTa LvTa
                Heq2 (fun y Hy => Hy) _).
      apply bg_ftv. }
    destruct (IH3 D3 (apC s3 (apC s2 (apC s1 G))) n3 Sc L3 (SemL_DOk Sem3) HRA3 HLo3 HLE3 HLv3
                (Avoid_mono _ _ _ _ (bg_av _ _ _) HAv3) HG3 HGL3 HC3)
      as (s4 & D4 & n4 & Sd & Tb & b' & St4 & Sem4 & HTb & HEb & LvTb & HRA4 & Heq3 & HgHeq3 & HlHeq3).
    destruct (next_facts Dd Gd D3 Sc n3 L3 s4 D4 n4 Sd Tb (apC s3 (apC s2 (apC s1 G))) HLo3 HLE3 HLv3 Sem4 HTb HEb LvTb
                HG3 HGL3 HC3)
      as (HLo4 & HLE4 & HLv4 & _ & _ & _).
    set (L4 := lnext s4 L3 Tb) in *.
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem4) HTa) as HTa4.
    assert (HsubTa : ftv_typ Ta [<=] L3) by exact (ftv_lnext s3 Lb Ta).
    assert (HsubTa4 : ftv_typ (apT s4 Ta) [<=] L4)
      by (intros y Hy; exact (limg_lnext s4 L3 Tb y (limg_ap s4 Ta L3 (proj1 HTa) HsubTa y Hy))).
    assert (Heq : teqD Dd (apT Sd (apT s4 Ta)) (apT Sd Tb)).
    { eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor PEv L3 Dd Sc n3 s4 D4 n4 Sd Ta Sem4 (proj1 HTa) HsubTa) | ].
      eapply teqD_trans; [ exact Heq2 | apply teqD_sym; exact Heq3 ]. }
    destruct (unify_stepL PEv Dd D4 Sd L4 (apT s4 Ta) Tb n4 PEv_float (SemL_DOk Sem4) HRA4 HLo4 HLE4 HLv4
                (proj1 HTa4) (proj1 HTb) HsubTa4 (ftv_lnext s4 L3 Tb) Heq)
      as (s5 & D5 & n5 & Se & St5 & Sem5 & HRA5).
    pose proof (SemL_comp PEv L L1 Dd Sg n s1 D1a n1 Sa s2 D1b n2 Sb HLo Sem1 (limg_lnext s1 L Tc)
      Sem2) as Sem12.
    pose proof (limg_chain n n1 s1 s2 L L1 Lb HLo (SemL_SI Sem1) (limg_lnext s1 L Tc) (fun _ H => H)) as Hc2.
    pose proof (SemL_comp PEv L Lb Dd Sg n (scomp s2 s1) D1b n2 Sb s3 D3 n3 Sc HLo Sem12 Hc2 Sem3) as Sem123.
    pose proof (SI_comp _ _ _ _ _ (SemL_SI Sem1) (SemL_SI Sem2)) as SI12.
    pose proof (limg_chain n n2 (scomp s2 s1) s3 L Lb L3 HLo SI12 Hc2 (limg_lnext s3 Lb Ta)) as Hc3.
    pose proof (SemL_comp PEv L L3 Dd Sg n (scomp s3 (scomp s2 s1)) D3 n3 Sc s4 D4 n4 Sd HLo Sem123 Hc3 Sem4) as Sem1234.
    pose proof (SI_comp _ _ _ _ _ SI12 (SemL_SI Sem3)) as SI123.
    pose proof (limg_chain n n3 (scomp s3 (scomp s2 s1)) s4 L L3 L4 HLo SI123 Hc3 (limg_lnext s4 L3 Tb)) as Hc4.
    exists (scomp s5 (scomp s4 (scomp s3 (scomp s2 s1)))), D5, n5, Se, (apT s5 Tb), (e_ite c' a' b').
    refine (conj _ (conj (SemL_comp PEv L L4 Dd Sg n _ D4 n4 Sd s5 D5 n5 Se HLo Sem1234 Hc4 Sem5)
              (conj _ (conj _ (conj _ (conj HRA5 (conj _ (conj _ _)))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3
        (Stable_and _ _ St4 St5))))) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2 & E3 & E4 & E5). cbn [infer]. rewrite E1, E2, E3, E4, E5. reflexivity.
    + exact (TOk_ap _ _ _ _ (SemL_SI Sem5) HTb).
    + exact (EvT_ap s5 _ (SemL_OkS Sem5) HEb).
    + exact (SemL_live_ap PEv L4 Dd Sd n4 s5 D5 n5 Se Tb Sem5 (proj1 HTb) (ftv_lnext s4 L3 Tb)).
    + eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor PEv L4 Dd Sd n4 s5 D5 n5 Se Tb Sem5 (proj1 HTb) (ftv_lnext s4 L3 Tb)) | ].
      exact Heq3.
    + cbn [is_gen_value]; try reflexivity; try assumption.
    + cbn [let_open]; reflexivity.
  - (* float(e) *)
    assert (HAv1 : Avoid (bg (bg Av Gd typ_Float `union` ats A) Gd A) L Sg)
      by exact (Avoid_mono _ _ _ _ (bg_av _ _ _) (Avoid_mono _ _ _ _ (sub_ul _ _ _ (sub_id _)) HAv)).
    destruct (IH1 D G n Sg L Hd HRA HLo HLE HLv HAv1 HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e' & St1 & Sem1 & HTa & HEa & LvTa & HRA1 & Heq1 & HgHeq1 & HlHeq1).
    destruct (next_facts Dd Gd D Sg n L s1 D1a n1 Sa Ta G HLo HLE HLv Sem1 HTa HEa LvTa HG HGL HC)
      as (HLo1 & HLE1 & HLv1 & _ & _ & _).
    set (L1 := lnext s1 L Ta) in *.
    assert (Hle : n1 <= S n1) by lia.
    assert (HTv : TOk (S n1) (typ_Var (ea n1))) by (apply TOk_var; apply old_ea; lia).
    assert (HsubTa : ftv_typ Ta [<=] L1) by exact (ftv_lnext s1 L Ta).
    assert (HLv2 : Live PEv (L1 `union` {{ ea n1 }}) (upd D1a (ea n1) k_Literal) Dd (supd Sa (ea n1) A)).
    { refine (Live_fresh PEv L1 D1a (upd D1a (ea n1) k_Literal) Dd Sa n1 k_Literal A HLo1 HLv1 Hs HPA
                (upd_same _ _ _) (fun a Ha => upd_other D1a (ea n1) k_Literal a (fun E => HLo1 a Ha n1 (le_n n1) E))). }
    assert (Heq : teqD Dd (apT (supd Sa (ea n1) A) Ta) (apT (supd Sa (ea n1) A) (typ_Var (ea n1)))).
    { rewrite (apT_supd Sa (ea n1) A Ta (proj1 HTa) (fun Hin => proj2 HTa _ Hin n1 (le_n n1) eq_refl)),
        apT_Var, supd_same. exact Heq1. }
    destruct (unify_stepL PEv Dd (upd D1a (ea n1) k_Literal) (supd Sa (ea n1) A) (L1 `union` {{ ea n1 }})
                Ta (typ_Var (ea n1)) (S n1) PEv_float (DOk_upd D1a n1 k_Literal (SemL_DOk Sem1)) (RA_upd _ _ _ HRA1)
                (LOld_fresh n1 L1 HLo1) (LEv_fresh n1 L1 HLE1) HLv2 (proj1 HTa) I
                (sub_ul _ _ _ HsubTa) (ftv_var_fresh n1 L1) Heq) as (s2 & D2 & n2 & S3 & St2 & Sem2 & HRA2).
    pose proof (SemL_unfresh PEv L1 Dd Sa n1 A s2 D2 n2 S3 HLo1 Sem2) as Sem2'.
    exists (scomp s2 s1), D2, n2, S3, typ_Float, (e_tofloat e').
    refine (conj _ (conj (SemL_comp PEv L L1 Dd Sg n s1 D1a n1 Sa s2 D2 n2 S3 HLo Sem1 (limg_lnext s1 L Ta) Sem2')
              (conj _ (conj _ (conj _ (conj HRA2 (conj _ (conj _ _)))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 St2)) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2). cbn [infer]. rewrite E1, E2. reflexivity.
    + apply TOk_scalar. right. left. reflexivity.
    + apply EvT_scalar. right. left. reflexivity.
    + apply Live_scalar. right. left. reflexivity.
    + apply teqD_refl.
    + cbn [is_gen_value]; try reflexivity; try assumption.
    + cbn [let_open]; reflexivity.
  - (* arithmetic *)
    assert (HAvX : Avoid (bg Av Gd A `union` ats A `union` ats A) L Sg)
      by exact (Avoid_mono _ _ _ _ (sub_ul _ _ _ (sub_id _)) HAv).
    assert (HAv1 : Avoid (bg (bg Av Gd A `union` ats A `union` ats A) Gd A) L Sg)
      by exact (Avoid_mono _ _ _ _ (bg_av _ _ _) HAvX).
    destruct (IH1 D G n Sg L Hd HRA HLo HLE HLv HAv1 HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & HEa & LvTa & HRA1 & Heq1 & HgHeq1 & HlHeq1).
    destruct (next_facts Dd Gd D Sg n L s1 D1a n1 Sa Ta G HLo HLE HLv Sem1 HTa HEa LvTa HG HGL HC)
      as (HLo1 & HLE1 & HLv1 & HG1 & HGL1 & HC1).
    set (L1 := lnext s1 L Ta) in *.
    assert (HAv2 : Avoid (bg (bg Av Gd A `union` ats A `union` ats A) Gd A) L1 Sa).
    { refine (Avoid_mono _ _ _ _ (bg_av _ _ _) _).
      exact (Avoid_next _ _ L D Dd Sg n s1 D1a n1 Sa Ta A HLo HAvX HLv Sem1 HTa LvTa Heq1 (sub_id _)
               (fun y Hy => sub_ur _ _ _ (sub_ul _ _ _ (sub_id _)) y (ats_ftv A y Hy))). }
    destruct (IH2 D1a (apC s1 G) n1 Sa L1 (SemL_DOk Sem1) HRA1 HLo1 HLE1 HLv1 HAv2 HG1 HGL1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & HEb & LvTb & HRA2 & Heq2 & HgHeq2 & HlHeq2).
    destruct (next_facts Dd Gd D1a Sa n1 L1 s2 D2 n2 Sb Tb (apC s1 G) HLo1 HLE1 HLv1 Sem2 HTb HEb LvTb HG1 HGL1 HC1)
      as (HLo2 & HLE2 & HLv2 & _ & _ & _).
    set (Ln := lnext s2 L1 Tb) in *.
    assert (HTv : TOk (S n2) (typ_Var (ea n2))) by (apply TOk_var; apply old_ea; lia).
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem2) HTa) as HTa2.
    assert (HsubTa : ftv_typ Ta [<=] L1) by exact (ftv_lnext s1 L Ta).
    assert (HsubTb : ftv_typ Tb [<=] Ln) by exact (ftv_lnext s2 L1 Tb).
    assert (HsubTa2 : ftv_typ (apT s2 Ta) [<=] Ln)
      by (intros y Hy; exact (limg_lnext s2 L1 Tb y (limg_ap s2 Ta L1 (proj1 HTa) HsubTa y Hy))).
    assert (Hg : sat Dd (generic_sort o) A) by exact Hs.
    assert (HLv3 : Live PEv (Ln `union` {{ ea n2 }}) (upd D2 (ea n2) (generic_sort o)) Dd (supd Sb (ea n2) A)).
    { refine (Live_fresh PEv Ln D2 (upd D2 (ea n2) (generic_sort o)) Dd Sb n2 (generic_sort o) A HLo2 HLv2 Hg HPA
                (upd_same _ _ _) (fun a Ha => upd_other D2 (ea n2) (generic_sort o) a (fun E => HLo2 a Ha n2 (le_n n2) E))). }
    assert (Heq : teqD Dd (apT (supd Sb (ea n2) A) (apT s2 Ta)) (apT (supd Sb (ea n2) A) (typ_Var (ea n2)))).
    { rewrite (apT_supd Sb (ea n2) A _ (proj1 HTa2) (fun Hin => proj2 HTa2 _ Hin n2 (le_n n2) eq_refl)),
        apT_Var, supd_same.
      eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor PEv L1 Dd Sa n1 s2 D2 n2 Sb Ta Sem2 (proj1 HTa) HsubTa) | ].
      exact Heq1. }
    destruct (unify_stepL PEv Dd (upd D2 (ea n2) (generic_sort o)) (supd Sb (ea n2) A) (Ln `union` {{ ea n2 }})
                (apT s2 Ta) (typ_Var (ea n2)) (S n2) PEv_float (DOk_upd D2 n2 _ (SemL_DOk Sem2)) (RA_upd _ _ _ HRA2)
                (LOld_fresh n2 Ln HLo2) (LEv_fresh n2 Ln HLE2) HLv3 (proj1 HTa2) I
                (sub_ul _ _ _ HsubTa2) (ftv_var_fresh n2 Ln) Heq) as (s3 & D3 & n3 & S3 & St3 & Sem3 & HRA3).
    pose proof (SemL_unfresh PEv Ln Dd Sb n2 A s3 D3 n3 S3 HLo2 Sem3) as Sem3'.
    set (Lu := Ln `union` {{ ea n2 }}) in *.
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem3) HTv) as HTc3.
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem3') HTb) as HTb3.
    assert (Fc : teqD Dd A (apT S3 (apT s3 (typ_Var (ea n2))))).
    { pose proof (SemL_F Sem3 (ea n2) (in_fresh n2 Ln)) as F. rewrite supd_same in F. exact F. }
    assert (Heq' : teqD Dd (apT S3 (apT s3 Tb)) (apT S3 (apT s3 (typ_Var (ea n2))))).
    { eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor PEv Ln Dd Sb n2 s3 D3 n3 S3 Tb Sem3' (proj1 HTb) HsubTb) | ].
      eapply teqD_trans; [ exact Heq2 | exact Fc ]. }
    assert (HLo3 : LOld n3 (limg s3 Lu)) by exact (limg_old _ _ _ _ (LOld_fresh n2 Ln HLo2) (SemL_SI Sem3)).
    assert (HLE3 : LEv (limg s3 Lu)) by exact (limg_ev s3 Lu (SemL_OkS Sem3) (LEv_fresh n2 Ln HLE2)).
    destruct (unify_stepL PEv Dd D3 S3 (limg s3 Lu) (apT s3 Tb) (apT s3 (typ_Var (ea n2))) n3 PEv_float (SemL_DOk Sem3)
                HRA3 HLo3 HLE3 (SemL_live Sem3) (proj1 HTb3) (proj1 HTc3)
                (limg_ap s3 Tb Lu (proj1 HTb) (sub_ul _ _ _ HsubTb))
                (limg_ap s3 (typ_Var (ea n2)) Lu I (ftv_var_fresh n2 Ln)) Heq')
      as (s4 & D4 & n4 & S4 & St4 & Sem4 & HRA4).
    pose proof (SemL_comp PEv L L1 Dd Sg n s1 D1a n1 Sa s2 D2 n2 Sb HLo Sem1 (limg_lnext s1 L Ta) Sem2) as Sem12.
    pose proof (limg_chain n n1 s1 s2 L L1 Ln HLo (SemL_SI Sem1) (limg_lnext s1 L Ta) (limg_lnext s2 L1 Tb)) as Hc2.
    pose proof (SemL_comp PEv L Ln Dd Sg n (scomp s2 s1) D2 n2 Sb s3 D3 n3 S3 HLo Sem12 Hc2 Sem3') as Sem123.
    pose proof (SI_comp _ _ _ _ _ (SemL_SI Sem1) (SemL_SI Sem2)) as SI12.
    pose proof (limg_chain n n2 (scomp s2 s1) s3 L Ln (limg s3 Lu) HLo SI12 Hc2
      (limg_mono s3 _ _ (sub_ul _ _ _ (fun _ H => H)))) as Hc3.
    exists (scomp s4 (scomp s3 (scomp s2 s1))), D4, n4, S4, (apT s4 (apT s3 (typ_Var (ea n2)))), (e_bin e1' o e2').
    refine (conj _ (conj (SemL_comp PEv L (limg s3 Lu) Dd Sg n _ D3 n3 S3 s4 D4 n4 S4 HLo Sem123 Hc3 Sem4)
              (conj _ (conj _ (conj _ (conj HRA4 (conj _ (conj _ _)))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3 St4)))) as HSt.
      stable_run HSt. destruct Hf as (E1 & E2 & E3 & E4). cbn [infer]. rewrite E1, E2.
      rewrite (is_cmp_op_false o Hk1). cbv beta iota zeta.
      rewrite E3, E4. rewrite (bin_res_arith o _ Hk1). reflexivity.
    + exact (TOk_ap _ _ _ _ (SemL_SI Sem4) HTc3).
    + exact (EvT_ap s4 _ (SemL_OkS Sem4) (EvT_ap s3 _ (SemL_OkS Sem3) (EvT_var_ea n2))).
    + exact (SemL_live_ap PEv (limg s3 Lu) Dd S3 n3 s4 D4 n4 S4 _ Sem4 (proj1 HTc3) (limg_ap s3 (typ_Var (ea n2)) Lu I (ftv_var_fresh n2 Ln))).
    + eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor PEv (limg s3 Lu) Dd S3 n3 s4 D4 n4 S4 _ Sem4 (proj1 HTc3) (limg_ap s3 (typ_Var (ea n2)) Lu I (ftv_var_fresh n2 Ln))) | ].
      apply teqD_sym. exact Fc.
    + cbn [is_gen_value]; try reflexivity; try assumption.
    + cbn [let_open]; reflexivity.
  - (* comparison *)
    assert (HAvX : Avoid (bg Av Gd typ_Bool `union` ats A `union` ats A) L Sg)
      by exact (Avoid_mono _ _ _ _ (sub_ul _ _ _ (sub_id _)) HAv).
    assert (HAv1 : Avoid (bg (bg Av Gd typ_Bool `union` ats A `union` ats A) Gd A) L Sg)
      by exact (Avoid_mono _ _ _ _ (bg_av _ _ _) HAvX).
    destruct (IH1 D G n Sg L Hd HRA HLo HLE HLv HAv1 HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & HEa & LvTa & HRA1 & Heq1 & HgHeq1 & HlHeq1).
    destruct (next_facts Dd Gd D Sg n L s1 D1a n1 Sa Ta G HLo HLE HLv Sem1 HTa HEa LvTa HG HGL HC)
      as (HLo1 & HLE1 & HLv1 & HG1 & HGL1 & HC1).
    set (L1 := lnext s1 L Ta) in *.
    assert (HAv2 : Avoid (bg (bg Av Gd typ_Bool `union` ats A `union` ats A) Gd A) L1 Sa).
    { refine (Avoid_mono _ _ _ _ (bg_av _ _ _) _).
      exact (Avoid_next _ _ L D Dd Sg n s1 D1a n1 Sa Ta A HLo HAvX HLv Sem1 HTa LvTa Heq1 (sub_id _)
               (fun y Hy => sub_ur _ _ _ (sub_ul _ _ _ (sub_id _)) y (ats_ftv A y Hy))). }
    destruct (IH2 D1a (apC s1 G) n1 Sa L1 (SemL_DOk Sem1) HRA1 HLo1 HLE1 HLv1 HAv2 HG1 HGL1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & HEb & LvTb & HRA2 & Heq2 & HgHeq2 & HlHeq2).
    destruct (next_facts Dd Gd D1a Sa n1 L1 s2 D2 n2 Sb Tb (apC s1 G) HLo1 HLE1 HLv1 Sem2 HTb HEb LvTb HG1 HGL1 HC1)
      as (HLo2 & HLE2 & HLv2 & _ & _ & _).
    set (Ln := lnext s2 L1 Tb) in *.
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem2) HTa) as HTa2.
    assert (HsubTa : ftv_typ Ta [<=] L1) by exact (ftv_lnext s1 L Ta).
    assert (HsubTb : ftv_typ Tb [<=] Ln) by exact (ftv_lnext s2 L1 Tb).
    assert (HsubTa2 : ftv_typ (apT s2 Ta) [<=] Ln)
      by (intros y Hy; exact (limg_lnext s2 L1 Tb y (limg_ap s2 Ta L1 (proj1 HTa) HsubTa y Hy))).
    assert (Heq : teqD Dd (apT Sb (apT s2 Ta)) (apT Sb Tb)).
    { eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor PEv L1 Dd Sa n1 s2 D2 n2 Sb Ta Sem2 (proj1 HTa) HsubTa) | ].
      eapply teqD_trans; [ exact Heq1 | apply teqD_sym; exact Heq2 ]. }
    destruct (unify_stepL PEv Dd D2 Sb Ln (apT s2 Ta) Tb n2 PEv_float (SemL_DOk Sem2) HRA2 HLo2 HLE2 HLv2
                (proj1 HTa2) (proj1 HTb) HsubTa2 HsubTb Heq) as (s3 & D3 & n3 & S3 & St3 & Sem3 & HRA3).
    pose proof (TOk_ap _ _ _ _ (SemL_SI Sem3) HTb) as HTb3.
    assert (HTv : TOk (S n3) (typ_Var (ea n3))) by (apply TOk_var; apply old_ea; lia).
    assert (HLo3 : LOld n3 (limg s3 Ln)) by exact (limg_old _ _ _ _ HLo2 (SemL_SI Sem3)).
    assert (HLE3 : LEv (limg s3 Ln)) by exact (limg_ev s3 Ln (SemL_OkS Sem3) HLE2).
    assert (HsubTb3 : ftv_typ (apT s3 Tb) [<=] limg s3 Ln) by exact (limg_ap s3 Tb Ln (proj1 HTb) HsubTb).
    assert (HLv4 : Live PEv (limg s3 Ln `union` {{ ea n3 }}) (upd D3 (ea n3) k_Eq) Dd (supd S3 (ea n3) A)).
    { refine (Live_fresh PEv (limg s3 Ln) D3 (upd D3 (ea n3) k_Eq) Dd S3 n3 k_Eq A HLo3 (SemL_live Sem3) Hs HPA
                (upd_same _ _ _) (fun a Ha => upd_other D3 (ea n3) k_Eq a (fun E => HLo3 a Ha n3 (le_n n3) E))). }
    assert (Heq' : teqD Dd (apT (supd S3 (ea n3) A) (apT s3 Tb)) (apT (supd S3 (ea n3) A) (typ_Var (ea n3)))).
    { rewrite (apT_supd S3 (ea n3) A _ (proj1 HTb3) (fun Hin => proj2 HTb3 _ Hin n3 (le_n n3) eq_refl)),
        apT_Var, supd_same.
      eapply teqD_trans; [ apply teqD_sym; exact (SemL_factor PEv Ln Dd Sb n2 s3 D3 n3 S3 Tb Sem3 (proj1 HTb) HsubTb) | ].
      exact Heq2. }
    destruct (unify_stepL PEv Dd (upd D3 (ea n3) k_Eq) (supd S3 (ea n3) A) (limg s3 Ln `union` {{ ea n3 }})
                (apT s3 Tb) (typ_Var (ea n3)) (S n3) PEv_float (DOk_upd D3 n3 k_Eq (SemL_DOk Sem3)) (RA_upd _ _ _ HRA3)
                (LOld_fresh n3 _ HLo3) (LEv_fresh n3 _ HLE3) HLv4 (proj1 HTb3) I
                (sub_ul _ _ _ HsubTb3) (ftv_var_fresh n3 _) Heq') as (s4 & D4 & n4 & S4 & St4 & Sem4 & HRA4).
    pose proof (SemL_unfresh PEv (limg s3 Ln) Dd S3 n3 A s4 D4 n4 S4 HLo3 Sem4) as Sem4'.
    pose proof (SemL_comp PEv L L1 Dd Sg n s1 D1a n1 Sa s2 D2 n2 Sb HLo Sem1 (limg_lnext s1 L Ta) Sem2) as Sem12.
    pose proof (limg_chain n n1 s1 s2 L L1 Ln HLo (SemL_SI Sem1) (limg_lnext s1 L Ta) (limg_lnext s2 L1 Tb)) as Hc2.
    pose proof (SemL_comp PEv L Ln Dd Sg n (scomp s2 s1) D2 n2 Sb s3 D3 n3 S3 HLo Sem12 Hc2 Sem3) as Sem123.
    pose proof (SI_comp _ _ _ _ _ (SemL_SI Sem1) (SemL_SI Sem2)) as SI12.
    pose proof (limg_chain n n2 (scomp s2 s1) s3 L Ln (limg s3 Ln) HLo SI12 Hc2 (fun _ H => H)) as Hc3.
    exists (scomp s4 (scomp s3 (scomp s2 s1))), D4, n4, S4, typ_Bool, (e_bin e1' o e2').
    refine (conj _ (conj (SemL_comp PEv L (limg s3 Ln) Dd Sg n _ D3 n3 S3 s4 D4 n4 S4 HLo Sem123 Hc3 Sem4')
              (conj _ (conj _ (conj _ (conj HRA4 (conj _ (conj _ _)))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3 St4)))) as HSt.
      stable_run HSt. destruct Hf as (E1 & E2 & E3 & E4). cbn [infer]. rewrite E1, E2.
      rewrite (is_cmp_op_true o Hk). cbv beta iota zeta. rewrite E3, E4. reflexivity.
    + apply TOk_scalar. right. right. left. reflexivity.
    + apply EvT_scalar. right. right. left. reflexivity.
    + apply Live_scalar. right. right. left. reflexivity.
    + apply teqD_refl.
    + cbn [is_gen_value]; try reflexivity; try assumption.
    + cbn [let_open]; reflexivity.
  - (* let of a binding that is not a value *)
    assert (HAvX : Avoid (bg Av Gd T2 `union` ats T1) L Sg)
      by exact (Avoid_mono _ _ _ _ (sub_ul _ _ _ (sub_id _)) HAv).
    assert (HAv1 : Avoid (bg (bg Av Gd T2 `union` ats T1) Gd T1) L Sg)
      by exact (Avoid_mono _ _ _ _ (bg_av _ _ _) HAvX).
    destruct (IH1 D G n Sg L Hd HRA HLo HLE HLv HAv1 HG HGL HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & HEa & LvTa & HRA1 & Heq1 & Hgv & Hlo1).
    destruct (next_facts Dd Gd D Sg n L s1 D1a n1 Sa Ta G HLo HLE HLv Sem1 HTa HEa LvTa HG HGL HC)
      as (HLo1 & HLE1 & HLv1 & HG1 & HGL1 & HC1).
    set (L1 := lnext s1 L Ta) in *.
    rewrite Hv in Hgv.
    assert (HAvX2 : Avoid (bg Av Gd T2 `union` ats T1) L1 Sa).
    { exact (Avoid_next _ _ L D Dd Sg n s1 D1a n1 Sa Ta T1 HLo HAvX HLv Sem1 HTa LvTa Heq1 (sub_id _)
               (fun y Hy => sub_ur _ _ _ (ats_ftv T1) y Hy)). }
    assert (HAv2 : Avoid (bg (bg Av Gd T2 `union` ats T1) Gd T1) L1 Sa)
      by exact (Avoid_mono _ _ _ _ (bg_av _ _ _) HAvX2).
    assert (Hx : fresh_var (apC s1 G) e2 `notin` dom Gd `union` fv_exp e2).
    { rewrite (CI_dom _ _ _ _ HC). pose proof (dom_apC s1 G).
      pose proof (fresh_var_notin_dom (apC s1 G) e2). pose proof (fresh_var_notin_fv (apC s1 G) e2). fsetdec. }
    assert (HAv3 : Avoid (bg (bg Av Gd T2 `union` ats T1) ((fresh_var (apC s1 G) e2 ~ sch_mono T1) ++ Gd) T2) L1 Sa).
    { exact (Avoid_mono _ _ _ _ (bg_av _ _ _) HAvX2). }
    destruct (IH2 _ Hx D1a ((fresh_var (apC s1 G) e2 ~ sch_mono Ta) ++ apC s1 G) n1 Sa L1
                (SemL_DOk Sem1) HRA1 HLo1 HLE1 HLv1 HAv3 (GOk_cons n1 _ Ta _ HTa HEa HG1)
                (GLive_cons L1 _ Ta _ (ftv_lnext s1 L Ta) HGL1)
                (CI_cons Dd Sa Gd (apC s1 G) _ T1 Ta HC1 Heq1))
      as (s2 & D2 & n2 & Sb & T & e2' & St2 & Sem2 & HT & HE & LvT & HRA2 & Heq2 & Hg2 & Hl2).
    exists (scomp s2 s1), D2, n2, Sb, T, (e_let e1' (cl 0 (fresh_var (apC s1 G) e2) e2')).
    refine (conj _ (conj (SemL_comp PEv L L1 Dd Sg n s1 D1a n1 Sa s2 D2 n2 Sb HLo Sem1 (limg_lnext s1 L Ta) Sem2)
      (conj HT (conj HE (conj LvT (conj HRA2 (conj Heq2 (conj _ _)))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 St2)) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2). cbn [infer]. rewrite E1, Hgv. cbn [andb]. cbv beta iota zeta. rewrite E2. reflexivity.
    + reflexivity.
    + reflexivity.
  - (* let of a value *)
    pose proof (proj1 (proj2 (proj2 (rf_facts T1 Hrf1)))) as Hfrv1.
    set (Vt := AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm Gd))) in *.
    set (Vr := AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm Gd))) in *.
    set (Dg := extr (ext Dd Vt k) Vr rk) in *.
    assert (Hdsort : forall c, c `notin` Vt -> Dg c = Dd c)
      by (intros c Hc; unfold Dg; rewrite extr_dsort; exact (ext_out _ _ _ _ Hc)).
    assert (Hdrk : forall r, drk Dg r = drk Dd r).
    { intros r. unfold Dg. rewrite extr_out; [ apply ext_drk | ].
      intro Hr. unfold Vr in Hr. apply AtomSetFacts.diff_iff in Hr. exact (Hfrv1 r (proj1 Hr)). }
    assert (HGdV : forall a, a `in` ftv_ctx Gd -> a `notin` Vt).
    { intros a Ha Hv. unfold Vt in Hv. apply AtomSetFacts.diff_iff in Hv. apply (proj2 Hv).
      apply (proj2 (ftv_pin_ctx Tm Gd a)). apply AtomSetFacts.union_iff. right. exact Ha. }
    assert (HVt : forall c, c `in` Vt -> c `notin` bg Av Gd T2) by (intros c Hc; exact (proj2 (HevA c Hc))).
    assert (HAvT : forall x0, x0 `in` L -> forall c, c `in` ftv_typ (sT Sg x0) -> Dg c = Dd c).
    { intros x0 Hx0 c Hc. apply Hdsort. intro Hcv. exact (HVt c Hcv (HAv x0 Hx0 c Hc)). }
    assert (HLvg : Live PEv L D Dg Sg) by exact (Live_env L D Dd Dg Sg HLv HAvT Hdrk).
    assert (HCg : CI Dg Sg Gd G)
      by exact (CI_env Dd Dg Sg Gd G HC (fun a Ha => Hdsort a (HGdV a Ha)) Hdrk).
    destruct (IH1 D G n Sg L Hd HRA HLo HLE HLvg (Avoid_mono _ _ _ _ (bg_av _ _ _) HAv) HG HGL HCg)
      as (s1 & D1 & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & HEa & LvTa & HRA1 & Heq1 & Hgv1 & Hlo1).
    destruct (next_facts Dg Gd D Sg n L s1 D1 n1 Sa Ta G HLo HLE HLvg Sem1 HTa HEa LvTa HG HGL HCg)
      as (HLo1 & HLE1 & HLv1 & HG1 & HGL1 & HC1).
    destruct (CI_stepL L D Dg Sg n s1 D1 n1 Sa Gd G Sem1 HLvg HLE HCg HG HGL) as (_ & _ & HGLl).
    assert (Hgv1' : is_gen_value e1' = true) by (rewrite Hgv1; exact Hgv).
    assert (HrfA : rf (apT Sa Ta)).
    { apply rf_ap; [ exact (proj1 HTa) | intros w Hw; exact (proj2 (proj2 (LvTa w Hw))) ]. }
    pose proof (teqD_rf_eq _ _ _ HrfA Heq1) as ET.
    pose proof (SemL_OkS Sem1) as Hok1.
    destruct (gen_ren_sc D1 (pin_ctx (let_pin D1 e1' Ta) (apC s1 G)) Ta n1 HTa HEa) as (Hsc & Hscf & Hscc).
    set (G1 := apC s1 G) in *.
    set (sc := gen_ren D1 (pin_ctx (let_pin D1 e1' Ta) G1) Ta) in *.
    set (L1 := lnext s1 L Ta) in *.
    set (Lb := limg s1 L `union` ftv_sch sc).
    assert (HlimL : limg s1 L [<=] Lb) by (intros y Hy; apply AtomSetFacts.union_iff; left; exact Hy).
    assert (HscLb : ftv_sch sc [<=] Lb) by (intros y Hy; apply AtomSetFacts.union_iff; right; exact Hy).
    assert (HLbL1 : Lb [<=] L1).
    { intros y Hy. apply AtomSetFacts.union_iff in Hy. destruct Hy as [Hy|Hy];
        [ exact (limg_lnext s1 L Ta y Hy) | exact (ftv_lnext s1 L Ta y (Hscf y Hy)) ]. }
    assert (HQ : forall b, b `in` s_tq sc -> b `notin` L1).
    { intros b Hbq HbL. exact (ev_od b (HLE1 b HbL) ((proj1 (proj1 Hsc)) b Hbq)). }
    assert (HSa'a : forall y, y `in` L1 -> sT (sfix (s_tq sc) Sa) y = sT Sa y).
    { intros y Hy. apply sfix_out. intro Hq. exact (HQ y Hq Hy). }
    assert (HG1ctx : ftv_ctx G1 [<=] limg s1 L) by exact (GLive_ftv_ctx _ _ HGLl).
    assert (HfzG1 : frozen (sfix (s_tq sc) Sa) G1 Gd).
    { split.
      - intros a Ha. assert (HaL : a `in` L1) by exact (limg_lnext s1 L Ta a (HG1ctx a Ha)).
        split.
        + rewrite (HSa'a a HaL).
          exact (CI_ftv Dg Sa Gd G1 n1 L1 D1 HC1 HG1 HGL1 HLv1 a Ha).
        + intros c Hc. exfalso.
          rewrite (HSa'a a HaL) in Hc.
          exact (proj1 (proj2 (proj2 (rf_facts _ (proj2 (proj2 (HLv1 a HaL)))))) c Hc).
      - intros r Hr. exfalso. exact (GOk_frv n1 G1 HG1 r Hr). }
    assert (EqS : apT (sfix (s_tq sc) Sa) Ta = T1).
    { rewrite ET. apply apT_agree; [ exact (proj1 HTa) | ]. intros a Ha. apply HSa'a. exact (ftv_lnext s1 L Ta a Ha). }
    assert (Hlit' : lit_pinned e1' (AtomSetImpl.diff (ftv_typ (apT (sfix (s_tq sc) Sa) Ta)) (ftv_ctx (pin_ctx Tm Gd))) k).
    { rewrite EqS. intros Ho. apply Hlit. rewrite <- Hlo1. exact Ho. }
    assert (Hk' : forall b, b `in` ftv_typ Ta ->
      sat (extr (ext Dd (AtomSetImpl.diff (ftv_typ (apT (sfix (s_tq sc) Sa) Ta)) (ftv_ctx (pin_ctx Tm Gd))) k)
            (AtomSetImpl.diff (frv_typ (apT (sfix (s_tq sc) Sa) Ta)) (frv_ctx (pin_ctx Tm Gd))) rk)
          (dsort D1 b) (sT (sfix (s_tq sc) Sa) b)).
    { intros b Hbq. rewrite EqS. rewrite (HSa'a b (ftv_lnext s1 L Ta b Hbq)).
      exact (proj1 (HLv1 b (ftv_lnext s1 L Ta b Hbq))). }
    pose proof (let_frozen Dd D1 (sfix (s_tq sc) Sa) G1 Gd Tm Ta e1' k rk HfzG1 Hlit' Hk') as Hfzp.
    assert (HfrvTa : forall q, q `notin` frv_typ Ta) by exact (proj1 (proj2 (proj2 (rf_facts Ta (proj1 HTa))))).
    assert (Hsch : sch_leP Dd (gen (pin_ctx Tm Gd) T1 k rk) (apS (sfix (s_tq sc) Sa) sc)).
    { pose proof (gen_mono_let Dd D1 (sfix (s_tq sc) Sa) G1 Gd Tm Ta e1' k rk HfzG1
        (fun b Hbq => sfix_in _ _ b Hbq)
        (fun r Hr => False_rect _ (proj1 (AtomSetFacts.empty_iff r) (proj1 (proj1 (proj2 Hsc) r) Hr)))
        (fun a Ha => ltac:(
           assert (HaL : a `in` L1);
           [ apply (proj1 (ftv_pin_ctx (let_pin D1 e1' Ta) G1 a)) in Ha;
             apply AtomSetFacts.union_iff in Ha; destruct Ha as [Ha|Ha];
             [ exact (ftv_lnext s1 L Ta a (let_pin_ftv D1 e1' Ta a Ha)) | exact (limg_lnext s1 L Ta a (HG1ctx a Ha)) ]
           | rewrite (HSa'a a HaL); exact (proj1 (proj2 (HLv1 a HaL))) ]))
        (fun r Hr => ltac:(
           exfalso; apply (proj1 (frv_pin_ctx (let_pin D1 e1' Ta) G1 r)) in Hr;
           apply AtomSetFacts.union_iff in Hr; destruct Hr as [Hr|Hr];
           [ exact (let_pin_frv D1 e1' Ta r Hr) | exact (GOk_frv n1 G1 HG1 r Hr) ]))
        (fun a Ha => ltac:(
           rewrite (HSa'a a (ftv_lnext s1 L Ta a Ha)); exact (proj2 (HLv1 a (ftv_lnext s1 L Ta a Ha)))))
        (fun r Hr => ltac:(exfalso; exact (HfrvTa r Hr)))
        Hlit' Hk'
        (fun r Hr => ltac:(exfalso; exact (HfrvTa r Hr)))) as Hg.
      rewrite EqS in Hg. exact Hg. }
    assert (Hsch2 : SchI Dd (sfix (s_tq sc) Sa) (gen (pin_ctx Tm Gd) T1 k rk) sc).
    { unfold SchI. rewrite apS_sfix_fixed; [ exact Hsch | exact (proj1 (proj2 (proj2 Hsc))) | ].
      intros q Hq. exact (sfix_in _ _ q Hq). }
    assert (HAvl : Avoid (bg Av Gd T2) (limg s1 L) Sa) by exact (Avoid_limg _ L D Dg Sg n s1 D1 n1 Sa HLo HAv HLvg Sem1).
    assert (HnotVt : forall y, y `in` Lb -> forall c, c `in` ftv_typ (sT Sa y) -> c `notin` Vt).
    { intros y Hy c Hc Hcv. apply AtomSetFacts.union_iff in Hy. destruct Hy as [Hy|Hy].
      - exact (HVt c Hcv (HAvl y Hy c Hc)).
      - pose proof (proj1 Hfzp y (Hscc y Hy)) as [Hf _].
        assert (Hc' : c `in` ftv_typ (sT (sfix (s_tq sc) Sa) y))
          by (rewrite (HSa'a y (ftv_lnext s1 L Ta y (Hscf y Hy))); exact Hc).
        pose proof (Hf c Hc') as Hin. unfold Vt in Hcv. apply AtomSetFacts.diff_iff in Hcv.
        exact (proj2 Hcv Hin). }
    assert (HLvb : Live PEv Lb D1 Dd (sfix (s_tq sc) Sa)).
    { intros y Hy. assert (HyL : y `in` L1) by exact (HLbL1 y Hy).
      rewrite (HSa'a y HyL). destruct (HLv1 y HyL) as [Hs Hp]. split; [ | exact Hp ].
      eapply sat_loc; [ | | exact Hs ].
      - intros c Hc. exact (eq_sym (Hdsort c (HnotVt y Hy c Hc))).
      - intros r _. exact (eq_sym (Hdrk r)). }
    assert (Sem1e : SemL PEv L Dd Sg n s1 D1 n1 Sa).
    { refine (SemL_env L Dg Dd Sg n s1 D1 n1 Sa Sem1 HRA1 _ (fun r => eq_sym (Hdrk r))).
      intros x0 Hx0 c Hc. exact (eq_sym (Hdsort c (fun Hv => HVt c Hv (HAvl x0 Hx0 c Hc)))). }
    assert (Sem1' : SemL PEv L Dd Sg n s1 D1 n1 (sfix (s_tq sc) Sa)).
    { refine (SemL_agree PEv L Dd Sg n s1 D1 n1 Sa (sfix (s_tq sc) Sa) HLo Sem1e _ eq_refl).
      intros y Hy. apply HSa'a. exact (limg_lnext s1 L Ta y Hy). }
    assert (HCd : CI Dd Sa Gd G1)
      by exact (CI_env Dg Dd Sa Gd G1 HC1 (fun a Ha => eq_sym (Hdsort a (HGdV a Ha))) (fun r => eq_sym (Hdrk r))).
    assert (HCd' : CI Dd (sfix (s_tq sc) Sa) Gd G1)
      by exact (CI_agree Dd Sa (sfix (s_tq sc) Sa) Gd G1 L1 n1 HCd HG1 HGL1 HSa'a).
    assert (Hx : fresh_var G1 e2 `notin` dom Gd `union` fv_exp e2) by exact (fresh_notin_Gd Dd Sg Gd G s1 e2 HC).
    assert (HAvb : Avoid (bg (bg Av Gd T2) ((fresh_var G1 e2 ~ gen (pin_ctx Tm Gd) T1 k rk) ++ Gd) T2) Lb
                     (sfix (s_tq sc) Sa)).
    { intros y Hy c Hc. apply AtomSetFacts.union_iff in Hy as Hy'. destruct Hy' as [Hy'|Hy'].
      - assert (HyL : y `in` L1) by exact (HLbL1 y Hy).
        rewrite (HSa'a y HyL) in Hc. apply bg_av. exact (HAvl y Hy' c Hc).
      - assert (HyL : y `in` L1) by exact (HLbL1 y Hy).
        rewrite (HSa'a y HyL) in Hc.
        apply ftv_sch_in_bg. apply (proj1 Hsch). unfold ftv_sch. cbn [apS s_body s_tq].
        apply AtomSetFacts.diff_iff. split.
        + assert (Hyb : y `in` ftv_typ (s_body sc))
            by (unfold ftv_sch in Hy'; apply AtomSetFacts.diff_iff in Hy'; exact (proj1 Hy')).
          assert (Hc2 : c `in` ftv_typ (sT (sfix (s_tq sc) Sa) y)) by (rewrite (HSa'a y HyL); exact Hc).
          exact (ftv_ap_in1 (sT (sfix (s_tq sc) Sa)) (sR (sfix (s_tq sc) Sa)) (s_body sc) c y Hyb Hc2).
        + intro Hcq. exact (ev_od c (proj1 (proj1 (proj2 (HLv1 y HyL))) c Hc) ((proj1 (proj1 Hsc)) c Hcq)). }
    destruct (IHb (fresh_var G1 e2) Hx D1 ((fresh_var G1 e2 ~ sc) ++ G1) n1 (sfix (s_tq sc) Sa) Lb
                (SemL_DOk Sem1) HRA1 (LOld_sub n1 Lb L1 HLbL1 HLo1) (LEv_sub Lb L1 HLbL1 HLE1) HLvb HAvb
                (GOk_cons_sch n1 _ sc G1 Hsc HG1)
                (GLive_cons_sch Lb _ sc G1 HscLb (GLive_mono _ _ _ HlimL HGLl))
                (CI_cons_sch Dd (sfix (s_tq sc) Sa) Gd G1 _ _ sc HCd' Hsch2))
      as (s2 & D2 & n2 & Sb & T & e2' & St2 & Sem2 & HT & HE & LvT & HRA2 & Heq2 & Hg2 & Hl2).
    destruct (SemL_sid_after PEv L Dd Sg n s1 D1 n1 (sfix (s_tq sc) Sa) HLo Sem1') as (Sem1s & Hlsid).
    exists (scomp s2 (scomp sid s1)), D2, n2, Sb, T, (e_let e1' (cl 0 (fresh_var G1 e2) e2')).
    refine (conj _ (conj (SemL_comp PEv L Lb Dd Sg n (scomp sid s1) D1 n1 (sfix (s_tq sc) Sa) s2 D2 n2 Sb HLo Sem1s
                            (fun y Hy => HlimL y (Hlsid y Hy)) Sem2)
      (conj HT (conj HE (conj LvT (conj HRA2 (conj Heq2 (conj _ _)))))))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 St2)) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2). cbn [infer]. rewrite E1, Hgv1', pres_owned_nil. cbn [negb andb]. cbn [length]. rewrite dis_nil.
      cbv beta iota zeta. rewrite apT_sid, apC_sid.
      unfold sc, G1 in E2. rewrite E2. reflexivity.
    + reflexivity.
    + reflexivity.
  - (* conversion *)
    assert (HAv1 : Avoid (bg (bg Av Gd T' `union` ats T) Gd T) L Sg)
      by exact (Avoid_mono _ _ _ _ (bg_av _ _ _) (Avoid_mono _ _ _ _ (sub_ul _ _ _ (sub_id _)) HAv)).
    destruct (IH1 D G n Sg L Hd HRA HLo HLE HLv HAv1 HG HGL HC)
      as (s & D' & n' & S2 & T0 & e' & Hst & Hsem & HT & HE & LvT & HRA' & Heq & HgHeq & HlHeq).
    exists s, D', n', S2, T0, e'.
    refine (conj Hst (conj Hsem (conj HT (conj HE (conj LvT (conj HRA' (conj _ (conj HgHeq HlHeq)))))))).
    eapply teqD_trans; [ exact Heq | exact Hteq ].
Qed.

(* The closed program: a derivation of a core program at the program judgment
   gives a run of the closed entry point from some fuel on, whose result is a
   principal type of the derivation's, and whose elaborated term erases to the
   program. *)
Theorem infer_complete_core_closed : forall e T, ctyping {} d_any nil e T ->
  exists D T' e' S2,
    Stable (fun f => infer_closed_elab f e = Some (D, T', e')) /\ erase e' = e /\
    Live PEv (ftv_typ T') D d_any S2 /\ rkres D d_any (sR S2) /\
    teqD d_any (apT S2 T') T /\ rf T'.
Proof.
  intros e T H.
  destruct (infer_complete_core {} d_any nil e T H d_any nil 0 sid {}
              (d_any_DOk 0) RA_d_any (fun a Ha => ltac:(exfalso; revert Ha; fsetdec)) LEv_empty
              (Live_empty _ _ _ _) (Avoid_empty _ _) (GOk_nil 0) (GLive_nil {}) (CI_nil d_any sid))
    as (s & D' & n' & S2 & T' & e' & St & Sem & HT & HE & LvT & HRA & Heq & HgHeq & HlHeq).
  exists D', T', e', S2.
  assert (St' : Stable (fun f => infer_closed_elab f e = Some (D', T', e'))).
  { eapply Stable_mono; [ | exact St ]. intros f Hf. unfold infer_closed_elab. rewrite Hf. rewrite dis_top_nil. cbv iota. rewrite apT_sid. reflexivity. }
  refine (conj St' (conj _ (conj LvT (conj (rkres_RA D' d_any (sR S2) HRA) (conj Heq (proj1 HT)))))).
  destruct St' as [f0 Hf0]. exact (proj2 (infer_closed_sound f0 e D' T' e' (Hf0 f0 (le_n f0)))).
Qed.

Lemma instP_mono : forall D T, PEv T -> instP D T (sch_mono T).
Proof.
  intros D T HP. exists idt, idr.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - intros a _. reflexivity.
  - intros r _. reflexivity.
  - symmetry. apply ap_typ_pointwise_id; reflexivity.
  - intros a Ha. simpl in Ha. fsetdec.
  - intros r Hr. simpl in Hr. fsetdec.
  - apply lc_sub_id.
  - intros a Ha. simpl in Ha. fsetdec.
  - intros r Hr. simpl in Hr. fsetdec.
Qed.

(* The identity function has the derivation at [Int -> Int]; the algorithm
   answers with a type of which that one is an instance. *)
Example core_identity : exists D T' e' S2,
  Stable (fun f => infer_closed_elab f (e_abs (e_fvar_b 0)) = Some (D, T', e')) /\
  erase e' = e_abs (e_fvar_b 0) /\ Live PEv (ftv_typ T') D d_any S2 /\ rkres D d_any (sR S2) /\
  teqD d_any (apT S2 T') (typ_Arrow typ_Int typ_Int) /\ rf T'.
Proof.
  apply infer_complete_core_closed.
  assert (HI : PEv typ_Int) by (apply PEv_scalar; left; reflexivity).
  apply C_Abs; [ exact HI | ]. intros x Hx. simpl.
  refine (C_Var _ _ _ _ (sch_mono typ_Int) typ_Int _ _ _ (instP_mono _ _ HI)); [ solve_uniq | apply binds_one_3; reflexivity | simpl; fsetdec ].
Qed.

(* A comparison, which unifies its operands and only then requires the joined
   type to be [Eq]. *)
Example core_comparison : exists D T' e' S2,
  Stable (fun f => infer_closed_elab f (e_abs (e_bin (e_fvar_b 0) bop_eq (e_fvar_b 0))) = Some (D, T', e')) /\
  erase e' = e_abs (e_bin (e_fvar_b 0) bop_eq (e_fvar_b 0)) /\
  Live PEv (ftv_typ T') D d_any S2 /\ rkres D d_any (sR S2) /\
  teqD d_any (apT S2 T') (typ_Arrow typ_Int typ_Bool) /\ rf T'.
Proof.
  apply infer_complete_core_closed.
  assert (HI : PEv typ_Int) by (apply PEv_scalar; left; reflexivity).
  apply C_Abs; [ exact HI | ]. intros x Hx. simpl.
  apply C_Cmp with (A := typ_Int); [ reflexivity | simpl; auto | exact HI | | ];
    (refine (C_Var _ _ _ _ (sch_mono typ_Int) typ_Int _ _ _ (instP_mono _ _ HI)); [ solve_uniq | apply binds_one_3; reflexivity | simpl; fsetdec ]).
Qed.
