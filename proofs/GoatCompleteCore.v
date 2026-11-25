(* Completeness of algorithm W, stage 7.7: the core constructs
   (docs/design/phase7-proof-plan.md).

   The derivations of the constructs whose types are base types, variables and
   arrows: variables, constants, [program], a call, [if], the operators, a
   comparison, [float(e)], and [let] (of a value, which generalizes, and of
   anything else, which does not).  The induction over them is
   [infer_complete_core] (GoatCompleteCoreW.v): a derivation [ctyping Av D1 G1 e
   T1] of one of them, a context [G] of the algorithm that [G1] is compared with
   ([CIT], GoatCompleteCtxT.v), live atoms [L] and a substitution [Sg] that
   respects the sorts on [L] ([Live PEv L D D1 Sg]) give a run of [infer] and a
   step [SemC] (GoatCompleteCtxW.v).

   [ctyping] follows the normal form of GoatCompleteNf.v ([ntyping]): each rule
   hands its premises the atoms of its own judgement and of its siblings' types
   ([bg]), and a [let] of a value generalizes atoms that are even and outside
   that set.  The induction carries the same set as [AvoidE]: the images of the
   live atoms stay inside it, so the premise of a generalizing [let], read at an
   environment that re-sorts the generalized atoms, sees the same sorts on
   everything the run holds live.  What a binder generalizes is dead afterwards:
   the body is compared with the live atoms that are not generalized
   ([gen_monoT], GoatCompleteMonoT.v).

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
Require Import Goat.GoatCompleteLiveRf.
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

(* A type of the record-free fragment has no entry to re-hold. *)
Lemma rh_rf : forall ps T m, rf T -> rh_t ps T m = (T, nil, m).
Proof.
  intros ps T. induction T; intros m H; cbn [rf] in H; try contradiction; try reflexivity.
  destruct H as [HA HB]. cbn [rh_t]. rewrite (IHT1 m HA), (IHT2 m HB). reflexivity.
Qed.

Lemma is_cmp_op_true : forall o, kind o = k_cmp -> is_cmp_op o = true.
Proof. intros o H. unfold is_cmp_op. rewrite H. reflexivity. Qed.

Lemma is_cmp_op_false : forall o, kind o <> k_cmp -> is_cmp_op o = false.
Proof. intros o H. unfold is_cmp_op. destruct (kind o); try reflexivity. contradiction. Qed.

Lemma EvT_scalar : forall c,
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) -> EvT c.
Proof. intros c Hc. exact (proj1 (PEv_scalar c Hc)). Qed.

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

(* ---- reading the derivation at another environment ---- *)

Lemma Live_env : forall L (D Dd Dg : denv) Sg, Live PEv L D Dd Sg ->
  (forall x, x `in` L -> forall c, c `in` ftv_typ (sT Sg x) -> Dg c = Dd c) ->
  (forall r, drk Dg r = drk Dd r) -> Live PEv L D Dg Sg.
Proof.
  intros L D Dd Dg Sg H Hs Hr a Ha. destruct (H a Ha) as [Hsat HP]. split; [ | exact HP ].
  eapply sat_loc; [ intros c Hc; exact (Hs a Ha c Hc) | intros r _; exact (Hr r) | exact Hsat ].
Qed.

(* A step read at the extended environment. *)
Lemma GOk_frv : forall n G, GOk n G -> forall r, r `notin` frv_ctx G.
Proof.
  intros n G H. induction H as [|[x s] G Hb _ IH]; intros r; simpl; [ fsetdec | ].
  destruct Hb as (_ & _ & Hrf & _). pose proof (IH r) as Hn.
  assert (Hs : r `notin` frv_sch s).
  { unfold frv_sch. intro Hr. apply AtomSetFacts.diff_iff in Hr. destruct Hr as [Hr _].
    exact (proj1 (proj2 (proj2 (rf_facts _ Hrf))) r Hr). }
  fsetdec.
Qed.

Lemma ats_arrow_eq : forall A B, ats (typ_Arrow A B) [=] ats A `union` ats B.
Proof. intros A B. unfold ats. simpl. fsetdec. Qed.

Lemma sub_ur : forall A B C : atoms, A [<=] C -> A [<=] B `union` C.
Proof. intros A B C H y Hy. apply AtomSetFacts.union_iff. right. exact (H y Hy). Qed.

Lemma ftv_sch_in_bg : forall X x s G T, ftv_sch s [<=] bg X ((x ~ s) ++ G) T.
Proof. intros X x s G T y Hy. unfold bg, atc. simpl. fsetdec. Qed.

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

Lemma own_sub_nil : forall d, own_sub d nil = sid.
Proof. reflexivity. Qed.
