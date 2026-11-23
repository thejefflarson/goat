(* Completeness of algorithm W, stage 7.7: the core constructs
   (docs/design/phase7-proof-plan.md).

   L3 for the constructs whose types are base types, variables and arrows:
   variables, constants, [program], a call, [if], the operators, a comparison
   and [float(e)].  A derivation [ctyping D1 G1 e T1] of one of them, a context
   [G] of the algorithm that [G1] instantiates ([CI]), and a substitution [Sg]
   that respects the sorts ([KR D D1 Sg]) give a run of [infer] that succeeds
   from some fuel on and a step [Sem] to the derivation's side: the extension
   [S2] of [Sg] to the variables the run made respects the sorts the run ends
   with, [Sg] factors through the run's substitution at [teqD D1], and the
   type the run returns is [teqD D1] to the derivation's under [S2].  The
   unifier's completeness on this fragment is [unify_tD_rf_complete]
   (GoatCompleteRf.v), which needs no hypothesis beyond the sorts.

   [let] and [letrec] are not here: they generalize, so the algorithm's context
   holds schemes, and the comparison of a scheme with the derivation's
   ([gen_mono_let], GoatCompleteLet.v) needs the derivation's substitutions to
   keep clear of the quantified atoms.  Here every binding is monomorphic, so
   the context relation is [teqD] of the instance of each type.

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
Require Import Goat.GoatInferW.
Require Import Goat.GoatInferSound.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatClose.
Require Import Goat.GoatElab.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteRf.
Require Import Goat.GoatCompleteRfRows.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- extending a substitution at one atom ---- *)

Definition supd (Sg : sub) (a : atom) (U : typ) : sub :=
  Sub (fun b => if Atom.eq_dec b a then U else sT Sg b) (sR Sg).

Lemma supd_same : forall Sg a U, sT (supd Sg a U) a = U.
Proof. intros. cbn [supd sT]. destruct (Atom.eq_dec a a); [ reflexivity | contradiction ]. Qed.

Lemma supd_other : forall Sg a U b, b <> a -> sT (supd Sg a U) b = sT Sg b.
Proof. intros. cbn [supd sT]. destruct (Atom.eq_dec b a); [ contradiction | reflexivity ]. Qed.

Lemma apT_Arrow : forall s A B, apT s (typ_Arrow A B) = typ_Arrow (apT s A) (apT s B).
Proof. reflexivity. Qed.

Lemma apT_Var : forall s a, apT s (typ_Var a) = sT s a.
Proof. reflexivity. Qed.

Lemma apT_supd : forall Sg a U T, rf T -> a `notin` ftv_typ T -> apT (supd Sg a U) T = apT Sg T.
Proof.
  intros Sg a U T. induction T; simpl; intros H Hn; try contradiction; try reflexivity.
  - destruct H as [H1 H2]. rewrite !apT_Arrow.
    rewrite (IHT1 H1 ltac:(fsetdec)), (IHT2 H2 ltac:(fsetdec)). reflexivity.
  - rewrite !apT_Var. rewrite supd_other by fsetdec. reflexivity.
Qed.

Lemma KR_supd : forall D D1 Sg a U, KR D D1 Sg -> sat D1 (D a) U -> KR D D1 (supd Sg a U).
Proof.
  intros D D1 Sg a U [Hk Hr] Hs. split.
  - intros b. cbn [supd sT]. destruct (Atom.eq_dec b a) as [->|_]; [ exact Hs | exact (Hk b) ].
  - exact Hr.
Qed.

(* ---- record-free types over atoms below a supply ---- *)

Definition TOk (n : nat) (T : typ) : Prop :=
  rf T /\ forall a, a `in` ftv_typ T -> old n a.

Lemma TOk_mono : forall n n' T, n <= n' -> TOk n T -> TOk n' T.
Proof. intros n n' T Hl [H1 H2]. split; [ exact H1 | intros a Ha; exact (old_le _ _ _ Hl (H2 a Ha)) ]. Qed.

Lemma TOk_var : forall n a, old n a -> TOk n (typ_Var a).
Proof.
  intros n a Ha. split; [ exact I | intros b Hb; simpl in Hb;
    apply AtomSetFacts.singleton_iff in Hb; subst; exact Ha ].
Qed.

Lemma TOk_arrow : forall n A B, TOk n A -> TOk n B -> TOk n (typ_Arrow A B).
Proof.
  intros n A B [A1 A2] [B1 B2]. split; [ exact (conj A1 B1) | ].
  intros a Ha. simpl in Ha. apply AtomSetFacts.union_iff in Ha.
  destruct Ha as [Ha|Ha]; [ exact (A2 a Ha) | exact (B2 a Ha) ].
Qed.

Lemma TOk_arrow_inv : forall n A B, TOk n (typ_Arrow A B) -> TOk n A /\ TOk n B.
Proof.
  intros n A B [[A1 B1] H]. split; split; try assumption;
    intros a Ha; apply H; simpl; apply AtomSetFacts.union_iff; [ left | right ]; exact Ha.
Qed.

Lemma TOk_scalar : forall n c,
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) -> TOk n c.
Proof.
  intros n c Hc. split.
  - destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; exact I.
  - intros a Ha. destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; simpl in Ha; fsetdec.
Qed.

Lemma TOk_ap : forall n n' s T, SI n n' s -> TOk n T -> TOk n' (apT s T).
Proof.
  intros n n' s T (Hl & Hx & _) [H1 H2]. split.
  - apply rf_ap; [ exact H1 | intros x Hxi; exact (proj1 (Hx x (H2 x Hxi))) ].
  - intros y Hy. destruct (ftv_ap_rf s T y H1 Hy) as (x & Hxi & Hyx).
    exact (proj2 (Hx x (H2 x Hxi)) y Hyx).
Qed.

(* ---- steps ---- *)

Lemma SI_weaken : forall n0 n1 n' s, n0 <= n1 -> SI n1 n' s -> SI n0 n' s.
Proof.
  intros n0 n1 n' s Hl (Hl1 & Hx & Hr). split; [ lia | split ].
  - intros x Hx0. exact (Hx x (old_le _ _ _ Hl Hx0)).
  - intros q Hq. exact (Hr q (old_le _ _ _ Hl Hq)).
Qed.

Lemma SI_id_le : forall n n', n <= n' -> SI n n' sid.
Proof.
  intros n n' Hl. split; [ exact Hl | split; intros x Hx; [ | reflexivity ] ].
  cbn [sT sid idt]. split; [ exact I | ].
  intros y Hy. simpl in Hy. apply AtomSetFacts.singleton_iff in Hy. subst. exact (old_le _ _ _ Hl Hx).
Qed.

(* A step from a substitution that agrees with [Sg] on the atoms below a smaller
   supply is a step from [Sg]. *)
Lemma Sem_weaken : forall DT Sg Sg' n0 n1 s D' n' S2,
  n0 <= n1 -> Sem DT Sg' n1 s D' n' S2 ->
  (forall x, old n0 x -> sT Sg' x = sT Sg x) -> (forall q, old n0 q -> sR Sg' q = sR Sg q) ->
  Sem DT Sg n0 s D' n' S2.
Proof.
  intros DT Sg Sg' n0 n1 s D' n' S2 Hl (HK & Hd & HI & Hx & Hr) Ex Er.
  refine (conj HK (conj Hd (conj (SI_weaken _ _ _ _ Hl HI) (conj _ _)))).
  - intros x Hx0. rewrite <- (Ex x Hx0). exact (Hx x (old_le _ _ _ Hl Hx0)).
  - intros q Hq. rewrite <- (Er q Hq). exact (Hr q (old_le _ _ _ Hl Hq)).
Qed.

Lemma Sem_supd : forall DT Sg U n s D' n' S2,
  Sem DT (supd Sg (ea n) U) (S n) s D' n' S2 -> Sem DT Sg n s D' n' S2.
Proof.
  intros DT Sg U n s D' n' S2 H. refine (Sem_weaken DT Sg (supd Sg (ea n) U) n (S n) s D' n' S2 _ H _ _).
  - lia.
  - intros x Hx. apply supd_other. intro E. exact (Hx n (le_n n) E).
  - intros q _. reflexivity.
Qed.

Lemma Sem_comp : forall DT Sg n s D1 n1 S1 s' D2 n2 S2,
  Sem DT Sg n s D1 n1 S1 -> Sem DT S1 n1 s' D2 n2 S2 ->
  Sem DT Sg n (scomp s' s) D2 n2 S2.
Proof.
  intros DT Sg n s D1 n1 S1 s' D2 n2 S2 (K1 & Hd1 & I1 & F1 & R1) (K2 & Hd2 & I2 & F2 & R2).
  refine (conj K2 (conj Hd2 (conj (SI_comp _ _ _ _ _ I1 I2) (conj _ _)))).
  - intros x Hx. eapply teqD_trans; [ exact (F1 x Hx) | ].
    pose proof (proj1 (proj2 I1) x Hx) as [Hrf Hold].
    change (teqD DT (apT S1 (sT s x)) (apT S2 (apT s' (sT s x)))).
    apply ap_factor_rf; [ exact Hrf | intros z Hz; exact (F2 z (Hold z Hz)) ].
  - intros q Hq. rewrite (R2 q (old_le _ _ _ (proj1 I1) Hq)). exact (R1 q Hq).
Qed.

(* ---- the contexts ---- *)

(* Every binding of the algorithm's context is a record-free type over atoms
   below the supply. *)
Definition GOk (n : nat) (G : ctx) : Prop :=
  Forall (fun b => exists T, snd b = sch_mono T /\ TOk n T) G.

(* The derivation's context holds, at each name, the type that the algorithm's
   is under [Sg], up to [teqD]. *)
Definition CI (D1 : denv) (Sg : sub) (G1 G : ctx) : Prop :=
  Forall2 (fun b1 b => fst b1 = fst b /\
     exists T1 T, snd b1 = sch_mono T1 /\ snd b = sch_mono T /\ teqD D1 (apT Sg T) T1) G1 G.

Lemma GOk_nil : forall n, GOk n nil.
Proof. intros n. constructor. Qed.

Lemma GOk_cons : forall n x T G, TOk n T -> GOk n G -> GOk n ((x ~ sch_mono T) ++ G).
Proof. intros n x T G HT HG. constructor; [ exists T; split; [ reflexivity | exact HT ] | exact HG ]. Qed.

Lemma GOk_mono : forall n n' G, n <= n' -> GOk n G -> GOk n' G.
Proof.
  intros n n' G Hl H. induction H as [|b G [T [E HT]] _ IH]; constructor.
  - exists T. split; [ exact E | exact (TOk_mono _ _ _ Hl HT) ].
  - exact IH.
Qed.

Lemma apS_mono : forall s T, apS s (sch_mono T) = sch_mono (apT s T).
Proof. reflexivity. Qed.

Lemma GOk_apC : forall n n' s G, SI n n' s -> GOk n G -> GOk n' (apC s G).
Proof.
  intros n n' s G HI H. rewrite apC_map. induction H as [|[y sc] G [T [E HT]] _ IH]; simpl in *.
  - constructor.
  - constructor; [ | exact IH ].
    simpl in E. subst sc. exists (apT s T). split; [ reflexivity | exact (TOk_ap _ _ _ _ HI HT) ].
Qed.

Lemma CI_nil : forall D1 Sg, CI D1 Sg nil nil.
Proof. intros. constructor. Qed.

Lemma CI_cons : forall D1 Sg G1 G x T1 T,
  CI D1 Sg G1 G -> teqD D1 (apT Sg T) T1 ->
  CI D1 Sg ((x ~ sch_mono T1) ++ G1) ((x ~ sch_mono T) ++ G).
Proof.
  intros D1 Sg G1 G x T1 T H Ht. constructor; [ | exact H ].
  simpl. split; [ reflexivity | exists T1, T; repeat split; exact Ht ].
Qed.

Lemma CI_dom : forall D1 Sg G1 G, CI D1 Sg G1 G -> dom G1 [=] dom G.
Proof.
  intros D1 Sg G1 G H. induction H as [|[x s1] [y s] G1 G [Hk _] _ IH]; simpl in *; [ reflexivity | ].
  subst y. rewrite IH. reflexivity.
Qed.

(* The substitution may change at an atom no type of the context mentions. *)
Lemma CI_supd : forall D1 Sg G1 G n U,
  CI D1 Sg G1 G -> GOk n G -> CI D1 (supd Sg (ea n) U) G1 G.
Proof.
  intros D1 Sg G1 G n U H. induction H as [|[x s1] [y s] G1 G [Hk [T1 [T [E1 [E2 Ht]]]]] _ IH]; intros HG.
  - constructor.
  - inversion HG as [|b G' [T' [E' [HT' HTa]]] HG' Eb]; subst. simpl in *. subst y.
    constructor; [ | exact (IH HG') ].
    simpl. split; [ reflexivity | ]. exists T1, T. repeat split; try assumption.
    rewrite E' in E2. injection E2 as <-.
    rewrite (apT_supd Sg (ea n) U _ HT' (fun Hin => HTa _ Hin n (le_n n) eq_refl)). exact Ht.
Qed.

(* A step: the context the algorithm continues with is the old one under the
   step's substitution, which the derivation's substitution follows. *)
Lemma CI_step : forall DT Sg n s D' n' S2 G1 G,
  Sem DT Sg n s D' n' S2 -> CI DT Sg G1 G -> GOk n G ->
  CI DT S2 G1 (apC s G) /\ GOk n' (apC s G).
Proof.
  intros DT Sg n s D' n' S2 G1 G Hs HC HG. split.
  - destruct Hs as (K & Hd & HI & F & R). rewrite apC_map.
    revert HG. induction HC as [|[x s1] [y sc] G1 G [Hk [T1 [T [E1 [E2 Ht]]]]] _ IH]; intros HG.
    + constructor.
    + inversion HG as [|b G' [T' [E' [HT' HTa]]] HG' Eb]; subst. simpl in *. subst y.
      constructor; [ | exact (IH HG') ].
      simpl. split; [ reflexivity | ]. try subst sc; apply (f_equal s_body) in E'; cbn [sch_mono s_body] in E'; subst T'. exists T1, (apT s T).
      split; [ exact E1 | split; [ reflexivity | ] ].
      eapply teqD_trans; [ | exact Ht ]. apply teqD_sym.
      apply ap_factor_rf; [ exact HT' | intros z Hz; exact (F z (HTa z Hz)) ].
  - exact (GOk_apC _ _ _ _ (proj1 (proj2 (proj2 Hs))) HG).
Qed.

Lemma CI_lookup : forall D1 Sg G1 G x sc1,
  CI D1 Sg G1 G -> uniq G1 -> binds x sc1 G1 ->
  exists T1 T, sc1 = sch_mono T1 /\ lookup x G = Some (sch_mono T) /\ teqD D1 (apT Sg T) T1.
Proof.
  intros D1 Sg G1 G x sc1 H. induction H as [|[y s1] [z sc] G1 G [Hk [T1 [T [E1 [E2 Ht]]]]] _ IH]; intros Hu Hb.
  - inversion Hb.
  - simpl in *. subst z. apply binds_cons_1 in Hb. destruct Hb as [[Hxy Hs]|Hb].
    + subst x sc1. exists T1, T. split; [ exact E1 | ]. split; [ | exact Ht ].
      cbn [lookup]. destruct (Atom.eq_dec y y); [ rewrite E2; reflexivity | contradiction ].
    + inversion Hu; subst.
      destruct (IH ltac:(assumption) Hb) as (T1' & T' & Ea & Eb & Hc). exists T1', T'.
      split; [ exact Ea | ]. split; [ | exact Hc ].
      cbn [lookup]. destruct (Atom.eq_dec x y) as [->|_]; [ | exact Eb ].
      exfalso. apply binds_In in Hb. contradiction.
Qed.


(* ---- the derivations of the core constructs ---- *)

(* [typing] restricted to the constructs here, with a binder's premise at every
   name fresh for the context and the term (the algorithm opens a binder at the
   one name it chose), the context's bindings monomorphic, and the operators of
   one numeric sort.  The record division of [sig_quot_rec] is not here: the
   algorithm unifies the operands of [/] with [Float]. *)
Inductive ctyping : denv -> ctx -> exp -> typ -> Prop :=
  | C_Var : forall Dd Gd x T,
      uniq Gd -> binds x (sch_mono T) Gd -> ctyping Dd Gd (e_fvar_f x) T
  | C_Num : forall Dd Gd i T, uniq Gd -> sat Dd k_Literal T -> ctyping Dd Gd (e_num i) T
  | C_Dec : forall Dd Gd d, uniq Gd -> ctyping Dd Gd (e_dec d) typ_Float
  | C_True : forall Dd Gd, uniq Gd -> ctyping Dd Gd e_true typ_Bool
  | C_False : forall Dd Gd, uniq Gd -> ctyping Dd Gd e_false typ_Bool
  | C_Unit : forall Dd Gd, uniq Gd -> ctyping Dd Gd e_unit typ_Unit
  | C_Str : forall Dd Gd q, uniq Gd -> ctyping Dd Gd (e_str q) typ_String
  | C_Abs : forall Dd Gd e T1 T2,
      (forall x, x `notin` dom Gd `union` fv_exp e ->
         ctyping Dd ((x ~ sch_mono T1) ++ Gd) (open_exp_wrt_exp e (e_fvar_f x)) T2) ->
      ctyping Dd Gd (e_abs e) (typ_Arrow T1 T2)
  | C_App : forall Dd Gd e1 e2 T1 T2,
      ctyping Dd Gd e1 (typ_Arrow T1 T2) -> ctyping Dd Gd e2 T1 ->
      ctyping Dd Gd (e_app e1 e2) T2
  | C_If : forall Dd Gd e1 e2 e3 T,
      ctyping Dd Gd e1 typ_Bool -> ctyping Dd Gd e2 T -> ctyping Dd Gd e3 T ->
      ctyping Dd Gd (e_ite e1 e2 e3) T
  | C_ToFloat : forall Dd Gd e A,
      ctyping Dd Gd e A -> sat Dd k_Literal A -> ctyping Dd Gd (e_tofloat e) typ_Float
  | C_Arith : forall Dd Gd e1 o e2 A,
      kind o <> k_cmp -> kind o <> k_quot -> sat Dd k_Numeric A ->
      ctyping Dd Gd e1 A -> ctyping Dd Gd e2 A -> ctyping Dd Gd (e_bin e1 o e2) A
  | C_Quot : forall Dd Gd e1 e2,
      ctyping Dd Gd e1 typ_Float -> ctyping Dd Gd e2 typ_Float ->
      ctyping Dd Gd (e_bin e1 bop_div e2) typ_Float
  | C_Cmp : forall Dd Gd e1 o e2 A,
      kind o = k_cmp -> sat Dd k_Eq A ->
      ctyping Dd Gd e1 A -> ctyping Dd Gd e2 A -> ctyping Dd Gd (e_bin e1 o e2) typ_Bool
  | C_LetMono : forall Dd Gd e1 e2 T1 T2,
      is_gen_value e1 = false -> ctyping Dd Gd e1 T1 ->
      (forall x, x `notin` dom Gd `union` fv_exp e2 ->
         ctyping Dd ((x ~ sch_mono T1) ++ Gd) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
      ctyping Dd Gd (e_let e1 e2) T2
  | C_Conv : forall Dd Gd e T T',
      ctyping Dd Gd e T -> teqD Dd T T' -> ctyping Dd Gd e T'.

Theorem ctyping_typing : forall D G e T, ctyping D G e T -> typing D G e T.
Proof.
  intros D G e T H. induction H.
  - eapply T_Var; [ exact H | exact H0 | apply inst_mono_self ].
  - apply T_Num; assumption.
  - apply T_Dec; assumption.
  - apply T_True; assumption.
  - apply T_False; assumption.
  - apply T_Unit; assumption.
  - apply T_Str; assumption.
  - apply T_Abs with (L := dom Gd `union` fv_exp e). exact H0.
  - eapply T_App; eassumption.
  - apply T_If; assumption.
  - eapply T_ToFloat; eassumption.
  - eapply T_Bin; [ exact IHctyping1 | exact IHctyping2 | ].
    destruct (kind o) eqn:Ek; try contradiction;
      [ apply sig_ring | apply sig_whole ]; assumption.
  - apply (T_Bin Dd Gd e1 bop_div e2 typ_Float typ_Float typ_Float); [ assumption | assumption | apply sig_quot ].
  - eapply T_Bin; [ exact IHctyping1 | exact IHctyping2 | ].
    apply sig_cmp; assumption.
  - apply T_LetMono with (L := dom Gd `union` fv_exp e2) (T1 := T1); [ exact IHctyping | exact H2 ].
  - eapply T_ConvD; eassumption.
Qed.

(* ---- what each case of the induction uses ---- *)

Lemma GOk_lookup : forall n G x T, GOk n G -> lookup x G = Some (sch_mono T) -> TOk n T.
Proof.
  intros n G x T H. induction H as [|[y sc] G [T0 [E HT]] _ IH]; intros Hl; [ discriminate Hl | ].
  cbn [lookup] in Hl. destruct (Atom.eq_dec x y) as [_|_].
  - cbn [snd] in E. subst sc. injection Hl as Hl. subst T0. exact HT.
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

Lemma unify_step : forall DT D Sg T1 T2 n,
  DOk D n -> KR D DT Sg -> TOk n T1 -> TOk n T2 -> teqD DT (apT Sg T1) (apT Sg T2) ->
  exists s D' n' S2,
    Stable (fun f => unify_coD f D T1 T2 n = Some (s, D', nil, n')) /\ Sem DT Sg n s D' n' S2.
Proof.
  intros DT D Sg T1 T2 n Hd HK [R1 A1] [R2 A2] Heq.
  destruct (unify_tD_rf_complete DT D Sg T1 T2 n Hd HK R1 R2 A1 A2 Heq)
    as (s & D' & n' & S2 & [f0 Hf0] & Hsem).
  exists s, D', n', S2. split; [ | exact Hsem ].
  exact (unify_coD_stable f0 D T1 T2 n s D' n' (Hf0 f0 (le_n f0))).
Qed.

Lemma KR_supd_upd : forall D D1 Sg n k U,
  KR D D1 Sg -> DOk D n -> sat D1 k U ->
  KR (upd D (ea n) k) D1 (supd Sg (ea n) U).
Proof.
  intros D D1 Sg n k U [Hk Hr] Hd Hs. split.
  - intros b. cbn [supd sT]. destruct (Atom.eq_dec b (ea n)) as [->|Hne].
    + rewrite upd_same. exact Hs.
    + rewrite upd_other by exact Hne. exact (Hk b).
  - intros r. exact (Hr r).
Qed.

(* A fresh variable of sort [k], sent to [U]. *)
Lemma sem_fresh : forall DT D Sg n k U,
  DOk D n -> KR D DT Sg -> sat DT k U ->
  Sem DT Sg n sid (upd D (ea n) k) (S n) (supd Sg (ea n) U).
Proof.
  intros DT D Sg n k U Hd HK Hs.
  refine (conj (KR_supd_upd D DT Sg n k U HK Hd Hs) (conj (DOk_upd D n k Hd)
    (conj (SI_id_le n (S n) (Nat.le_succ_diag_r n)) (conj _ _)))).
  - intros x Hx. cbn [sid sT idt]. change (teqD DT (sT Sg x) (sT (supd Sg (ea n) U) x)).
    rewrite supd_other by (intro E; exact (Hx n (le_n n) E)). apply teqD_refl.
  - intros q _. reflexivity.
Qed.

Lemma generic_sort_arith : forall o, kind o <> k_cmp -> generic_sort o = k_Numeric.
Proof. intros o H. unfold generic_sort. destruct (kind o); [ reflexivity | reflexivity | reflexivity | contradiction ]. Qed.

Lemma is_cmp_op_true : forall o, kind o = k_cmp -> is_cmp_op o = true.
Proof. intros o H. unfold is_cmp_op. rewrite H. reflexivity. Qed.

Lemma is_cmp_op_false : forall o, kind o <> k_cmp -> is_cmp_op o = false.
Proof. intros o H. unfold is_cmp_op. destruct (kind o); try reflexivity. contradiction. Qed.

Lemma is_generic_op_true : forall o, kind o <> k_quot -> is_generic_op o = true.
Proof. intros o H. unfold is_generic_op. destruct (kind o); try reflexivity. contradiction. Qed.

(* What a run ends with. *)
Definition Done (D1 : denv) (G : ctx) (e : exp) (D : denv) (n : nat) (Sg : sub) (T1 : typ) : Prop :=
  exists s D' n' S2 T e',
    Stable (fun f => infer f D G e n = Some (s, D', T, n', e')) /\
    Sem D1 Sg n s D' n' S2 /\ TOk n' T /\ teqD D1 (apT S2 T) T1 /\ is_gen_value e' = is_gen_value e.

Lemma Done_const : forall D1 G e D n Sg T1 c,
  (forall f, infer (S f) D G e n = Some (sid, D, c, n, e)) ->
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) ->
  DOk D n -> KR D D1 Sg -> teqD D1 c T1 -> Done D1 G e D n Sg T1.
Proof.
  intros D1 G e D n Sg T1 c Hi Hc Hd HK Hteq.
  exists sid, D, n, Sg, c, e. refine (conj _ (conj (Sem_id D1 Sg D n HK Hd) (conj (TOk_scalar n c Hc) (conj _ eq_refl)))).
  - exists 1. intros f Hf. destruct f as [|f]; [ lia | exact (Hi f) ].
  - destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; exact Hteq.
Qed.

(* ---- the induction ---- *)

Lemma Sem_KR : forall DT Sg n s D' n' S2, Sem DT Sg n s D' n' S2 -> KR D' DT S2.
Proof. intros DT Sg n s D' n' S2 H. exact (proj1 H). Qed.

Lemma Sem_DOk : forall DT Sg n s D' n' S2, Sem DT Sg n s D' n' S2 -> DOk D' n'.
Proof. intros DT Sg n s D' n' S2 H. exact (proj1 (proj2 H)). Qed.

Lemma Sem_SI : forall DT Sg n s D' n' S2, Sem DT Sg n s D' n' S2 -> SI n n' s.
Proof. intros DT Sg n s D' n' S2 H. exact (proj1 (proj2 (proj2 H))). Qed.

Lemma Sem_F : forall DT Sg n s D' n' S2, Sem DT Sg n s D' n' S2 ->
  forall x, old n x -> teqD DT (sT Sg x) (apT S2 (sT s x)).
Proof. intros DT Sg n s D' n' S2 H. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.

Arguments Sem_KR {DT Sg n s D' n' S2} H.
Arguments Sem_DOk {DT Sg n s D' n' S2} H.
Arguments Sem_SI {DT Sg n s D' n' S2} H.
Arguments Sem_F {DT Sg n s D' n' S2} H x _.

Lemma bin_res_arith : forall o A, kind o <> k_cmp -> bin_res o A = A.
Proof. intros o A H. unfold bin_res. destruct (kind o); try reflexivity. contradiction. Qed.

Ltac stable_run H :=
  eapply Stable_mono; [ | exact H ];
  intros [|f] Hf; [ contradiction | ].

Theorem infer_complete_core : forall D1 G1 e T1, ctyping D1 G1 e T1 ->
  forall D G n Sg, DOk D n -> KR D D1 Sg -> GOk n G -> CI D1 Sg G1 G ->
  Done D1 G e D n Sg T1.
Proof.
  intros Dd Gd e T1 H. induction H; intros D G n Sg Hd HK HG HC.
  - (* variable *)
    destruct (CI_lookup Dd Sg Gd G x (sch_mono T) HC H H0) as (T1' & T' & Ea & Eb & Hc).
    assert (ET : T = T1') by (apply (f_equal s_body) in Ea; exact Ea). subst T1'.
    exists sid, D, n, Sg, T', (e_fvar_f x). refine (conj _ (conj (Sem_id Dd Sg D n HK Hd) (conj _ (conj Hc eq_refl)))).
    + exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
      cbn [infer]. rewrite Eb, instantiate_mono. reflexivity.
    + exact (GOk_lookup n G x T' HG Eb).
  - (* numeral *)
    exists sid, (upd D (ea n) k_Literal), (S n), (supd Sg (ea n) T), (typ_Var (ea n)), (e_num i).
    refine (conj _ (conj (sem_fresh Dd D Sg n k_Literal T Hd HK H0) (conj _ (conj _ _)))).
    + exists 1. intros f Hf. destruct f as [|f]; [ lia | reflexivity ].
    + apply TOk_var. apply old_ea. lia.
    + rewrite apT_Var, supd_same. apply teqD_refl.
    + reflexivity.
  - (* float literal *)
    apply (Done_const Dd G (e_dec d) D n Sg typ_Float typ_Float); try assumption;
      [ intros f; reflexivity | right; left; reflexivity | apply teqD_refl ].
  - apply (Done_const Dd G e_true D n Sg typ_Bool typ_Bool); try assumption;
      [ intros f; reflexivity | right; right; left; reflexivity | apply teqD_refl ].
  - apply (Done_const Dd G e_false D n Sg typ_Bool typ_Bool); try assumption;
      [ intros f; reflexivity | right; right; left; reflexivity | apply teqD_refl ].
  - apply (Done_const Dd G e_unit D n Sg typ_Unit typ_Unit); try assumption;
      [ intros f; reflexivity | right; right; right; left; reflexivity | apply teqD_refl ].
  - apply (Done_const Dd G (e_str q) D n Sg typ_String typ_String); try assumption;
      [ intros f; reflexivity | right; right; right; right; reflexivity | apply teqD_refl ].
  - (* program *)
    rename e into b. rename H0 into IH.
    set (x := fresh_var G b).
    assert (Hx : x `notin` dom Gd `union` fv_exp b).
    { rewrite (CI_dom _ _ _ _ HC). pose proof (fresh_var_notin_dom G b). pose proof (fresh_var_notin_fv G b).
      fsetdec. }
    set (Sg' := supd Sg (ea n) T1).
    assert (Hsat : sat Dd (D (ea n)) T1) by (rewrite (DOk_ea D n n Hd (le_n n)); apply sat_any).
    assert (HTb : TOk (S n) (typ_Var (ea n))) by (apply TOk_var; apply old_ea; lia).
    destruct (IH x Hx (D) ((x ~ sch_mono (typ_Var (ea n))) ++ G) (S n) Sg'
                (DOk_mono D n (S n) Hd (Nat.le_succ_diag_r n)) (KR_supd D Dd Sg (ea n) T1 HK Hsat)
                (GOk_cons (S n) x _ G HTb (GOk_mono n (S n) G (Nat.le_succ_diag_r n) HG))
                (CI_cons Dd Sg' Gd G x T1 _ (CI_supd Dd Sg Gd G n T1 HC HG)
                   ltac:(unfold Sg'; rewrite apT_Var, supd_same; apply teqD_refl)))
      as (s & D' & n' & S2 & T & e' & Hst & Hsem & HT & Heq & HgHeq).
    exists s, D', n', S2, (typ_Arrow (apT s (typ_Var (ea n))) T), (e_abs (cl 0 x e')).
    pose proof (Sem_supd Dd Sg T1 n s D' n' S2 Hsem) as Hsem0.
    refine (conj _ (conj Hsem0 (conj _ (conj _ _)))).
    + pose proof (Stable_below _ Hst) as HSt. stable_run HSt.
      cbn [infer]. change (fresh_var G b) with x. rewrite Hf. reflexivity.
    + apply TOk_arrow; [ exact (TOk_ap _ _ _ _ (proj1 (proj2 (proj2 Hsem))) HTb) | exact HT ].
    + rewrite apT_Arrow. apply teqD_Arrow; [ | exact Heq ].
      pose proof (proj1 (proj2 (proj2 (proj2 Hsem))) (ea n) (old_ea (S n) n (Nat.lt_succ_diag_r n))) as F.
      unfold Sg' in F. rewrite supd_same in F. apply teqD_sym. exact F.
    + reflexivity.
  - (* call *)
    destruct (IHctyping1 D G n Sg Hd HK HG HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & Heq1 & HgHeq1).
    destruct (CI_step _ _ _ _ _ _ _ _ _ Sem1 HC HG) as [HC1 HG1].
    destruct (IHctyping2 D1a (apC s1 G) n1 Sa (Sem_DOk Sem1) (Sem_KR Sem1) HG1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & Heq2 & HgHeq2).
    pose proof (Sem_DOk Sem2) as Hd2.
    pose proof (TOk_ap _ _ _ _ (Sem_SI Sem2) HTa) as HTa2.
    assert (Hle : n2 <= S n2) by lia.
    assert (HTv : TOk (S n2) (typ_Var (ea n2))) by (apply TOk_var; apply old_ea; lia).
    assert (HTarr : TOk (S n2) (typ_Arrow Tb (typ_Var (ea n2))))
      by (apply TOk_arrow; [ exact (TOk_mono _ _ _ Hle HTb) | exact HTv ]).
    assert (HK3 : KR D2 Dd (supd Sb (ea n2) T2)).
    { apply KR_supd; [ exact (Sem_KR Sem2) | ]. rewrite (DOk_ea D2 n2 n2 Hd2 (le_n n2)). apply sat_any. }
    assert (Heq : teqD Dd (apT (supd Sb (ea n2) T2) (apT s2 Ta))
                          (apT (supd Sb (ea n2) T2) (typ_Arrow Tb (typ_Var (ea n2))))).
    { rewrite (apT_supd Sb (ea n2) T2 _ (proj1 HTa2) (fun Hin => proj2 HTa2 _ Hin n2 (le_n n2) eq_refl)).
      rewrite apT_Arrow, (apT_supd Sb (ea n2) T2 Tb (proj1 HTb) (fun Hin => proj2 HTb _ Hin n2 (le_n n2) eq_refl)),
        apT_Var, supd_same.
      eapply teqD_trans; [ apply teqD_sym; apply ap_factor_rf;
        [ exact (proj1 HTa) | intros z Hz; exact (Sem_F Sem2 z (proj2 HTa z Hz)) ] | ].
      eapply teqD_trans; [ exact Heq1 | ]. apply teqD_Arrow; [ apply teqD_sym; exact Heq2 | apply teqD_refl ]. }
    destruct (unify_step Dd D2 _ _ _ (S n2) (DOk_mono D2 n2 (S n2) Hd2 Hle) HK3
                (TOk_mono _ _ _ Hle HTa2) HTarr Heq) as (s3 & D3 & n3 & S3 & St3 & Sem3).
    pose proof (Sem_supd Dd Sb T2 n2 s3 D3 n3 S3 Sem3) as Sem3'.
    exists (scomp s3 (scomp s2 s1)), D3, n3, S3, (apT s3 (typ_Var (ea n2))), (e_app e1' e2').
    refine (conj _ (conj (Sem_comp _ _ _ _ _ _ _ _ _ _ _ (Sem_comp _ _ _ _ _ _ _ _ _ _ _ Sem1 Sem2) Sem3') (conj _ (conj _ _)))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 St3))) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2 & E3). cbn [infer]. rewrite E1, E2, E3. reflexivity.
    + exact (TOk_ap _ _ _ _ (Sem_SI Sem3) HTv).
    + pose proof (Sem_F Sem3 (ea n2) (old_ea (S n2) n2 (Nat.lt_succ_diag_r n2))) as F.
      rewrite supd_same in F. apply teqD_sym. exact F.
    + cbn [is_gen_value]; try reflexivity; try assumption.
  - (* if *)
    destruct (IHctyping1 D G n Sg Hd HK HG HC)
      as (s1 & D1a & n1 & Sa & Tc & c' & St1 & Sem1 & HTc & Heq1 & HgHeq1).
    destruct (CI_step _ _ _ _ _ _ _ _ _ Sem1 HC HG) as [HC1 HG1].
    destruct (unify_step Dd D1a Sa Tc typ_Bool n1 (Sem_DOk Sem1) (Sem_KR Sem1) HTc
                (TOk_scalar _ _ (or_intror (or_intror (or_introl eq_refl)))) Heq1)
      as (s2 & D1b & n2 & Sb & St2 & Sem2).
    destruct (CI_step _ _ _ _ _ _ _ _ _ Sem2 HC1 HG1) as [HC2 HG2].
    destruct (IHctyping2 D1b (apC s2 (apC s1 G)) n2 Sb (Sem_DOk Sem2) (Sem_KR Sem2) HG2 HC2)
      as (s3 & D3 & n3 & Sc & Ta & a' & St3 & Sem3 & HTa & Heq2 & HgHeq2).
    destruct (CI_step _ _ _ _ _ _ _ _ _ Sem3 HC2 HG2) as [HC3 HG3].
    destruct (IHctyping3 D3 (apC s3 (apC s2 (apC s1 G))) n3 Sc (Sem_DOk Sem3) (Sem_KR Sem3) HG3 HC3)
      as (s4 & D4 & n4 & Sd & Tb & b' & St4 & Sem4 & HTb & Heq3 & HgHeq3).
    pose proof (TOk_ap _ _ _ _ (Sem_SI Sem4) HTa) as HTa4.
    assert (Heq : teqD Dd (apT Sd (apT s4 Ta)) (apT Sd Tb)).
    { eapply teqD_trans; [ apply teqD_sym; apply ap_factor_rf;
        [ exact (proj1 HTa) | intros z Hz; exact (Sem_F Sem4 z (proj2 HTa z Hz)) ] | ].
      eapply teqD_trans; [ exact Heq2 | apply teqD_sym; exact Heq3 ]. }
    destruct (unify_step Dd D4 Sd _ _ n4 (Sem_DOk Sem4) (Sem_KR Sem4) HTa4 HTb Heq)
      as (s5 & D5 & n5 & Se & St5 & Sem5).
    exists (scomp s5 (scomp s4 (scomp s3 (scomp s2 s1)))), D5, n5, Se, (apT s5 Tb), (e_ite c' a' b').
    refine (conj _ (conj (Sem_comp _ _ _ _ _ _ _ _ _ _ _
      (Sem_comp _ _ _ _ _ _ _ _ _ _ _ (Sem_comp _ _ _ _ _ _ _ _ _ _ _ (Sem_comp _ _ _ _ _ _ _ _ _ _ _ Sem1 Sem2) Sem3) Sem4)
      Sem5) (conj _ (conj _ _)))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3
        (Stable_and _ _ St4 St5))))) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2 & E3 & E4 & E5). cbn [infer]. rewrite E1, E2, E3, E4, E5. reflexivity.
    + exact (TOk_ap _ _ _ _ (Sem_SI Sem5) HTb).
    + eapply teqD_trans; [ apply teqD_sym; apply ap_factor_rf;
        [ exact (proj1 HTb) | intros z Hz; exact (Sem_F Sem5 z (proj2 HTb z Hz)) ] | ].
      exact Heq3.
    + cbn [is_gen_value]; try reflexivity; try assumption.
  - (* float(e) *)
    destruct (IHctyping D G n Sg Hd HK HG HC)
      as (s1 & D1a & n1 & Sa & Ta & e' & St1 & Sem1 & HTa & Heq1 & HgHeq1).
    assert (Hle : n1 <= S n1) by lia.
    assert (HTv : TOk (S n1) (typ_Var (ea n1))) by (apply TOk_var; apply old_ea; lia).
    assert (Heq : teqD Dd (apT (supd Sa (ea n1) A) Ta) (apT (supd Sa (ea n1) A) (typ_Var (ea n1)))).
    { rewrite (apT_supd Sa (ea n1) A Ta (proj1 HTa) (fun Hin => proj2 HTa _ Hin n1 (le_n n1) eq_refl)),
        apT_Var, supd_same. exact Heq1. }
    destruct (unify_step Dd (upd D1a (ea n1) k_Literal) _ _ _ (S n1) (DOk_upd D1a n1 k_Literal (Sem_DOk Sem1))
                (KR_supd_upd D1a Dd Sa n1 k_Literal A (Sem_KR Sem1) (Sem_DOk Sem1) H0)
                (TOk_mono _ _ _ Hle HTa) HTv Heq) as (s2 & D2 & n2 & S3 & St2 & Sem2).
    pose proof (Sem_supd Dd Sa A n1 s2 D2 n2 S3 Sem2) as Sem2'.
    destruct (CI_step _ _ _ _ _ _ _ _ _ Sem1 HC HG) as [HC1 HG1].
    exists (scomp s2 s1), D2, n2, S3, typ_Float, (e_tofloat e').
    refine (conj _ (conj (Sem_comp _ _ _ _ _ _ _ _ _ _ _ Sem1 Sem2') (conj _ (conj _ _)))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 St2)) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2). cbn [infer]. rewrite E1, E2. reflexivity.
    + apply TOk_scalar. right. left. reflexivity.
    + apply teqD_refl.
    + cbn [is_gen_value]; try reflexivity; try assumption.
  - (* arithmetic *)
    destruct (IHctyping1 D G n Sg Hd HK HG HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & Heq1 & HgHeq1).
    destruct (CI_step _ _ _ _ _ _ _ _ _ Sem1 HC HG) as [HC1 HG1].
    destruct (IHctyping2 D1a (apC s1 G) n1 Sa (Sem_DOk Sem1) (Sem_KR Sem1) HG1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & Heq2 & HgHeq2).
    assert (Hle : n2 <= S n2) by lia.
    assert (HTv : TOk (S n2) (typ_Var (ea n2))) by (apply TOk_var; apply old_ea; lia).
    pose proof (TOk_ap _ _ _ _ (Sem_SI Sem2) HTa) as HTa2.
    assert (Hg : sat Dd (generic_sort o) A) by (rewrite (generic_sort_arith o H); exact H1).
    assert (Heq : teqD Dd (apT (supd Sb (ea n2) A) (apT s2 Ta)) (apT (supd Sb (ea n2) A) (typ_Var (ea n2)))).
    { rewrite (apT_supd Sb (ea n2) A _ (proj1 HTa2) (fun Hin => proj2 HTa2 _ Hin n2 (le_n n2) eq_refl)),
        apT_Var, supd_same.
      eapply teqD_trans; [ apply teqD_sym; apply ap_factor_rf;
        [ exact (proj1 HTa) | intros z Hz; exact (Sem_F Sem2 z (proj2 HTa z Hz)) ] | ].
      exact Heq1. }
    destruct (unify_step Dd (upd D2 (ea n2) (generic_sort o)) _ _ _ (S n2)
                (DOk_upd D2 n2 _ (Sem_DOk Sem2))
                (KR_supd_upd D2 Dd Sb n2 (generic_sort o) A (Sem_KR Sem2) (Sem_DOk Sem2) Hg)
                (TOk_mono _ _ _ Hle HTa2) HTv Heq) as (s3 & D3 & n3 & S3 & St3 & Sem3).
    pose proof (Sem_supd Dd Sb A n2 s3 D3 n3 S3 Sem3) as Sem3'.
    pose proof (TOk_ap _ _ _ _ (Sem_SI Sem3) HTv) as HTc3.
    pose proof (TOk_ap _ _ _ _ (Sem_SI Sem3') HTb) as HTb3.
    assert (Fc : teqD Dd A (apT S3 (apT s3 (typ_Var (ea n2))))).
    { pose proof (Sem_F Sem3 (ea n2) (old_ea (S n2) n2 (Nat.lt_succ_diag_r n2))) as F.
      rewrite supd_same in F. exact F. }
    assert (Heq' : teqD Dd (apT S3 (apT s3 Tb)) (apT S3 (apT s3 (typ_Var (ea n2))))).
    { eapply teqD_trans; [ apply teqD_sym; apply ap_factor_rf;
        [ exact (proj1 HTb) | intros z Hz; exact (Sem_F Sem3' z (proj2 HTb z Hz)) ] | ].
      eapply teqD_trans; [ exact Heq2 | exact Fc ]. }
    destruct (unify_step Dd D3 S3 _ _ n3 (Sem_DOk Sem3) (Sem_KR Sem3) HTb3 HTc3 Heq')
      as (s4 & D4 & n4 & S4 & St4 & Sem4).
    exists (scomp s4 (scomp s3 (scomp s2 s1))), D4, n4, S4, (apT s4 (apT s3 (typ_Var (ea n2)))), (e_bin e1' o e2').
    refine (conj _ (conj (Sem_comp _ _ _ _ _ _ _ _ _ _ _
      (Sem_comp _ _ _ _ _ _ _ _ _ _ _ (Sem_comp _ _ _ _ _ _ _ _ _ _ _ Sem1 Sem2) Sem3') Sem4) (conj _ (conj _ _)))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3 St4)))) as HSt.
      stable_run HSt. destruct Hf as (E1 & E2 & E3 & E4). cbn [infer]. rewrite E1, E2.
      rewrite (is_cmp_op_false o H), (is_generic_op_true o H0). cbv beta iota zeta.
      rewrite E3, E4. rewrite (bin_res_arith o _ H). reflexivity.
    + exact (TOk_ap _ _ _ _ (Sem_SI Sem4) HTc3).
    + eapply teqD_trans; [ apply teqD_sym; apply ap_factor_rf;
        [ exact (proj1 HTc3) | intros z Hz; exact (Sem_F Sem4 z (proj2 HTc3 z Hz)) ] | ].
      apply teqD_sym. exact Fc.
    + cbn [is_gen_value]; try reflexivity; try assumption.
  - (* division *)
    destruct (IHctyping1 D G n Sg Hd HK HG HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & Heq1 & HgHeq1).
    destruct (CI_step _ _ _ _ _ _ _ _ _ Sem1 HC HG) as [HC1 HG1].
    destruct (IHctyping2 D1a (apC s1 G) n1 Sa (Sem_DOk Sem1) (Sem_KR Sem1) HG1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & Heq2 & HgHeq2).
    pose proof (TOk_ap _ _ _ _ (Sem_SI Sem2) HTa) as HTa2.
    assert (HTf : forall m, TOk m typ_Float) by (intros m; apply TOk_scalar; right; left; reflexivity).
    assert (Heq : teqD Dd (apT Sb (apT s2 Ta)) (apT Sb typ_Float)).
    { eapply teqD_trans; [ apply teqD_sym; apply ap_factor_rf;
        [ exact (proj1 HTa) | intros z Hz; exact (Sem_F Sem2 z (proj2 HTa z Hz)) ] | ].
      exact Heq1. }
    destruct (unify_step Dd D2 Sb _ _ n2 (Sem_DOk Sem2) (Sem_KR Sem2) HTa2 (HTf n2) Heq)
      as (s3 & D3 & n3 & S3 & St3 & Sem3).
    pose proof (TOk_ap _ _ _ _ (Sem_SI Sem3) HTb) as HTb3.
    assert (Heq' : teqD Dd (apT S3 (apT s3 Tb)) (apT S3 typ_Float)).
    { eapply teqD_trans; [ apply teqD_sym; apply ap_factor_rf;
        [ exact (proj1 HTb) | intros z Hz; exact (Sem_F Sem3 z (proj2 HTb z Hz)) ] | ].
      exact Heq2. }
    destruct (unify_step Dd D3 S3 _ _ n3 (Sem_DOk Sem3) (Sem_KR Sem3) HTb3 (HTf n3) Heq')
      as (s4 & D4 & n4 & S4 & St4 & Sem4).
    exists (scomp s4 (scomp s3 (scomp s2 s1))), D4, n4, S4, typ_Float, (e_bin e1' bop_div e2').
    refine (conj _ (conj (Sem_comp _ _ _ _ _ _ _ _ _ _ _
      (Sem_comp _ _ _ _ _ _ _ _ _ _ _ (Sem_comp _ _ _ _ _ _ _ _ _ _ _ Sem1 Sem2) Sem3) Sem4) (conj _ (conj _ _)))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3 St4)))) as HSt.
      stable_run HSt. destruct Hf as (E1 & E2 & E3 & E4). cbn [infer]. rewrite E1, E2.
      rewrite (is_cmp_op_false bop_div ltac:(discriminate)).
      change (is_generic_op bop_div) with false. cbv beta iota zeta.
      rewrite E3, E4. reflexivity.
    + exact (HTf n4).
    + apply teqD_refl.
    + cbn [is_gen_value]; try reflexivity; try assumption.
  - (* comparison *)
    destruct (IHctyping1 D G n Sg Hd HK HG HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & Heq1 & HgHeq1).
    destruct (CI_step _ _ _ _ _ _ _ _ _ Sem1 HC HG) as [HC1 HG1].
    destruct (IHctyping2 D1a (apC s1 G) n1 Sa (Sem_DOk Sem1) (Sem_KR Sem1) HG1 HC1)
      as (s2 & D2 & n2 & Sb & Tb & e2' & St2 & Sem2 & HTb & Heq2 & HgHeq2).
    pose proof (TOk_ap _ _ _ _ (Sem_SI Sem2) HTa) as HTa2.
    assert (Heq : teqD Dd (apT Sb (apT s2 Ta)) (apT Sb Tb)).
    { eapply teqD_trans; [ apply teqD_sym; apply ap_factor_rf;
        [ exact (proj1 HTa) | intros z Hz; exact (Sem_F Sem2 z (proj2 HTa z Hz)) ] | ].
      eapply teqD_trans; [ exact Heq1 | apply teqD_sym; exact Heq2 ]. }
    destruct (unify_step Dd D2 Sb _ _ n2 (Sem_DOk Sem2) (Sem_KR Sem2) HTa2 HTb Heq)
      as (s3 & D3 & n3 & S3 & St3 & Sem3).
    pose proof (TOk_ap _ _ _ _ (Sem_SI Sem3) HTb) as HTb3.
    assert (Hle : n3 <= S n3) by lia.
    assert (HTv : TOk (S n3) (typ_Var (ea n3))) by (apply TOk_var; apply old_ea; lia).
    assert (Heq' : teqD Dd (apT (supd S3 (ea n3) A) (apT s3 Tb)) (apT (supd S3 (ea n3) A) (typ_Var (ea n3)))).
    { rewrite (apT_supd S3 (ea n3) A _ (proj1 HTb3) (fun Hin => proj2 HTb3 _ Hin n3 (le_n n3) eq_refl)),
        apT_Var, supd_same.
      eapply teqD_trans; [ apply teqD_sym; apply ap_factor_rf;
        [ exact (proj1 HTb) | intros z Hz; exact (Sem_F Sem3 z (proj2 HTb z Hz)) ] | ].
      exact Heq2. }
    destruct (unify_step Dd (upd D3 (ea n3) k_Eq) _ _ _ (S n3) (DOk_upd D3 n3 _ (Sem_DOk Sem3))
                (KR_supd_upd D3 Dd S3 n3 k_Eq A (Sem_KR Sem3) (Sem_DOk Sem3) H0)
                (TOk_mono _ _ _ Hle HTb3) HTv Heq') as (s4 & D4 & n4 & S4 & St4 & Sem4).
    pose proof (Sem_supd Dd S3 A n3 s4 D4 n4 S4 Sem4) as Sem4'.
    exists (scomp s4 (scomp s3 (scomp s2 s1))), D4, n4, S4, typ_Bool, (e_bin e1' o e2').
    refine (conj _ (conj (Sem_comp _ _ _ _ _ _ _ _ _ _ _
      (Sem_comp _ _ _ _ _ _ _ _ _ _ _ (Sem_comp _ _ _ _ _ _ _ _ _ _ _ Sem1 Sem2) Sem3) Sem4') (conj _ (conj _ _)))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 (Stable_and _ _ St2 (Stable_and _ _ St3 St4)))) as HSt.
      stable_run HSt. destruct Hf as (E1 & E2 & E3 & E4). cbn [infer]. rewrite E1, E2.
      rewrite (is_cmp_op_true o H). cbv beta iota zeta. rewrite E3, E4. reflexivity.
    + apply TOk_scalar. right. right. left. reflexivity.
    + apply teqD_refl.
    + cbn [is_gen_value]; try reflexivity; try assumption.
  - (* let of a binding that is not a value *)
    destruct (IHctyping D G n Sg Hd HK HG HC)
      as (s1 & D1a & n1 & Sa & Ta & e1' & St1 & Sem1 & HTa & Heq1 & Hgv).
    destruct (CI_step _ _ _ _ _ _ _ _ _ Sem1 HC HG) as [HC1 HG1].
    rewrite H in Hgv.
    assert (Hx : fresh_var (apC s1 G) e2 `notin` dom Gd `union` fv_exp e2).
    { rewrite (CI_dom _ _ _ _ HC). pose proof (dom_apC s1 G).
      pose proof (fresh_var_notin_dom (apC s1 G) e2). pose proof (fresh_var_notin_fv (apC s1 G) e2). fsetdec. }
    destruct (H2 _ Hx D1a ((fresh_var (apC s1 G) e2 ~ sch_mono Ta) ++ apC s1 G) n1 Sa
                (Sem_DOk Sem1) (Sem_KR Sem1) (GOk_cons n1 _ Ta _ HTa HG1)
                (CI_cons Dd Sa Gd (apC s1 G) _ T1 Ta HC1 Heq1))
      as (s2 & D2 & n2 & Sb & T & e2' & St2 & Sem2 & HT & Heq2 & Hg2).
    exists (scomp s2 s1), D2, n2, Sb, T, (e_let e1' (cl 0 (fresh_var (apC s1 G) e2) e2')).
    refine (conj _ (conj (Sem_comp _ _ _ _ _ _ _ _ _ _ _ Sem1 Sem2) (conj HT (conj Heq2 _)))).
    + pose proof (Stable_below _ (Stable_and _ _ St1 St2)) as HSt. stable_run HSt.
      destruct Hf as (E1 & E2). cbn [infer]. rewrite E1, Hgv. cbv beta iota zeta. rewrite E2. reflexivity.
    + reflexivity.
  - (* conversion *)
    destruct (IHctyping D G n Sg Hd HK HG HC) as (s & D' & n' & S2 & T0 & e' & Hst & Hsem & HT & Heq & HgHeq).
    exists s, D', n', S2, T0, e'. refine (conj Hst (conj Hsem (conj HT (conj _ HgHeq)))).
    eapply teqD_trans; [ exact Heq | exact H0 ].
Qed.

(* The closed program: a derivation of a core program at the program judgment
   gives a run of the closed entry point from some fuel on, whose result is a
   principal type of the derivation's, and whose elaborated term erases to the
   program. *)
Theorem infer_complete_core_closed : forall e T, ctyping d_any nil e T ->
  exists D T' e' S2,
    Stable (fun f => infer_closed_elab f e = Some (D, T', e')) /\ erase e' = e /\
    KR D d_any S2 /\ teqD d_any (apT S2 T') T /\ rf T'.
Proof.
  intros e T H.
  destruct (infer_complete_core d_any nil e T H d_any nil 0 sid (d_any_DOk 0) (KR_id d_any)
              (GOk_nil 0) (CI_nil d_any sid)) as (s & D' & n' & S2 & T' & e' & St & Sem & HT & Heq & HgHeq).
  exists D', T', e', S2.
  assert (St' : Stable (fun f => infer_closed_elab f e = Some (D', T', e'))).
  { eapply Stable_mono; [ | exact St ]. intros f Hf. unfold infer_closed_elab. rewrite Hf. reflexivity. }
  refine (conj St' (conj _ (conj (Sem_KR Sem) (conj Heq (proj1 HT))))).
  destruct St' as [f0 Hf0]. exact (proj2 (infer_closed_sound f0 e D' T' e' (Hf0 f0 (le_n f0)))).
Qed.

(* The identity function has the derivation at [Int -> Int]; the algorithm
   answers with a type of which that one is an instance. *)
Example core_identity : exists D T' e' S2,
  Stable (fun f => infer_closed_elab f (e_abs (e_fvar_b 0)) = Some (D, T', e')) /\
  erase e' = e_abs (e_fvar_b 0) /\ KR D d_any S2 /\
  teqD d_any (apT S2 T') (typ_Arrow typ_Int typ_Int) /\ rf T'.
Proof.
  apply infer_complete_core_closed. apply C_Abs. intros x Hx. simpl.
  apply C_Var; [ solve_uniq | apply binds_one_3; reflexivity ].
Qed.

(* A comparison, which unifies its operands and only then requires the joined
   type to be [Eq]. *)
Example core_comparison : exists D T' e' S2,
  Stable (fun f => infer_closed_elab f (e_abs (e_bin (e_fvar_b 0) bop_eq (e_fvar_b 0))) = Some (D, T', e')) /\
  erase e' = e_abs (e_bin (e_fvar_b 0) bop_eq (e_fvar_b 0)) /\ KR D d_any S2 /\
  teqD d_any (apT S2 T') (typ_Arrow typ_Int typ_Bool) /\ rf T'.
Proof.
  apply infer_complete_core_closed. apply C_Abs. intros x Hx. simpl.
  apply C_Cmp with (A := typ_Int); [ reflexivity | simpl; auto | | ];
    (apply C_Var; [ solve_uniq | apply binds_one_3; reflexivity ]).
Qed.
