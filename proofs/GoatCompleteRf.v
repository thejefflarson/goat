(* Completeness of algorithm W, stage 7.6j: the unifier on record-free types
   with sorts and a supply (docs/design/phase7-proof-plan.md).

   The record-free analogues of the unifier's step, [Sem], [Img] and their
   composition, over atoms below a supply.  The unifier's completeness over the
   fragment is [unify_stepG] (GoatCompleteLive.v).

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteRows.
Require Import Goat.GoatCompleteUnify.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteBindRow.
Require Import Goat.GoatCompleteRewrite.
Require Import Goat.GoatCompleteOcc.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the fragment ---- *)

Fixpoint rf (T : typ) : Prop :=
  match T with
  | typ_Int | typ_Float | typ_Bool | typ_Unit | typ_String | typ_Var _ => True
  | typ_Arrow A B => rf A /\ rf B
  | _ => False
  end.

Lemma rf_facts : forall T, rf T ->
  pf T /\ lcb 0 T = true /\ (forall q, q `notin` frv_typ T) /\ (forall D S k, fld D S k T) /\
  (forall k, lcb k T = true).
Proof.
  induction T; simpl; intros H; try contradiction;
    try (repeat split; intros; first [ exact I | reflexivity | fsetdec ]; fail).
  destruct H as [HA HB]. destruct (IHT1 HA) as (A1 & A2 & A3 & A4 & A5).
  destruct (IHT2 HB) as (B1 & B2 & B3 & B4 & B5).
  refine (conj (conj A1 B1) (conj _ (conj _ (conj _ _)))).
  - rewrite (A5 0), (B5 0). reflexivity.
  - intros q Hq. apply AtomSetFacts.union_iff in Hq. destruct Hq as [Hq|Hq];
      [ exact (A3 q Hq) | exact (B3 q Hq) ].
  - intros D S k. exact (conj (A4 D S k) (B4 D S k)).
  - intros k. rewrite (A5 k), (B5 k). reflexivity.
Qed.

(* A step's effect on the old variables: the supply grows, the images are
   record-free over atoms below the new supply, and no row variable moves. *)
Definition SI (n n' : nat) (s : sub) : Prop :=
  n <= n' /\
  (forall x, old n x -> rf (sT s x) /\ forall y, y `in` ftv_typ (sT s x) -> old n' y) /\
  (forall q, old n q -> sR s q = row_Var q).

Lemma old_le : forall n n' x, n <= n' -> old n x -> old n' x.
Proof. intros n n' x Hl H m Hm. apply H. lia. Qed.

Lemma SI_id : forall n, SI n n sid.
Proof.
  intros n. split; [ lia | split; intros x Hx; [ | reflexivity ] ].
  split; [ exact I | ]. intros y Hy. cbn [sT sid idt] in Hy. simpl in Hy.
  apply AtomSetFacts.singleton_iff in Hy. subst. exact Hx.
Qed.

Lemma rf_ap : forall s T, rf T -> (forall x, x `in` ftv_typ T -> rf (sT s x)) -> rf (apT s T).
Proof.
  intros s T. induction T; simpl; intros H Hs; try contradiction; try exact I.
  - destruct H as [HA HB]. split;
      [ apply IHT1; [ exact HA | intros x Hx; apply Hs; apply AtomSetFacts.union_iff; left; exact Hx ]
      | apply IHT2; [ exact HB | intros x Hx; apply Hs; apply AtomSetFacts.union_iff; right; exact Hx ] ].
  - apply Hs. fsetdec.
Qed.

(* The atoms of an image of a record-free type are the atoms of the images of its variables. *)
Lemma ftv_ap_rf : forall s T y, rf T -> y `in` ftv_typ (apT s T) ->
  exists x, x `in` ftv_typ T /\ y `in` ftv_typ (sT s x).
Proof.
  intros s T y Hrf Hy. unfold apT in Hy. destruct (ftv_ap_typ _ _ _ _ Hy) as [H|[p [Hp _]]];
    [ exact H | exfalso; exact (proj1 (proj2 (proj2 (rf_facts T Hrf))) p Hp) ].
Qed.

Lemma SI_comp : forall n n1 n2 s1 s2, SI n n1 s1 -> SI n1 n2 s2 -> SI n n2 (scomp s2 s1).
Proof.
  intros n n1 n2 s1 s2 (Hl1 & H1 & R1) (Hl2 & H2 & R2). split; [ lia | split ].
  - intros x Hx. destruct (H1 x Hx) as [Hrf Hold].
    change (rf (apT s2 (sT s1 x)) /\ forall y, y `in` ftv_typ (apT s2 (sT s1 x)) -> old n2 y).
    split.
    + apply rf_ap; [ exact Hrf | intros z Hz; exact (proj1 (H2 z (Hold z Hz))) ].
    + intros y Hy. destruct (ftv_ap_rf s2 _ y Hrf Hy) as (z & Hz & Hyz).
      exact (proj2 (H2 z (Hold z Hz)) y Hyz).
  - intros q Hq. change (apR s2 (sR s1 q) = row_Var q). rewrite (R1 q Hq).
    exact (R2 q (old_le n n1 q Hl1 Hq)).
Qed.

(* ---- where [push_sort] sends the type variables ---- *)

Lemma push_sort_new : forall l D k n sp D' n',
  push_sort D k l n = (sp, D', n') -> (forall c, In c l -> old n c) ->
  forall x y, sT sp x = typ_Var y -> y = x \/ exists m, n <= m /\ m < n' /\ y = ea m.
Proof.
  induction l as [|b l IH]; intros D k n sp D' n' H Hold x y E; cbn [push_sort] in H.
  - inversion H; subst. change (typ_Var x = typ_Var y) in E. injection E as <-. left. reflexivity.
  - destruct (finer_b (D b) k).
    + exact (IH _ _ _ _ _ _ H (fun c Hc => Hold c (or_intror Hc)) x y E).
    + destruct (finer_b k (D b));
        [ | destruct (push_sort D k l n) as [[s1 D1] n1] eqn:E1; inversion H; subst;
            change (apT s1 (sT (sbT b typ_Float) x) = typ_Var y) in E; cbn [sT sbT] in E;
            destruct (Atom.eq_dec x b) as [->|Hne];
            [ simpl in E; discriminate E
            | exact (IH _ _ _ _ _ _ E1 (fun c Hc => Hold c (or_intror Hc)) x y E) ] ].
      destruct (push_sort (upd D (ea n) k) k l (Datatypes.S n)) as [[s1 D1] n1] eqn:E1.
      inversion H; subst.
      assert (Hold' : forall c, In c l -> old (Datatypes.S n) c).
      { intros c Hc m Hm. apply (Hold c (or_intror Hc)). lia. }
      destruct (push_sort_facts _ _ _ _ _ _ _ E1 Hold') as (_ & Hn1 & H3 & _ & _ & _).
      change (apT s1 (sT (sbT b (typ_Var (ea n))) x) = typ_Var y) in E.
      cbn [sT sbT] in E. destruct (Atom.eq_dec x b) as [->|Hne].
      * assert (Hnl : ~ In (ea n) l).
        { intros Hin. exact (Hold (ea n) (or_intror Hin) n (le_n n) eq_refl). }
        change (sT s1 (ea n) = typ_Var y) in E. rewrite (H3 _ Hnl) in E. injection E as <-.
        right. exists n. split; [ lia | split; [ lia | reflexivity ] ].
      * change (sT s1 x = typ_Var y) in E.
        destruct (IH _ _ _ _ _ _ E1 Hold' x y E) as [->|[m [H1 [H2 ->]]]].
        -- left. reflexivity.
        -- right. exists m. split; [ lia | split; [ exact H2 | reflexivity ] ].
Qed.

(* ---- [bind_prop] on a record-free type ---- *)

Lemma elements_empty_of : forall S : atoms, (forall q, q `notin` S) -> AtomSetImpl.elements S = nil.
Proof.
  intros S H. destruct (AtomSetImpl.elements S) as [|q l] eqn:E; [ reflexivity | ].
  exfalso. apply (H q). apply in_elts. rewrite E. left. reflexivity.
Qed.

Lemma rf_live : forall T, rf T -> na T = true /\ ftv_live T = ftv_typ T /\ frv_live T = frv_typ T.
Proof.
  induction T; simpl; intros H; try contradiction;
    try (repeat split; reflexivity; fail).
  - destruct H as [HA HB]. destruct (IHT1 HA) as (A1 & A2 & A3). destruct (IHT2 HB) as (B1 & B2 & B3).
    rewrite A1, B1, A2, A3, B2, B3. repeat split; reflexivity.
Qed.

Lemma rf_bind0 : forall D a T n r, rf T -> bind_prop D a T n = Some r -> bind_prop0 D a T n = Some r.
Proof.
  intros D a T n r Hrf H. unfold bind_prop in H.
  destruct (bind_prop0 D a T n) as [x|] eqn:E0; [ exact H | ].
  destruct (occT a T); [ discriminate | ].
  assert (Hf : forall k, forced k T = nil) by (destruct T; simpl in Hrf; try contradiction; reflexivity).
  rewrite Hf in H. discriminate H.
Qed.

Lemma bind_prop_SI : forall D a T n s D' n',
  bind_prop D a T n = Some (s, D', n') -> DOk D n -> old n a -> rf T ->
  (forall b, b `in` ftv_typ T -> old n b) ->
  (forall b, b `in` ftv_typ T -> cmpb (D b) (D a)) -> SI n n' s.
Proof.
  intros D a T n s D' n' H Hd Ha Hrf Hot Hcb.
  destruct (rf_facts T Hrf) as (_ & _ & Hfrv & _ & _).
  pose proof (rf_bind0 _ _ _ _ _ Hrf H) as H0. clear H.
  rename H0 into H. destruct (rf_live T Hrf) as (_ & Hlt & Hlr).
  unfold bind_prop0 in H. rewrite Hlt, Hlr in H. destruct (occT a T); [ discriminate | ].
  assert (Holdl : forall b, In b (AtomSetImpl.elements (ftv_typ T)) -> old n b)
    by (intros b Hb; apply Hot; apply in_elts; exact Hb).
  destruct (push_sort D (D a) (AtomSetImpl.elements (ftv_typ T)) n) as [[sp D1] n1] eqn:Ep.
  destruct (push_sort_facts _ _ _ _ _ _ _ Ep Holdl) as (P1 & P2 & P3 & P4' & P5 & P6).
  pose proof (P4' (fun b Hb => Hcb b (proj1 (in_elts _ _) Hb))) as P4.
  rewrite (elements_empty_of _ Hfrv) in H. cbn [push_sort_r] in H.
  set (T' := apT sid (apT sp T)) in H.
  destruct (occT a T'); [ discriminate | ]. destruct (sat_b D1 (D1 a) T'); [ | discriminate ].
  inversion H; subst; clear H.
  assert (Hvp : forall x, exists y, sT sp x = typ_Var y)
    by (intros x; destruct (P4 x) as (y & E & _); exists y; exact E).
  assert (HT' : T' = apT sp T) by (subst T'; apply apT_id).
  assert (Hrf' : rf (apT sp T)).
  { apply rf_ap; [ exact Hrf | intros x _; destruct (Hvp x) as [y ->]; exact I ]. }
  assert (Hatoms : forall y, y `in` ftv_typ (apT sp T) -> old n' y).
  { intros y Hy. destruct (ftv_ap_rf sp T y Hrf Hy) as (x & Hx & Hyx).
    destruct (Hvp x) as [z Ez]. rewrite Ez in Hyx. simpl in Hyx.
    apply AtomSetFacts.singleton_iff in Hyx. subst z.
    destruct (push_sort_new _ _ _ _ _ _ _ Ep Holdl x y Ez) as [->|[m [H1 [H2 ->]]]].
    - exact (old_le n n' x ltac:(lia) (Hot x Hx)).
    - intros m' Hm' E. apply ea_inj in E. lia. }
  split; [ lia | split ].
  - intros x Hx. change (rf (apT (sbT a T') (apT sid (sT sp x))) /\
      forall y, y `in` ftv_typ (apT (sbT a T') (apT sid (sT sp x))) -> old n' y).
    destruct (P4 x) as (y & Ey & _). rewrite Ey. rewrite HT' in *.
    change (apT sid (typ_Var y)) with (typ_Var y).
    change (apT (sbT a (apT sp T)) (typ_Var y)) with (sT (sbT a (apT sp T)) y).
    cbn [sT sbT]. destruct (Atom.eq_dec y a) as [_|Hya].
    + split; [ exact Hrf' | exact Hatoms ].
    + split; [ exact I | ]. intros z Hz. simpl in Hz. apply AtomSetFacts.singleton_iff in Hz. subst z.
      destruct (push_sort_new _ _ _ _ _ _ _ Ep Holdl x y Ey) as [->|[m [H1 [H2 ->]]]].
      * exact (old_le n n' x ltac:(lia) Hx).
      * intros m' Hm' E. apply ea_inj in E. lia.
  - intros q Hq. change (apR (sbT a T') (apR sid (sR sp q)) = row_Var q).
    rewrite (P1 q). reflexivity.
Qed.

(* ---- one step's promise ---- *)

(* [Sg] factors through [s] by the extension [S2] at the environment [D'], and
   the step keeps what the next call needs. *)
Definition Sem (DT : denv) (Sg : sub) (n : nat) (s : sub) (D' : denv) (n' : nat) (S2 : sub) : Prop :=
  KR D' DT S2 /\ DOk D' n' /\ SI n n' s /\
  (forall x, old n x -> teqD DT (sT Sg x) (apT S2 (sT s x))) /\
  (forall q, old n q -> sR S2 q = sR Sg q).

Lemma Sem_id : forall DT Sg D n, KR D DT Sg -> DOk D n -> Sem DT Sg n sid D n Sg.
Proof.
  intros DT Sg D n HK Hd. refine (conj HK (conj Hd (conj (SI_id n) (conj _ _)))).
  - intros x _. apply teqD_refl.
  - intros q _. reflexivity.
Qed.

Lemma Sem_sbT : forall DT Sg D n a a', KR D DT Sg -> DOk D n -> old n a' ->
  teqD DT (sT Sg a) (sT Sg a') -> Sem DT Sg n (sbT a (typ_Var a')) D n Sg.
Proof.
  intros DT Sg D n a a' HK Hd Ha' Heq. refine (conj HK (conj Hd (conj _ (conj _ _)))).
  - split; [ lia | split ].
    + intros x Hx. cbn [sT sbT]. destruct (Atom.eq_dec x a) as [_|_]; split; try exact I;
        intros y Hy; simpl in Hy; apply AtomSetFacts.singleton_iff in Hy; subst; assumption.
    + intros q _. reflexivity.
  - intros x _. cbn [sT sbT]. destruct (Atom.eq_dec x a) as [->|_]; [ exact Heq | apply teqD_refl ].
  - intros q _. reflexivity.
Qed.

(* ---- factoring through a step, on a record-free type ---- *)

Lemma ap_factor_rf : forall DT Sg S2 s T, rf T ->
  (forall x, x `in` ftv_typ T -> teqD DT (sT Sg x) (apT S2 (sT s x))) ->
  teqD DT (apT Sg T) (apT S2 (apT s T)).
Proof.
  intros DT Sg S2 s T. induction T; simpl; intros H Hx; try contradiction; try apply teqD_refl.
  - destruct H as [HA HB]. apply teqD_Arrow;
      [ apply IHT1; [ exact HA | intros x Hx'; apply Hx; apply AtomSetFacts.union_iff; left; exact Hx' ]
      | apply IHT2; [ exact HB | intros x Hx'; apply Hx; apply AtomSetFacts.union_iff; right; exact Hx' ] ].
  - apply Hx. fsetdec.
Qed.

Lemma rf_po : forall S a T, rf T -> a `in` ftv_typ T -> po S (eq a) (fun _ => False) T.
Proof.
  intros S a T. induction T; simpl; intros H Hin; try contradiction; try fsetdec.
  - destruct H as [HA HB]. apply AtomSetFacts.union_iff in Hin. destruct Hin as [Hin|Hin];
      [ left; exact (IHT1 HA Hin) | right; exact (IHT2 HB Hin) ].
Qed.

(* ---- the leaves ---- *)

Lemma sem_bind : forall DT (D : denv) Sg a T n,
  DOk D n -> KR D DT Sg -> old n a -> rf T -> (forall v, T <> typ_Var v) ->
  (forall b, b `in` ftv_typ T -> old n b) -> teqD DT (sT Sg a) (apT Sg T) ->
  exists s D' n' S2, bind_prop D a T n = Some (s, D', n') /\ Sem DT Sg n s D' n' S2 /\ Img Sg S2.
Proof.
  intros DT D Sg a T n Hd HK Ha Hrf Hv Hot Heq.
  destruct (rf_facts T Hrf) as (Hpf & Hlc & Hfrv & Hfld & _).
  assert (Hcb : forall b, b `in` ftv_typ T -> cmpb (D b) (D a)).
  { intros b Hb. left.
    destruct T as [ | | | | | T1 T2 | | | | | ]; try (simpl in Hrf; contradiction);
      try (exfalso; exact (Hv _ eq_refl)); try (simpl in Hb; fsetdec).
    assert (Hsa : sat DT (D a) (apT Sg (typ_Arrow T1 T2))).
    { apply (sat_teqD DT (D a) (sT Sg a) _ Heq). exact (proj1 HK a). }
    cbn in Hsa. rewrite Hsa. destruct (D b); reflexivity. }
  destruct (bind_prop_pres_complete D DT Sg a T n Hd HK Ha Hv Hot (fun q Hq => ltac:(exfalso; exact (Hfrv q Hq)))
              Hpf Hlc (proj1 (rf_live T Hrf)) Hcb (fun q Hq => ltac:(exfalso; exact (Hfrv q Hq))) (rf_po Sg a T Hrf) (Hfld DT Sg (D a)) Heq)
    as (s & D' & n' & S2 & E & K & Hl & Hd' & F & Fr & Im & _).
  exists s, D', n', S2. refine (conj E (conj (conj K (conj Hd' (conj _ (conj F _)))) Im)).
  - exact (bind_prop_SI D a T n s D' n' E Hd Ha Hrf Hot Hcb).
  - intros q Hq. pose proof (Fr q Hq) as E1.
    pose proof (proj2 (proj2 (bind_prop_SI D a T n s D' n' E Hd Ha Hrf Hot Hcb)) q Hq) as E2.
    rewrite E2 in E1. symmetry. exact E1.
Qed.

Lemma stable_bind_l : forall D a T n r,
  bind_prop D a T n = Some r -> (forall v, T <> typ_Var v) ->
  Stable (fun f => unify_tD f D (typ_Var a) T n = Some r).
Proof.
  intros D a T n r E Hv. exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  destruct T; try (exfalso; exact (Hv _ eq_refl)); exact E.
Qed.

Lemma stable_bind_r : forall D a T n r,
  bind_prop D a T n = Some r -> (forall v, T <> typ_Var v) ->
  Stable (fun f => unify_tD f D T (typ_Var a) n = Some r).
Proof.
  intros D a T n r E Hv. exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  destruct T; try (exfalso; exact (Hv _ eq_refl)); exact E.
Qed.

Lemma stable_scalar : forall D c n,
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) ->
  Stable (fun f => unify_tD f D c c n = Some (sid, D, n)).
Proof.
  intros D c n Hc. exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; reflexivity.
Qed.

Lemma stable_varvar : forall D a a' n,
  Stable (fun f => unify_tD f D (typ_Var a) (typ_Var a') n =
    Some (if Atom.eq_dec a a' then sid else if finer_b (D a') (D a) then sbT a (typ_Var a')
          else if finer_b (D a) (D a') then sbT a' (typ_Var a) else meet_float a a', D, n)).
Proof.
  intros D a a' n. exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  cbn [unify_tD]. destruct (Atom.eq_dec a a') as [->|Hne]; [ reflexivity | ].
  destruct (finer_b (D a') (D a)); [ reflexivity | ].
  destruct (finer_b (D a) (D a')); reflexivity.
Qed.

Lemma meet_float_sT : forall a b x,
  ((x = a \/ x = b) /\ sT (meet_float a b) x = typ_Float) \/ sT (meet_float a b) x = typ_Var x.
Proof.
  intros a b x. unfold meet_float.
  change (((x = a \/ x = b) /\ apT (sbT b typ_Float) (sT (sbT a typ_Float) x) = typ_Float) \/
          apT (sbT b typ_Float) (sT (sbT a typ_Float) x) = typ_Var x).
  cbn [sT sbT]. destruct (Atom.eq_dec x a) as [->|Hne]; [ left; split; [ left; reflexivity | reflexivity ] | ].
  change (((x = a \/ x = b) /\ sT (sbT b typ_Float) x = typ_Float) \/ sT (sbT b typ_Float) x = typ_Var x).
  cbn [sT sbT]. destruct (Atom.eq_dec x b) as [->|Hnb]; [ left; split; [ right; reflexivity | reflexivity ] | right; reflexivity ].
Qed.

(* Two variables the unifier meets at [Float]: neither sort is finer, and both
   images are [Float]. *)
Lemma Sem_meet : forall DT Sg D n a b, KR D DT Sg -> DOk D n ->
  teqD DT (sT Sg a) typ_Float -> teqD DT (sT Sg b) typ_Float ->
  Sem DT Sg n (meet_float a b) D n Sg.
Proof.
  intros DT Sg D n a b HK Hd Ha Hb. refine (conj HK (conj Hd (conj _ (conj _ _)))).
  - split; [ lia | split ].
    + intros x Hx. destruct (meet_float_sT a b x) as [[_ E]|E]; rewrite E; split; try exact I;
        intros y Hy; simpl in Hy; [ fsetdec | apply AtomSetFacts.singleton_iff in Hy; subst; exact Hx ].
    + intros q _. reflexivity.
  - intros x _. destruct (meet_float_sT a b x) as [[[H0|H0] E]|E]; try subst x; rewrite E.
    + exact Ha.
    + exact Hb.
    + apply teqD_refl.
  - intros q _. reflexivity.
Qed.

Ltac nv := intros ? Hnv; discriminate Hnv.
