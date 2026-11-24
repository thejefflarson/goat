(* Completeness of algorithm W, stage 7.6j: the unifier on record-free types
   with sorts and a supply (docs/design/phase7-proof-plan.md).

   This is the induction of statement A with the machinery in place and the row
   arms absent.  The types are base types, variables and arrows ([rf]); the
   substitution [Sg] respects the sorts ([KR D DT Sg]) and unifies the two types
   up to [teqD DT]; every atom of the types is below the supply ([old n]).  The
   unifier succeeds from some fuel on ([Stable]), and the extension [S2] of [Sg]
   to the fresh variables it makes respects the new environment, with [Sg]
   factoring through the result ([teqD DT]).  The composite of two steps
   threads [(D', n', S2)]: each call runs at the environment and supply the
   previous one left, with the substitution [S2] that call produced.  What a
   later call needs of an earlier result is [SI]: the images of the old
   variables are record-free, with every atom below the new supply, and no row
   variable is renamed.

   The occurs check and the field condition of [bind_prop] are not hypotheses
   here: with no entry in a type, every occurrence is present ([po]) and no
   field is absent ([fld]).  The measure is the size of the image
   ([tsz], [GoatCompleteRows.v]).

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
    + destruct (push_sort (upd D (ea n) k) k l (Datatypes.S n)) as [[s1 D1] n1] eqn:E1.
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

Lemma bind_prop_SI : forall D a T n s D' n',
  bind_prop D a T n = Some (s, D', n') -> DOk D n -> old n a -> rf T ->
  (forall b, b `in` ftv_typ T -> old n b) -> SI n n' s.
Proof.
  intros D a T n s D' n' H Hd Ha Hrf Hot.
  destruct (rf_facts T Hrf) as (_ & _ & Hfrv & _ & _).
  unfold bind_prop in H. destruct (occT a T); [ discriminate | ].
  assert (Holdl : forall b, In b (AtomSetImpl.elements (ftv_typ T)) -> old n b)
    by (intros b Hb; apply Hot; apply in_elts; exact Hb).
  destruct (push_sort D (D a) (AtomSetImpl.elements (ftv_typ T)) n) as [[sp D1] n1] eqn:Ep.
  destruct (push_sort_facts _ _ _ _ _ _ _ Ep Holdl) as (P1 & P2 & P3 & P4 & P5 & P6).
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
  destruct (bind_prop_pres_complete D DT Sg a T n Hd HK Ha Hv Hot (fun q Hq => ltac:(exfalso; exact (Hfrv q Hq)))
              Hpf Hlc (rf_po Sg a T Hrf) (Hfld DT Sg (D a)) Heq)
    as (s & D' & n' & S2 & E & K & Hl & Hd' & F & Fr & Im).
  exists s, D', n', S2. refine (conj E (conj (conj K (conj Hd' (conj _ (conj F _)))) Im)).
  - exact (bind_prop_SI D a T n s D' n' E Hd Ha Hrf Hot).
  - intros q Hq. pose proof (Fr q Hq) as E1.
    pose proof (proj2 (proj2 (bind_prop_SI D a T n s D' n' E Hd Ha Hrf Hot)) q Hq) as E2.
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
    Some (if Atom.eq_dec a a' then sid else if finer_b (D a') (D a) then sbT a (typ_Var a') else sbT a' (typ_Var a), D, n)).
Proof.
  intros D a a' n. exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  cbn [unify_tD]. destruct (Atom.eq_dec a a') as [->|Hne]; [ reflexivity | ].
  destruct (finer_b (D a') (D a)); reflexivity.
Qed.

Ltac nv := intros ? Hnv; discriminate Hnv.

Theorem unify_rf_complete_aux : forall (DT : denv) m (D : denv) Sg T1 T2 n,
  tsz (apT Sg T1) < m -> DOk D n -> KR D DT Sg -> rf T1 -> rf T2 ->
  (forall x, x `in` ftv_typ T1 -> old n x) -> (forall x, x `in` ftv_typ T2 -> old n x) ->
  teqD DT (apT Sg T1) (apT Sg T2) ->
  exists s D' n' S2, Stable (fun f => unify_tD f D T1 T2 n = Some (s, D', n')) /\
    Sem DT Sg n s D' n' S2 /\ Img Sg S2.
Proof.
  intros DT m. induction m as [|m IH]; intros D Sg T1 T2 n Hlt Hd HK C1 C2 A1 A2 Hteq; [ lia | ].
  destruct T1 as [ | | | | | A B | R | a | i | B1 | w A1' ]; try (simpl in C1; contradiction);
  destruct T2 as [ | | | | | A' B' | R' | a' | i' | B1' | w' A1'' ];
    try (simpl in C2; contradiction);
    try (exfalso; pose proof (teqD_thead _ _ _ Hteq) as Ht; unfold apT in Ht;
         cbn [ap_typ thead_tag] in Ht; discriminate Ht).
  all: try (exists sid, D, n, Sg; split; [ apply stable_scalar; tauto | exact (conj (Sem_id DT Sg D n HK Hd) (Img_refl Sg)) ]; fail).
  all: try (destruct (sem_bind DT D Sg a _ n Hd HK (A1 a ltac:(simpl; fsetdec)) C2 ltac:(nv) A2 Hteq)
              as (s & D' & n' & S2 & E & Hs);
            exists s, D', n', S2; split; [ exact (stable_bind_l D a _ n _ E ltac:(nv)) | exact Hs ]; fail).
  all: try (destruct (sem_bind DT D Sg a' _ n Hd HK (A2 a' ltac:(simpl; fsetdec)) C1 ltac:(nv) A1 (teqD_sym _ _ _ Hteq))
              as (s & D' & n' & S2 & E & Hs);
            exists s, D', n', S2; split; [ exact (stable_bind_r D a' _ n _ E ltac:(nv)) | exact Hs ]; fail).
  - (* Arrow, Arrow *)
    destruct C1 as [CA CB], C2 as [CA' CB'].
    change (apT Sg (typ_Arrow A B)) with (typ_Arrow (apT Sg A) (apT Sg B)) in Hlt, Hteq.
    change (apT Sg (typ_Arrow A' B')) with (typ_Arrow (apT Sg A') (apT Sg B')) in Hteq.
    cbn [tsz] in Hlt.
    destruct (teqD_Arrow_inv _ _ _ _ Hteq) as (X & Y & EX & H1 & H2).
    injection EX as <- <-.
    assert (AB : forall x, x `in` ftv_typ B -> old n x) by (intros x Hx; apply A1; simpl; fsetdec).
    assert (AB' : forall x, x `in` ftv_typ B' -> old n x) by (intros x Hx; apply A2; simpl; fsetdec).
    destruct (IH D Sg A A' n ltac:(lia) Hd HK CA CA'
                (fun x Hx => A1 x ltac:(simpl; fsetdec)) (fun x Hx => A2 x ltac:(simpl; fsetdec)) H1)
      as (s1 & D1 & n1 & S2 & E1 & (K1 & Hd1 & (Hl1 & I1 & Q1) & F1 & R1) & Im1).
    pose proof (ap_factor_rf DT Sg S2 s1 B CB (fun x Hx => F1 x (AB x Hx))) as FB.
    pose proof (ap_factor_rf DT Sg S2 s1 B' CB' (fun x Hx => F1 x (AB' x Hx))) as FB'.
    assert (Hrf1 : forall T, rf T -> (forall x, x `in` ftv_typ T -> old n x) ->
              rf (apT s1 T) /\ forall y, y `in` ftv_typ (apT s1 T) -> old n1 y).
    { intros T HT Ho. split.
      - apply rf_ap; [ exact HT | intros x Hx; exact (proj1 (I1 x (Ho x Hx))) ].
      - intros y Hy. destruct (ftv_ap_rf s1 T y HT Hy) as (x & Hx & Hyx).
        exact (proj2 (I1 x (Ho x Hx)) y Hyx). }
    destruct (Hrf1 B CB AB) as [RB OB]. destruct (Hrf1 B' CB' AB') as [RB' OB'].
    destruct (IH D1 S2 (apT s1 B) (apT s1 B') n1
                ltac:(rewrite <- (teqD_tsz _ _ _ FB); lia) Hd1 K1 RB RB' OB OB'
                (teqD_trans _ _ _ _ (teqD_sym _ _ _ FB) (teqD_trans _ _ _ _ H2 FB')))
      as (s2 & D2 & n2 & S3 & E2 & (K2 & Hd2 & I2 & F2 & R2) & Im2).
    exists (scomp s2 s1), D2, n2, S3. split.
    + eapply Stable_mono; [ | exact (Stable_below _ (Stable_and _ _ E1 E2)) ].
      intros [|f] Hf; [ contradiction | ]. destruct Hf as [Ha Hb].
      cbn [unify_tD]. rewrite Ha, Hb. reflexivity.
    + refine (conj (conj K2 (conj Hd2 (conj (SI_comp _ _ _ _ _ (conj Hl1 (conj I1 Q1)) I2) (conj _ _)))) (Img_trans _ _ _ Im1 Im2)).
      * intros x Hx. change (teqD DT (sT Sg x) (apT S3 (apT s2 (sT s1 x)))).
        destruct (I1 x Hx) as [Hrx Hox].
        eapply teqD_trans; [ exact (F1 x Hx) | ].
        apply ap_factor_rf; [ exact Hrx | intros z Hz; exact (F2 z (Hox z Hz)) ].
      * intros q Hq. rewrite (R2 q (old_le n n1 q Hl1 Hq)). exact (R1 q Hq).
  - (* Var, Var *)
    destruct (Atom.eq_dec a a') as [->|Hne].
    + exists sid, D, n, Sg. split; [ | exact (conj (Sem_id DT Sg D n HK Hd) (Img_refl Sg)) ].
      eapply Stable_mono; [ | exact (stable_varvar D a' a' n) ].
      intros f Hf. rewrite Hf. destruct (Atom.eq_dec a' a'); [ reflexivity | congruence ].
    + destruct (finer_b (D a') (D a)) eqn:Ef.
      * exists (sbT a (typ_Var a')), D, n, Sg. split.
        { eapply Stable_mono; [ | exact (stable_varvar D a a' n) ].
          intros f Hf. rewrite Hf. destruct (Atom.eq_dec a a'); [ congruence | ]. rewrite Ef. reflexivity. }
        exact (conj (Sem_sbT DT Sg D n a a' HK Hd (A2 a' ltac:(simpl; fsetdec)) Hteq) (Img_refl Sg)).
      * exists (sbT a' (typ_Var a)), D, n, Sg. split.
        { eapply Stable_mono; [ | exact (stable_varvar D a a' n) ].
          intros f Hf. rewrite Hf. destruct (Atom.eq_dec a a'); [ congruence | ]. rewrite Ef. reflexivity. }
        exact (conj (Sem_sbT DT Sg D n a' a HK Hd (A1 a ltac:(simpl; fsetdec)) (teqD_sym _ _ _ Hteq)) (Img_refl Sg)).
Qed.

(* The unifier W calls is complete on record-free types: given a substitution
   that respects the sorts and unifies the two types up to [teqD DT], it
   succeeds from some fuel on, and [Sg] factors through its result by an
   extension [S2] of [Sg] to the fresh variables. *)
Theorem unify_tD_rf_complete_img : forall (DT D : denv) Sg T1 T2 n,
  DOk D n -> KR D DT Sg -> rf T1 -> rf T2 ->
  (forall x, x `in` ftv_typ T1 -> old n x) -> (forall x, x `in` ftv_typ T2 -> old n x) ->
  teqD DT (apT Sg T1) (apT Sg T2) ->
  exists s D' n' S2, Stable (fun f => unify_tD f D T1 T2 n = Some (s, D', n')) /\
    Sem DT Sg n s D' n' S2 /\ Img Sg S2.
Proof.
  intros DT D Sg T1 T2 n Hd HK C1 C2 A1 A2 Hteq.
  exact (unify_rf_complete_aux DT (Datatypes.S (tsz (apT Sg T1))) D Sg T1 T2 n
           (Nat.lt_succ_diag_r _) Hd HK C1 C2 A1 A2 Hteq).
Qed.

Theorem unify_tD_rf_complete : forall (DT D : denv) Sg T1 T2 n,
  DOk D n -> KR D DT Sg -> rf T1 -> rf T2 ->
  (forall x, x `in` ftv_typ T1 -> old n x) -> (forall x, x `in` ftv_typ T2 -> old n x) ->
  teqD DT (apT Sg T1) (apT Sg T2) ->
  exists s D' n' S2, Stable (fun f => unify_tD f D T1 T2 n = Some (s, D', n')) /\
    Sem DT Sg n s D' n' S2.
Proof.
  intros DT D Sg T1 T2 n Hd HK C1 C2 A1 A2 Hteq.
  destruct (unify_tD_rf_complete_img DT D Sg T1 T2 n Hd HK C1 C2 A1 A2 Hteq)
    as (s & D' & n' & S2 & St & Hs & _).
  exists s, D', n', S2. exact (conj St Hs).
Qed.

(* Given even images, the extension's images are even: the unifier adds no atom
   to those [Sg] already uses, which is the bound [OkS] asks of a step. *)
Corollary unify_tD_rf_complete_even : forall (DT D : denv) Sg T1 T2 n,
  DOk D n -> KR D DT Sg -> rf T1 -> rf T2 ->
  (forall x, x `in` ftv_typ T1 -> old n x) -> (forall x, x `in` ftv_typ T2 -> old n x) ->
  teqD DT (apT Sg T1) (apT Sg T2) -> (forall z, EvT (sT Sg z)) ->
  exists s D' n' S2, Stable (fun f => unify_tD f D T1 T2 n = Some (s, D', n')) /\
    Sem DT Sg n s D' n' S2 /\ forall y, EvT (sT S2 y).
Proof.
  intros DT D Sg T1 T2 n Hd HK C1 C2 A1 A2 Hteq Hev.
  destruct (unify_tD_rf_complete_img DT D Sg T1 T2 n Hd HK C1 C2 A1 A2 Hteq)
    as (s & D' & n' & S2 & St & Hs & Im).
  exists s, D', n', S2. exact (conj St (conj Hs (Img_bound EvT Sg S2 Im Hev))).
Qed.
