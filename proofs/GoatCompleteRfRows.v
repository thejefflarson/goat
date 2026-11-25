(* Completeness of algorithm W, stages 7.6k and 7.6l: the unifier on records with
   row variables and present entries, at sorted environments
   (docs/design/phase7-proof-plan.md).

   The fragment is [pf] types (base types, variables, arrows, records of rows
   with plain fields, presence entries and row variables) in which every
   presence entry is present under the substitution [Sg] ([ps]: the image of
   its presence is [Unit]).  The environment is the one [Sg] respects ([KR D DT
   Sg]: the sort of each variable's image, the kind of each row variable's image,
   the labels a row variable lacks) and satisfies two conditions on the sorts
   ([Dsrt]): the sorts of the row variables are [Any] or [Eq], and [Sg] sends no
   [Numeric] variable to a record.  A type variable has any sort.  [bind_prop]
   and [bind_row] push the sort of the variable they bind onto the variables of
   the type or row, renaming each coarser one to a fresh variable of the sort
   ([push_sort], [push_sort_r]); [Pkg] says the images of the old atoms are
   renamings of the old atoms to atoms below the new supply, except the one
   bound atom, and the extension [S2] of [Sg] to the fresh variables respects
   the new environment.  With every entry present no occurrence hides behind an
   absent entry, the guard and the field condition never bind, the unifier's
   normalization of rows is the identity ([nfR] at the environment for
   [unify_tD], [drop_abs] for [unify_t]), and the unifier is read at plain
   [teq]/[req].

   The two conditions on the sorts are what the presence variables ask.  Each
   presence entry of a type bound at sort [k] puts a presence variable under the
   sort ([fld]), whose image [Unit] satisfies [Any] and [Eq] only.  A row
   variable carries a sort onto the rows it is bound to, so its sort is [Any] or
   [Eq]; a type variable of sort [Numeric] or [Literal] is bound to a scalar
   (neither an arrow nor, at [Literal], a record), which has no variable to push
   the sort onto, and [Sg] sends no [Numeric] variable to a record, so no entry
   is under it.

   A tag group [typ_Grp w A] is in the fragment when its payload [A] is
   ([pf A]) and spells the group's parameters ([spn]: arrows ending in [Unit],
   every slot used by a tag).  [unify_tD] hands the payload to the plain
   unifier, which the induction runs beside it, so the group arm is the
   induction hypothesis on the payload at the same [Sg]: [nfT] does not enter a
   group, so nothing is normalized, and [tsz] falls from a group to its payload.

   Absent entries are the hypothesis this stage does not discharge; they are
   listed in the plan under what remains of 7.6.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatSound.
Require Import Goat.GoatSubst.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteRows.
Require Import Goat.GoatSatTeq.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteBindRow.
Require Import Goat.GoatCompleteRewrite.
Require Import Goat.GoatCompleteOcc.
Require Import Goat.GoatCompleteUnify.
Require Import Goat.GoatCompleteRf.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the environment ---- *)

(* The row kinds keep their lacks sets and their sorts are [Any] or [Eq]: a row
   variable's sort is pushed onto the presence variables of the rows it is bound to,
   and a presence variable's image [Unit] satisfies exactly these two sorts.  This is
   the Numeric presence hypothesis, on the rows: a row of sort [Numeric] or [Literal]
   is not in the fragment. *)
Definition Drow (D : denv) : Prop :=
  forall r, rk_sort (drk D r) = k_Any \/ rk_sort (drk D r) = k_Eq.

(* The sorts whose variables [NN] keeps off records. *)
Definition NQ (k : sort) : Prop := k = k_Numeric \/ k = k_Quot.

(* A type variable of sort [Numeric] or [Quot] is not sent to a record.  A record is
   [Numeric] or [Quot] only through its fields, and the presence variables of its
   entries would be pushed to that sort by [bind_prop], where [Unit] does not satisfy
   it.  Record division, which [/] allows on records, is outside the fragment: a
   [Quot] atom is never sent to a record. *)
Definition NN (D : denv) (S : sub) : Prop :=
  forall y, NQ (D y) -> forall R, sT S y <> typ_Record R.

(* What the sorts of the environment ask of a substitution, beyond [KR]. *)
Definition Dsrt (D : denv) (S : sub) : Prop := Drow D /\ NN D S.

Lemma Drow_rupd : forall D a K, Drow D -> (rk_sort K = k_Any \/ rk_sort K = k_Eq) -> Drow (rupd D a K).
Proof.
  intros D a K Hr Hk q. cbn [rupd drk]. destruct (Atom.eq_dec q a); [ exact Hk | apply Hr ].
Qed.

Lemma Drow_join : forall D r q, Drow D ->
  rk_sort (rk_join (drk D r) (drk D q)) = k_Any \/ rk_sort (rk_join (drk D r) (drk D q)) = k_Eq.
Proof.
  intros D r q Hr. unfold rk_join. cbn [rk_sort].
  destruct (finer_b (rk_sort (drk D r)) (rk_sort (drk D q))); apply Hr.
Qed.

Lemma push_sort_sorts : forall l D k n sp D' n',
  push_sort D k l n = (sp, D', n') -> forall y, D' y = D y \/ D' y = k.
Proof.
  induction l as [|b l IH]; intros D k n sp D' n' H y; cbn [push_sort] in H.
  - inversion H; subst. left. reflexivity.
  - destruct (finer_b (D b) k).
    + exact (IH _ _ _ _ _ _ H y).
    + destruct (finer_b k (D b));
        [ | destruct (push_sort D k l n) as [[s1 D1] n1] eqn:E1; inversion H; subst; exact (IH _ _ _ _ _ _ E1 y) ].
      destruct (push_sort (upd D (ea n) k) k l (S n)) as [[s1 D1] n1] eqn:E.
      inversion H; subst.
      destruct (IH _ _ _ _ _ _ E y) as [Hy|Hy]; [ | right; exact Hy ].
      rewrite Hy. cbn [upd dsort]. destruct (Atom.eq_dec y (ea n)); [ right; reflexivity | left; reflexivity ].
Qed.

Lemma push_sort_drow : forall l D k n sp D' n',
  push_sort D k l n = (sp, D', n') -> Drow D -> (k = k_Any \/ k = k_Eq) -> Drow D'.
Proof.
  intros l D k n sp D' n' H Hd Hk r. rewrite (push_sort_drk _ _ _ _ _ _ _ H). exact (Hd r).
Qed.

Lemma push_sort_r_drow : forall l D k n sr D' n',
  push_sort_r D k l n = (sr, D', n') -> Drow D -> (k = k_Any \/ k = k_Eq) -> Drow D'.
Proof.
  induction l as [|b l IH]; intros D k n sr D' n' H Hd Hk; cbn [push_sort_r] in H.
  - inversion H; subst. exact Hd.
  - destruct (finer_b (rk_sort (drk D b)) k).
    + exact (IH _ _ _ _ _ _ H Hd Hk).
    + destruct (finer_b k (rk_sort (drk D b))); [ | exact (IH _ _ _ _ _ _ H Hd Hk) ].
      destruct (push_sort_r (rupd D (ea n) (RK k (rk_lacks (drk D b)))) k l (S n))
        as [[s1 D1] n1] eqn:E.
      inversion H; subst. exact (IH _ _ _ _ _ _ E (Drow_rupd D (ea n) (RK k (rk_lacks (drk D b))) Hd Hk) Hk).
Qed.

(* [push_sort] leaves a variable whose sort is already as fine as [k] where it is, and
   changes a sort only to [k]. *)
Lemma push_sort_keeps : forall l D k n sp D' n',
  push_sort D k l n = (sp, D', n') -> forall x, finer_b (D x) k = true -> old n x -> sT sp x = typ_Var x.
Proof.
  induction l as [|b l IH]; intros D k n sp D' n' H x Hf Hx; cbn [push_sort] in H.
  - inversion H; subst. reflexivity.
  - destruct (finer_b (D b) k) eqn:Efb.
    + exact (IH _ _ _ _ _ _ H x Hf Hx).
    + destruct (finer_b k (D b));
        [ | destruct (push_sort D k l n) as [[s1 D1] n1] eqn:E1; inversion H; subst;
            change (apT s1 (sT (sbT b typ_Float) x) = typ_Var x); cbn [sT sbT];
            destruct (Atom.eq_dec x b) as [->|Hne];
            [ rewrite Efb in Hf; discriminate Hf | exact (IH _ _ _ _ _ _ E1 x Hf Hx) ] ].
      destruct (push_sort (upd D (ea n) k) k l (S n)) as [[s1 D1] n1] eqn:E.
      inversion H; subst.
      change (apT s1 (sT (sbT b (typ_Var (ea n))) x) = typ_Var x).
      cbn [sT sbT]. destruct (Atom.eq_dec x b) as [->|Hne].
      * rewrite Efb in Hf. discriminate Hf.
      * change (sT s1 x = typ_Var x). apply (IH _ _ _ _ _ _ E x).
        -- cbn [upd dsort]. destruct (Atom.eq_dec x (ea n)) as [E2|_]; [ exfalso; exact (Hx n (le_n n) E2) | exact Hf ].
        -- intros m Hm. apply Hx. lia.
Qed.

Lemma nq_old : forall D n y, DOk D n -> NQ (D y) -> old n y.
Proof.
  intros D n y Hd Hy m Hm E. subst y. rewrite (DOk_ea D n m Hd Hm) in Hy.
  destruct Hy as [Hy|Hy]; discriminate Hy.
Qed.

(* A record stays a record up to conversion, so a substitution that sends no variable
   of a sort to a record keeps to it across [teq]. *)
Lemma teq_not_record : forall X Y, teq X Y -> (forall R, X <> typ_Record R) -> forall R, Y <> typ_Record R.
Proof.
  intros X Y H HX R EY. pose proof (teq_thead _ _ H) as Hh. subst Y.
  destruct X; simpl in Hh; try discriminate Hh. exact (HX _ eq_refl).
Qed.

(* ---- atoms below the supply ---- *)

Definition atT (n : nat) (T : typ) : Prop :=
  (forall x, x `in` ftv_typ T -> old n x) /\ (forall q, q `in` frv_typ T -> old n q).

Definition atR (n : nat) (R : row) : Prop :=
  (forall x, x `in` ftv_row R -> old n x) /\ (forall q, q `in` frv_row R -> old n q).

Lemma atT_mono : forall n n' T, n <= n' -> atT n T -> atT n' T.
Proof.
  intros n n' T Hl [H1 H2]. split; intros x Hx;
    [ exact (old_le _ _ _ Hl (H1 x Hx)) | exact (old_le _ _ _ Hl (H2 x Hx)) ].
Qed.

Lemma atR_mono : forall n n' R, n <= n' -> atR n R -> atR n' R.
Proof.
  intros n n' R Hl [H1 H2]. split; intros x Hx;
    [ exact (old_le _ _ _ Hl (H1 x Hx)) | exact (old_le _ _ _ Hl (H2 x Hx)) ].
Qed.

Lemma old_ea : forall n m, m < n -> old n (ea m).
Proof. intros n m Hm k Hk E. apply ea_inj in E. lia. Qed.

Lemma atT_ap : forall n' s T,
  (forall x, x `in` ftv_typ T -> atT n' (sT s x)) ->
  (forall q, q `in` frv_typ T -> atR n' (sR s q)) -> atT n' (apT s T).
Proof.
  intros n' s T Hx Hq. split.
  - intros y Hy. destruct (ftv_ap_typ _ _ _ _ Hy) as [[b [Hb Hyb]]|[p [Hp Hyp]]];
      [ exact (proj1 (Hx b Hb) y Hyb) | exact (proj1 (Hq p Hp) y Hyp) ].
  - intros y Hy. destruct (frv_ap_typ _ _ _ _ Hy) as [[b [Hb Hyb]]|[p [Hp Hyp]]];
      [ exact (proj2 (Hx b Hb) y Hyb) | exact (proj2 (Hq p Hp) y Hyp) ].
Qed.

Lemma atR_ap : forall n' s R,
  (forall x, x `in` ftv_row R -> atT n' (sT s x)) ->
  (forall q, q `in` frv_row R -> atR n' (sR s q)) -> atR n' (apR s R).
Proof.
  intros n' s R Hx Hq. split.
  - intros y Hy. destruct (proj2 ftv_ap_mut _ _ _ _ Hy) as [[b [Hb Hyb]]|[p [Hp Hyp]]];
      [ exact (proj1 (Hx b Hb) y Hyb) | exact (proj1 (Hq p Hp) y Hyp) ].
  - intros y Hy. destruct (proj2 frv_ap_mut _ _ _ _ Hy) as [[b [Hb Hyb]]|[p [Hp Hyp]]];
      [ exact (proj2 (Hx b Hb) y Hyb) | exact (proj2 (Hq p Hp) y Hyp) ].
Qed.

(* ---- the fragment ---- *)

Lemma pf_lcb : (forall T, pf T -> forall k, lcb k T = true) /\
               (forall R, prf R -> forall k, lcrb k R = true).
Proof.
  apply typ_row_mutind; simpl; try (intros; reflexivity); try (intros; contradiction).
  - intros A IHA B IHB [HA HB] k. rewrite (IHA HA), (IHB HB). reflexivity.
  - intros R IH HR k. exact (IH HR k).
  - intros w B IH [HB _] k. exact (IH HB k).
  - intros l T IHT R IHR [HT HR] k. rewrite (IHT HT), (IHR HR). reflexivity.
  - intros l P IHP T IHT R IHR [HP [HT HR]] k. rewrite (IHP HP), (IHT HT), (IHR HR). reflexivity.
Qed.

Lemma pf_ap : forall s,
  (forall T, pf T -> (forall x, x `in` ftv_typ T -> pf (sT s x)) ->
     (forall q, q `in` frv_typ T -> prf (sR s q)) -> pf (apT s T)) /\
  (forall R, prf R -> (forall x, x `in` ftv_row R -> pf (sT s x)) ->
     (forall q, q `in` frv_row R -> prf (sR s q)) -> prf (apR s R)).
Proof.
  intros s. unfold apT, apR. apply typ_row_mutind; simpl; try (intros; exact I); try (intros; contradiction).
  - intros A IHA B IHB [HA HB] Hx Hq. split;
      [ apply IHA; [ exact HA | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]
      | apply IHB; [ exact HB | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ] ].
  - intros R IH HR Hx Hq. exact (IH HR Hx Hq).
  - intros a _ Hx Hq. apply Hx. fsetdec.
  - intros w B IH [HB Hn] Hx Hq. exact (conj (IH HB Hx Hq) (spn_ap _ _ B w 0 Hn)).
  - intros r _ Hx Hq. apply Hq. fsetdec.
  - intros l T IHT R IHR [HT HR] Hx Hq. split;
      [ apply IHT; [ exact HT | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]
      | apply IHR; [ exact HR | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ] ].
  - intros l P IHP T IHT R IHR [HP [HT HR]] Hx Hq. refine (conj _ (conj _ _));
      [ apply IHP; [ exact HP | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]
      | apply IHT; [ exact HT | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]
      | apply IHR; [ exact HR | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ] ].
Qed.

(* ---- every entry is present ---- *)

Fixpoint ps (S : sub) (T : typ) {struct T} : Prop :=
  match T with
  | typ_Arrow A B => ps S A /\ ps S B
  | typ_Record R => psr S R
  | typ_Grp _ A => ps S A
  | _ => True
  end
with psr (S : sub) (R : row) {struct R} : Prop :=
  match R with
  | row_Ext _ T R' => ps S T /\ psr S R'
  | row_Maybe _ P T R' => apT S P = typ_Unit /\ ps S T /\ psr S R'
  | _ => True
  end.

(* A presence that is [Unit] under [S] is [Unit] or a variable [S] sends to [Unit]. *)
Lemma pres_shape : forall S P, pf P -> apT S P = typ_Unit ->
  P = typ_Unit \/ exists v, P = typ_Var v /\ sT S v = typ_Unit.
Proof.
  intros S P HP E. destruct P; simpl in HP; try contradiction;
    try (unfold apT in E; simpl in E; discriminate E).
  - left. reflexivity.
  - right. exists a. split; [ reflexivity | exact E ].
Qed.

Lemma pres_not_abs : forall S P, pf P -> apT S P = typ_Unit -> is_abs P = false.
Proof.
  intros S P HP E. destruct (pres_shape S P HP E) as [-> | [v [-> _]]]; reflexivity.
Qed.

Lemma pres_frv : forall S P q, pf P -> apT S P = typ_Unit -> q `notin` frv_typ P.
Proof.
  intros S P q HP E. destruct (pres_shape S P HP E) as [-> | [v [-> _]]]; simpl; fsetdec.
Qed.

(* The substitution carries an entry's presence along when [S'] after [s] is [S] on its atoms. *)
Lemma ps_pull : forall S S' s,
  (forall T, pf T -> ps S T ->
     (forall x, x `in` ftv_typ T -> teq (sT S x) (apT S' (sT s x)) /\ ps S' (sT s x)) ->
     (forall q, q `in` frv_typ T -> psr S' (sR s q)) -> ps S' (apT s T)) /\
  (forall R, prf R -> psr S R ->
     (forall x, x `in` ftv_row R -> teq (sT S x) (apT S' (sT s x)) /\ ps S' (sT s x)) ->
     (forall q, q `in` frv_row R -> psr S' (sR s q)) -> psr S' (apR s R)).
Proof.
  intros S S' s. unfold apT, apR. apply typ_row_mutind; simpl; try (intros; exact I);
    try (intros; contradiction).
  - intros A IHA B IHB [HA HB] [PA PB] Hx Hq. split;
      [ apply IHA; [ exact HA | exact PA | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]
      | apply IHB; [ exact HB | exact PB | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ] ].
  - intros R IH HR PR Hx Hq. exact (IH HR PR Hx Hq).
  - intros a _ _ Hx Hq. exact (proj2 (Hx a ltac:(fsetdec))).
  - intros w B IH [HB _] PB Hx Hq. exact (IH HB PB Hx Hq).
  - intros r _ _ Hx Hq. exact (Hq r ltac:(fsetdec)).
  - intros l T IHT R IHR [HT HR] [PT PR] Hx Hq. split;
      [ apply IHT; [ exact HT | exact PT | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]
      | apply IHR; [ exact HR | exact PR | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ] ].
  - intros l P IHP T IHT R IHR [HP [HT HR]] [PP [PT PR]] Hx Hq. refine (conj _ (conj _ _)).
    + destruct (pres_shape S P HP PP) as [-> | [v [-> Hv]]]; [ reflexivity | ].
      simpl. pose proof (proj1 (Hx v ltac:(simpl; fsetdec))) as Ht. rewrite Hv in Ht.
      exact (teq_Unit_inv _ Ht).
    + apply IHT; [ exact HT | exact PT | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ].
    + apply IHR; [ exact HR | exact PR | intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ].
Qed.

(* Where every entry is present the unifier's normalization of rows does nothing. *)
Lemma ps_nf : forall D S,
  (forall T, pf T -> ps S T -> nfT D T = T) /\ (forall R, prf R -> psr S R -> nfR D R = R).
Proof.
  intros D S. apply typ_row_mutind; simpl; try (intros; reflexivity); try (intros; contradiction).
  - intros A IHA B IHB [HA HB] [PA PB]. rewrite (IHA HA PA), (IHB HB PB). reflexivity.
  - intros R IH HR PR. rewrite (IH HR PR). reflexivity.
  - intros l T IHT R IHR [HT HR] [PT PR]. rewrite (IHT HT PT), (IHR HR PR). reflexivity.
  - intros l P IHP T IHT R IHR [HP [HT HR]] [PP [PT PR]]. rewrite (IHR HR PR).
    rewrite (pres_not_abs S P HP PP). cbn [andb]. cbv iota.
    rewrite (IHT HT PT).
    destruct (pres_shape S P HP PP) as [-> | [v [-> _]]]; reflexivity.
Qed.

(* A variable that is not [Unit] under [S] and occurs in a type of the fragment occurs
   under present entries only. *)
Lemma ps_po : forall S a, sT S a <> typ_Unit ->
  (forall T, pf T -> ps S T -> a `in` ftv_typ T -> po S (eq a) (fun _ => False) T) /\
  (forall R, prf R -> psr S R -> a `in` ftv_row R -> por S (eq a) (fun _ => False) R).
Proof.
  intros S a Hne. apply typ_row_mutind; simpl; try (intros; exfalso; fsetdec); try (intros; contradiction).
  - intros A IHA B IHB [HA HB] [PA PB] Hin. apply AtomSetFacts.union_iff in Hin.
    destruct Hin as [H|H]; [ left; exact (IHA HA PA H) | right; exact (IHB HB PB H) ].
  - intros R IH HR PR Hin. exact (IH HR PR Hin).
  - intros b _ _ Hin. apply AtomSetFacts.singleton_iff in Hin. symmetry. exact Hin.
  - intros w B IH [HB _] PB Hin. exact (IH HB PB Hin).
  - intros l T IHT R IHR [HT HR] [PT PR] Hin. apply AtomSetFacts.union_iff in Hin.
    destruct Hin as [H|H]; [ left; exact (IHT HT PT H) | right; exact (IHR HR PR H) ].
  - intros l P IHP T IHT R IHR [HP [HT HR]] [PP [PT PR]] Hin.
    pose proof (pres_not_abs S P HP PP) as Hna.
    assert (Hap : is_abs (apT S P) = false) by (rewrite PP; reflexivity).
    apply AtomSetFacts.union_iff in Hin. destruct Hin as [Hin|Hin].
    + exfalso. destruct (pres_shape S P HP PP) as [-> | [v [-> Hv]]]; simpl in Hin; [ fsetdec | ].
      apply AtomSetFacts.singleton_iff in Hin. subst. exact (Hne Hv).
    + apply AtomSetFacts.union_iff in Hin. destruct Hin as [Hin|Hin];
        [ left; exact (conj Hap (IHT HT PT Hin)) | right; exact (IHR HR PR Hin) ].
Qed.

(* The same for a row variable. *)
Lemma ps_pos : forall S r,
  (forall T, pf T -> ps S T -> r `in` frv_typ T -> po S (fun _ => False) (eq r) T) /\
  (forall R, prf R -> psr S R -> r `in` frv_row R -> por S (fun _ => False) (eq r) R).
Proof.
  intros S r. apply typ_row_mutind; simpl; try (intros; exfalso; fsetdec); try (intros; contradiction).
  - intros A IHA B IHB [HA HB] [PA PB] Hin. apply AtomSetFacts.union_iff in Hin.
    destruct Hin as [H|H]; [ left; exact (IHA HA PA H) | right; exact (IHB HB PB H) ].
  - intros R IH HR PR Hin. exact (IH HR PR Hin).
  - intros w B IH [HB _] PB Hin. exact (IH HB PB Hin).
  - intros q _ _ Hin. apply AtomSetFacts.singleton_iff in Hin. symmetry. exact Hin.
  - intros l T IHT R IHR [HT HR] [PT PR] Hin. apply AtomSetFacts.union_iff in Hin.
    destruct Hin as [H|H]; [ left; exact (IHT HT PT H) | right; exact (IHR HR PR H) ].
  - intros l P IHP T IHT R IHR [HP [HT HR]] [PP [PT PR]] Hin.
    assert (Hap : is_abs (apT S P) = false) by (rewrite PP; reflexivity).
    apply AtomSetFacts.union_iff in Hin. destruct Hin as [Hin|Hin].
    + exfalso. exact (pres_frv S P r HP PP Hin).
    + apply AtomSetFacts.union_iff in Hin. destruct Hin as [Hin|Hin];
        [ left; exact (conj Hap (IHT HT PT Hin)) | right; exact (IHR HR PR Hin) ].
Qed.

(* A row with an entry and a variable in it has the variable behind a present entry. *)
Lemma ps_pos_row : forall S r R, prf R -> psr S R -> r `in` frv_row R ->
  (forall q, R <> row_Var q) -> pos S (fun _ => False) (eq r) R.
Proof.
  intros S r R HR PR Hin Hnv. pose proof (proj2 (ps_pos S r) R HR PR Hin) as Hp.
  destruct R as [ | q | l T R' | l P T R' ]; simpl in *.
  - fsetdec.
  - exfalso. exact (Hnv q eq_refl).
  - exact Hp.
  - destruct PR as [PP _]. assert (Hap : is_abs (apT S P) = false) by (rewrite PP; reflexivity).
    left. split; [ exact Hap | ]. destruct Hp as [[_ H]|H]; [ left; exact H | right; exact H ].
Qed.

Section Sorted.

Variable DT : denv.

(* ---- what a step promises the next one ---- *)

(* [s] is the step's substitution, [S2] extends [Sg] to its fresh variables: the
   supply grows, [S2] respects the environment the step returns, the images of
   the old atoms are in the fragment over atoms below the new supply with every
   entry present under [S2], [Sg] factors through [s] by [S2], and [S2]
   mentions no atom [Sg]'s images do not ([Cov]).  [Cov] is what bounds the
   atoms of [S2]'s images by a bound on [Sg]'s: it holds although the field a
   row variable is bound to is only [teq] to a field of [Sg]'s image, because
   [rewrite_row_var_canon] picks the canonical representative. *)
Definition Pkg (Sg : sub) (n : nat) (s : sub) (D' : denv) (n' : nat) (S2 : sub) : Prop :=
  n <= n' /\ DOk D' n' /\ Dsrt D' S2 /\ KR D' DT S2 /\
  (forall x, old n x -> pf (sT s x) /\ atT n' (sT s x) /\ ps S2 (sT s x) /\
     teq (sT Sg x) (apT S2 (sT s x))) /\
  (forall q, old n q -> prf (sR s q) /\ atR n' (sR s q) /\ psr S2 (sR s q) /\
     req (sR Sg q) (apR S2 (sR s q))) /\
  Cov Sg S2.

Lemma Pkg_id : forall Sg D n, DOk D n -> Dsrt D Sg -> KR D DT Sg -> Pkg Sg n sid D n Sg.
Proof.
  intros Sg D n Hd Ht Hk. refine (conj (le_n n) (conj Hd (conj Ht (conj Hk (conj _ (conj _ (Cov_refl Sg))))))).
  - intros x Hx. cbn [sT sid idt]. refine (conj I (conj _ (conj I (teq_refl _)))).
    split; intros y Hy; simpl in Hy; [ | fsetdec ].
    apply AtomSetFacts.singleton_iff in Hy. subst. exact Hx.
  - intros q Hq. cbn [sR sid idr]. refine (conj I (conj _ (conj I (req_refl _)))).
    split; intros y Hy; simpl in Hy; [ fsetdec | ].
    apply AtomSetFacts.singleton_iff in Hy. subst. exact Hq.
Qed.

Lemma ap_factor_row : forall Sg S2 s R,
  (forall x, x `in` ftv_row R -> teq (sT Sg x) (apT S2 (sT s x))) ->
  (forall q, q `in` frv_row R -> req (sR Sg q) (apR S2 (sR s q))) ->
  req (apR Sg R) (apR S2 (apR s R)).
Proof.
  intros Sg S2 s R Hx Hq. rewrite apR_comp.
  exact (proj2 (ap_cong_on Sg (scomp S2 s)) R Hx Hq).
Qed.

Lemma pkg_ap_T : forall Sg n s D' n' S2 T, Pkg Sg n s D' n' S2 -> pf T -> atT n T -> ps Sg T ->
  pf (apT s T) /\ atT n' (apT s T) /\ ps S2 (apT s T).
Proof.
  intros Sg n s D' n' S2 T (Hl & Hd & Ht & Hk & Hx & Hq & _) HT [A1 A2] PT.
  refine (conj _ (conj _ _)).
  - apply (proj1 (pf_ap s)); [ exact HT | intros x Hx'; exact (proj1 (Hx x (A1 x Hx')))
                              | intros q Hq'; exact (proj1 (Hq q (A2 q Hq'))) ].
  - apply atT_ap; [ intros x Hx'; exact (proj1 (proj2 (Hx x (A1 x Hx'))))
                  | intros q Hq'; exact (proj1 (proj2 (Hq q (A2 q Hq')))) ].
  - apply (proj1 (ps_pull Sg S2 s)); [ exact HT | exact PT
      | intros x Hx'; destruct (Hx x (A1 x Hx')) as (_ & _ & P & F); exact (conj F P)
      | intros q Hq'; exact (proj1 (proj2 (proj2 (Hq q (A2 q Hq'))))) ].
Qed.

Lemma pkg_ap_R : forall Sg n s D' n' S2 R, Pkg Sg n s D' n' S2 -> prf R -> atR n R -> psr Sg R ->
  prf (apR s R) /\ atR n' (apR s R) /\ psr S2 (apR s R).
Proof.
  intros Sg n s D' n' S2 R (Hl & Hd & Ht & Hk & Hx & Hq & _) HR [A1 A2] PR.
  refine (conj _ (conj _ _)).
  - apply (proj2 (pf_ap s)); [ exact HR | intros x Hx'; exact (proj1 (Hx x (A1 x Hx')))
                              | intros q Hq'; exact (proj1 (Hq q (A2 q Hq'))) ].
  - apply atR_ap; [ intros x Hx'; exact (proj1 (proj2 (Hx x (A1 x Hx'))))
                  | intros q Hq'; exact (proj1 (proj2 (Hq q (A2 q Hq')))) ].
  - apply (proj2 (ps_pull Sg S2 s)); [ exact HR | exact PR
      | intros x Hx'; destruct (Hx x (A1 x Hx')) as (_ & _ & P & F); exact (conj F P)
      | intros q Hq'; exact (proj1 (proj2 (proj2 (Hq q (A2 q Hq'))))) ].
Qed.

Lemma pkg_fac_T : forall Sg n s D' n' S2 T, Pkg Sg n s D' n' S2 -> atT n T ->
  teq (apT Sg T) (apT S2 (apT s T)).
Proof.
  intros Sg n s D' n' S2 T (Hl & Hd & Ht & Hk & Hx & Hq & _) [A1 A2].
  apply ap_factor; [ intros x Hx'; exact (proj2 (proj2 (proj2 (Hx x (A1 x Hx')))))
                   | intros q Hq'; exact (proj2 (proj2 (proj2 (Hq q (A2 q Hq'))))) ].
Qed.

Lemma pkg_fac_R : forall Sg n s D' n' S2 R, Pkg Sg n s D' n' S2 -> atR n R ->
  req (apR Sg R) (apR S2 (apR s R)).
Proof.
  intros Sg n s D' n' S2 R (Hl & Hd & Ht & Hk & Hx & Hq & _) [A1 A2].
  apply ap_factor_row; [ intros x Hx'; exact (proj2 (proj2 (proj2 (Hx x (A1 x Hx')))))
                       | intros q Hq'; exact (proj2 (proj2 (proj2 (Hq q (A2 q Hq'))))) ].
Qed.

Lemma Pkg_comp : forall Sg n s1 D1 n1 S2 s2 D2 n2 S3,
  Pkg Sg n s1 D1 n1 S2 -> Pkg S2 n1 s2 D2 n2 S3 -> Pkg Sg n (scomp s2 s1) D2 n2 S3.
Proof.
  intros Sg n s1 D1 n1 S2 s2 D2 n2 S3 P1 P2.
  destruct P1 as (Hl1 & Hd1 & Ht1 & Hk1 & Hx1 & Hq1 & Cv1).
  assert (P2' := P2). destruct P2 as (Hl2 & Hd2 & Ht2 & Hk2 & Hx2 & Hq2 & Cv2).
  refine (conj (Nat.le_trans _ _ _ Hl1 Hl2) (conj Hd2 (conj Ht2 (conj Hk2 (conj _ (conj _ (Cov_trans _ _ _ Cv1 Cv2))))))).
  - intros x Hx. destruct (Hx1 x Hx) as (Hpf & Hat & Hps & Hf).
    change (pf (apT s2 (sT s1 x)) /\ atT n2 (apT s2 (sT s1 x)) /\ ps S3 (apT s2 (sT s1 x)) /\
            teq (sT Sg x) (apT S3 (apT s2 (sT s1 x)))).
    destruct (pkg_ap_T S2 n1 s2 D2 n2 S3 _ P2' Hpf Hat Hps) as (A & B & C).
    refine (conj A (conj B (conj C _))).
    exact (teq_trans _ _ _ Hf (pkg_fac_T S2 n1 s2 D2 n2 S3 _ P2' Hat)).
  - intros q Hq. destruct (Hq1 q Hq) as (Hpf & Hat & Hps & Hf).
    change (prf (apR s2 (sR s1 q)) /\ atR n2 (apR s2 (sR s1 q)) /\ psr S3 (apR s2 (sR s1 q)) /\
            req (sR Sg q) (apR S3 (apR s2 (sR s1 q)))).
    destruct (pkg_ap_R S2 n1 s2 D2 n2 S3 _ P2' Hpf Hat Hps) as (A & B & C).
    refine (conj A (conj B (conj C _))).
    exact (req_trans _ _ _ Hf (pkg_fac_R S2 n1 s2 D2 n2 S3 _ P2' Hat)).
Qed.

(* ---- the field condition holds when every entry is present ---- *)

Lemma ps_pres : forall S P, pf P -> apT S P = typ_Unit -> ps S P.
Proof.
  intros S P HP E. destruct (pres_shape S P HP E) as [-> | [v [-> _]]]; exact I.
Qed.

(* With every entry present, the field condition at [Any] or [Eq] has nothing to say:
   no entry is absent, and a presence variable's image [Unit] satisfies both sorts. *)
Lemma ps_fld : forall S k, (k = k_Any \/ k = k_Eq) ->
  (forall T, pf T -> ps S T -> fld DT S k T) /\ (forall R, prf R -> psr S R -> frld DT S k R).
Proof.
  intros S k Hk. apply typ_row_mutind; simpl; try (intros; exact I); try (intros; contradiction).
  - intros A IHA B IHB [HA HB] [PA PB]. exact (conj (IHA HA PA) (IHB HB PB)).
  - intros R IH HR PR. exact (IH HR PR).
  - intros w B IH [HB _] PB. exact (IH HB PB).
  - intros l T IHT R IHR [HT HR] [PT PR]. exact (conj (IHT HT PT) (IHR HR PR)).
  - intros l P IHP T IHT R IHR [HP [HT HR]] [PP [PT PR]].
    refine (conj _ (conj _ (conj (IHP HP (ps_pres S P HP PP)) (conj (IHT HT PT) (IHR HR PR))))).
    + intros H. rewrite PP in H. discriminate H.
    + rewrite PP. exact Hk.
Qed.

(* A row whose entries are all present under [Sg] never mentions a label its kind lacks:
   the kind's lacks set is respected by [Sg r], so [bind_row] finds nothing to make
   absent. *)
Lemma ps_lacks : forall Sg K R, prf R -> psr Sg R -> LK DT K (apR Sg R) ->
  abs_vars K R = nil.
Proof.
  intros Sg K R. induction R as [ | r | l T R IH | l P T R IH ]; intros HR PR HL.
  - reflexivity.
  - reflexivity.
  - rewrite apR_Ext in HL. pose proof (IH (proj2 HR) (proj2 PR) (LK_ext _ _ _ _ _ HL)) as H1.
    cbn [abs_vars]. exact H1.
  - destruct HR as [HP [HT HR']]. destruct PR as [PP [PT PR']].
    rewrite apR_Maybe in HL. pose proof (IH HR' PR' (LK_maybe _ _ _ _ _ _ HL)) as H1.
    assert (Hk : rk_lacks K l = false).
    { destruct (rk_lacks K l) eqn:Ek; [ | reflexivity ]. exfalso.
      pose proof (HL l Ek) as H. cbn [rlacksD] in H. rewrite Nat.eqb_refl in H.
      apply andb_prop in H. destruct H as [H _].
      change (ap_typ (sT Sg) (sR Sg) P) with (apT Sg P) in H. rewrite PP in H. discriminate H. }
    destruct P; cbn [abs_vars]; try rewrite Hk; exact H1.
Qed.

(* ---- renamings by fresh atoms ---- *)

(* [RenN n n' r]: [r] sends each atom below [n] to itself or to a fresh atom in [n, n'). *)
Definition RenN (n n' : nat) (r : sub) : Prop :=
  n <= n' /\
  (forall x, old n x -> exists y, sT r x = typ_Var y /\
     (y = x \/ exists m, n <= m /\ m < n' /\ y = ea m)) /\
  (forall q, old n q -> exists q', sR r q = row_Var q' /\
     (q' = q \/ exists m, n <= m /\ m < n' /\ q' = ea m)).

Lemma RenN_id : forall n, RenN n n sid.
Proof.
  intros n. refine (conj (le_n n) (conj _ _)).
  - intros x _. exists x. split; [ reflexivity | left; reflexivity ].
  - intros q _. exists q. split; [ reflexivity | left; reflexivity ].
Qed.

Lemma old_ren : forall n n' x y, n <= n' -> old n x ->
  (y = x \/ exists m, n <= m /\ m < n' /\ y = ea m) -> old n' y.
Proof.
  intros n n' x y Hl Hx [->|[m [H1 [H2 ->]]]]; [ exact (old_le n n' _ Hl Hx) | exact (old_ea n' m H2) ].
Qed.

Lemma RenN_comp : forall n n1 n2 r1 r2, RenN n n1 r1 -> RenN n1 n2 r2 -> RenN n n2 (scomp r2 r1).
Proof.
  intros n n1 n2 r1 r2 (Hl1 & T1 & R1) (Hl2 & T2 & R2).
  refine (conj (Nat.le_trans _ _ _ Hl1 Hl2) (conj _ _)).
  - intros x Hx. destruct (T1 x Hx) as (y & Ey & Hy).
    destruct (T2 y (old_ren n n1 x y Hl1 Hx Hy)) as (z & Ez & Hz).
    exists z. split.
    + change (apT r2 (sT r1 x) = typ_Var z). rewrite Ey. exact Ez.
    + destruct Hz as [Hz|[m [H1 [H2 H3]]]].
      * destruct Hy as [Hy|[m [H1 [H2 H3]]]].
        -- left. rewrite Hz, Hy. reflexivity.
        -- right. exists m. split; [ exact H1 | split; [ lia | rewrite Hz; exact H3 ] ].
      * right. exists m. split; [ lia | split; [ exact H2 | exact H3 ] ].
  - intros q Hq. destruct (R1 q Hq) as (y & Ey & Hy).
    destruct (R2 y (old_ren n n1 q y Hl1 Hq Hy)) as (z & Ez & Hz).
    exists z. split.
    + change (apR r2 (sR r1 q) = row_Var z). rewrite Ey. exact Ez.
    + destruct Hz as [Hz|[m [H1 [H2 H3]]]].
      * destruct Hy as [Hy|[m [H1 [H2 H3]]]].
        -- left. rewrite Hz, Hy. reflexivity.
        -- right. exists m. split; [ exact H1 | split; [ lia | rewrite Hz; exact H3 ] ].
      * right. exists m. split; [ lia | split; [ exact H2 | exact H3 ] ].
Qed.

Lemma RenN_push : forall l D k n sp D' n',
  push_sort D k l n = (sp, D', n') -> (forall c, In c l -> old n c) -> allcmp D k l -> RenN n n' sp.
Proof.
  intros l D k n sp D' n' H Hold Hall.
  destruct (push_sort_facts _ _ _ _ _ _ _ H Hold) as (P1 & P2 & P3 & P4' & _ & _).
  pose proof (P4' Hall) as P4.
  refine (conj P2 (conj _ _)).
  - intros x _. destruct (P4 x) as (y & Ey & _). exists y. split; [ exact Ey | ].
    exact (push_sort_new _ _ _ _ _ _ _ H Hold x y Ey).
  - intros q _. exists q. split; [ exact (P1 q) | left; reflexivity ].
Qed.

Lemma RenN_push_r : forall l D k n sr D' n',
  push_sort_r D k l n = (sr, D', n') -> (forall c, In c l -> old n c) -> RenN n n' sr.
Proof.
  intros l D k n sr D' n' H Hold.
  destruct (push_sort_r_facts _ _ _ _ _ _ _ H Hold) as (Q1 & Q2 & _ & _ & Q5 & _ & _).
  refine (conj Q2 (conj _ _)).
  - intros x _. exists x. split; [ exact (Q1 x) | left; reflexivity ].
  - intros q Hq. destruct (Q5 q) as (q' & Eq'). exists q'. split; [ exact Eq' | ].
    exact (push_sort_r_new _ _ _ _ _ _ _ H Hold q q' Hq Eq').
Qed.

Lemma RenN_tail : forall n q, RenN n (S n) (sbR q (row_Var (ea n))).
Proof.
  intros n q. refine (conj (le_S n n (le_n n)) (conj _ _)).
  - intros x _. exists x. split; [ reflexivity | left; reflexivity ].
  - intros q0 _. cbn [sR sbR]. destruct (Atom.eq_dec q0 q) as [_|_].
    + exists (ea n). split; [ reflexivity | right; exists n; split; [ apply le_n | split; [ lia | reflexivity ] ] ].
    + exists q0. split; [ reflexivity | left; reflexivity ].
Qed.

Lemma atT_V : forall n y, old n y -> atT n (typ_Var y).
Proof.
  intros n y Hy. split; simpl; intros z Hz; [ | fsetdec ].
  apply AtomSetFacts.singleton_iff in Hz. subst. exact Hy.
Qed.

Lemma atR_V : forall n y, old n y -> atR n (row_Var y).
Proof.
  intros n y Hy. split; simpl; intros z Hz; [ fsetdec | ].
  apply AtomSetFacts.singleton_iff in Hz. subst. exact Hy.
Qed.

(* A type or row of the fragment keeps its place under a renaming. *)
Lemma ren_ap_T : forall n n' rho T, RenN n n' rho -> pf T -> atT n T ->
  pf (apT rho T) /\ atT n' (apT rho T).
Proof.
  intros n n' rho T (Hl & Rt & Rr) PT [A1 A2]. split.
  - apply (proj1 (pf_ap rho)); [ exact PT | | ].
    + intros x Hx. destruct (Rt x (A1 x Hx)) as (y & Ey & _). rewrite Ey. exact I.
    + intros q Hq. destruct (Rr q (A2 q Hq)) as (q' & Eq' & _). rewrite Eq'. exact I.
  - apply atT_ap.
    + intros x Hx. destruct (Rt x (A1 x Hx)) as (y & Ey & Hy). rewrite Ey.
      exact (atT_V n' y (old_ren n n' x y Hl (A1 x Hx) Hy)).
    + intros q Hq. destruct (Rr q (A2 q Hq)) as (q' & Eq' & Hq'). rewrite Eq'.
      exact (atR_V n' q' (old_ren n n' q q' Hl (A2 q Hq) Hq')).
Qed.

Lemma ren_ap_R : forall n n' rho R, RenN n n' rho -> prf R -> atR n R ->
  prf (apR rho R) /\ atR n' (apR rho R).
Proof.
  intros n n' rho R (Hl & Rt & Rr) PR [A1 A2]. split.
  - apply (proj2 (pf_ap rho)); [ exact PR | | ].
    + intros x Hx. destruct (Rt x (A1 x Hx)) as (y & Ey & _). rewrite Ey. exact I.
    + intros q Hq. destruct (Rr q (A2 q Hq)) as (q' & Eq' & _). rewrite Eq'. exact I.
  - apply atR_ap.
    + intros x Hx. destruct (Rt x (A1 x Hx)) as (y & Ey & Hy). rewrite Ey.
      exact (atT_V n' y (old_ren n n' x y Hl (A1 x Hx) Hy)).
    + intros q Hq. destruct (Rr q (A2 q Hq)) as (q' & Eq' & Hq'). rewrite Eq'.
      exact (atR_V n' q' (old_ren n n' q q' Hl (A2 q Hq) Hq')).
Qed.

(* The presence of every entry is carried along a renaming by [S2] when [S2] after the
   renaming is [Sg] on the atoms. *)
Lemma ren_ps_T : forall Sg S2 rho n n' T, RenN n n' rho -> pf T -> atT n T -> ps Sg T ->
  (forall x, x `in` ftv_typ T -> teq (sT Sg x) (apT S2 (sT rho x))) -> ps S2 (apT rho T).
Proof.
  intros Sg S2 rho n n' T (Hl & Rt & Rr) PT [A1 A2] PS Hf.
  apply (proj1 (ps_pull Sg S2 rho)); [ exact PT | exact PS | | ].
  - intros x Hx. destruct (Rt x (A1 x Hx)) as (y & Ey & _).
    refine (conj (Hf x Hx) _). rewrite Ey. exact I.
  - intros q Hq. destruct (Rr q (A2 q Hq)) as (q' & Eq' & _). rewrite Eq'. exact I.
Qed.

Lemma ren_ps_R : forall Sg S2 rho n n' R, RenN n n' rho -> prf R -> atR n R -> psr Sg R ->
  (forall x, x `in` ftv_row R -> teq (sT Sg x) (apT S2 (sT rho x))) -> psr S2 (apR rho R).
Proof.
  intros Sg S2 rho n n' R (Hl & Rt & Rr) PR [A1 A2] PS Hf.
  apply (proj2 (ps_pull Sg S2 rho)); [ exact PR | exact PS | | ].
  - intros x Hx. destruct (Rt x (A1 x Hx)) as (y & Ey & _).
    refine (conj (Hf x Hx) _). rewrite Ey. exact I.
  - intros q Hq. destruct (Rr q (A2 q Hq)) as (q' & Eq' & _). rewrite Eq'. exact I.
Qed.

(* ---- binding a type variable ---- *)

Lemma ps_na : forall Sg,
  (forall T, pf T -> ps Sg T -> na T = true) /\
  (forall R, prf R -> psr Sg R -> nar R = true).
Proof.
  intros Sg. apply typ_row_mutind; cbn [pf prf ps psr na nar].
  - intros _ _. reflexivity.
  - intros _ _. reflexivity.
  - intros _ _. reflexivity.
  - intros _ _. reflexivity.
  - intros _ _. reflexivity.
  - intros A IHA B IHB [HA HB] [PA PB]. rewrite (IHA HA PA), (IHB HB PB). reflexivity.
  - intros R IH H1 H2. exact (IH H1 H2).
  - intros a _ _. reflexivity.
  - intros i H. contradiction.
  - intros B IH H. contradiction.
  - intros w A IH [HA _] PA. exact (IH HA PA).
  - intros _ _. reflexivity.
  - intros r _ _. reflexivity.
  - intros l T IHT R IHR [HT HR] [PT PR]. rewrite (IHT HT PT), (IHR HR PR). reflexivity.
  - intros l P IHP T IHT R IHR [HP [HT HR]] [PU [PT PR]].
    rewrite (pres_not_abs Sg P HP PU), (IHT HT PT), (IHR HR PR). cbn [negb andb].
    destruct (pres_shape Sg P HP PU) as [->|[v [-> _]]]; reflexivity.
Qed.

Lemma bind_prop_unfold : forall D a T n s D' n',
  bind_prop0 D a T n = Some (s, D', n') -> na T = true ->
  exists sp D1 n1 sr,
    push_sort D (D a) (AtomSetImpl.elements (ftv_typ T)) n = (sp, D1, n1) /\
    push_sort_r D1 (D1 a) (AtomSetImpl.elements (frv_typ T)) n1 = (sr, D', n') /\
    s = scomp (sbT a (apT sr (apT sp T))) (scomp sr sp).
Proof.
  intros D a T n s D' n' H Hna. unfold bind_prop0 in H.
  destruct ((proj1 na_live_mut) T Hna) as [Hlt Hlr]. rewrite Hlt, Hlr in H.
  destruct (occT a T); [ discriminate | ].
  destruct (push_sort D (D a) (AtomSetImpl.elements (ftv_typ T)) n) as [[sp D1] n1] eqn:E1.
  destruct (push_sort_r D1 (D1 a) (AtomSetImpl.elements (frv_typ T)) n1) as [[sr D2] n2] eqn:E2.
  cbv zeta in H.
  destruct (occT a (apT sr (apT sp T))); [ discriminate | ].
  destruct (sat_b D2 (D2 a) (apT sr (apT sp T))); [ | discriminate ].
  inversion H; subst. exists sp, D1, n1, sr. repeat split; first [ assumption | reflexivity ].
Qed.

(* The step that binds [a] to [T] renamed by [rho]: the images of the old atoms are
   renamings, except [a], whose image is the renamed type. *)
Lemma pkg_close_T : forall Sg S2 n n' a T rho s,
  RenN n n' rho -> old n a -> pf T -> atT n T -> ps Sg T -> a `notin` ftv_typ T ->
  (forall x, sT s x = apT (sbT a (apT rho T)) (sT rho x)) ->
  (forall q, sR s q = apR (sbT a (apT rho T)) (sR rho q)) ->
  (forall x, old n x -> teq (sT Sg x) (apT S2 (sT s x))) ->
  (forall q, old n q -> req (sR Sg q) (apR S2 (sR s q))) ->
  (forall x, old n x -> pf (sT s x) /\ atT n' (sT s x) /\ ps S2 (sT s x) /\
     teq (sT Sg x) (apT S2 (sT s x))) /\
  (forall q, old n q -> prf (sR s q) /\ atR n' (sR s q) /\ psr S2 (sR s q) /\
     req (sR Sg q) (apR S2 (sR s q))).
Proof.
  intros Sg S2 n n' a T rho s Rho Ha HT AT PT Hna Hsx Hsr Fx Fr.
  pose proof Rho as (Hl & Rt & Rr).
  destruct (ren_ap_T n n' rho T Rho HT AT) as [P1 A1].
  assert (Hother : forall x, x `in` ftv_typ T -> sT s x = sT rho x).
  { intros x Hx. rewrite (Hsx x). destruct (Rt x (proj1 AT x Hx)) as (y & Ey & Hy). rewrite Ey.
    change (apT (sbT a (apT rho T)) (typ_Var y)) with (sT (sbT a (apT rho T)) y). cbn [sT sbT].
    destruct (Atom.eq_dec y a) as [Hya|Hya]; [ exfalso | reflexivity ].
    destruct Hy as [Hyx|[m [H1 [H2 H3]]]].
    - apply Hna. rewrite <- Hya, Hyx. exact Hx.
    - exact (Ha m H1 (eq_trans (eq_sym Hya) H3)). }
  assert (PS : ps S2 (apT rho T)).
  { refine (ren_ps_T Sg S2 rho n n' T Rho HT AT PT _). intros x Hx.
    pose proof (Fx x (proj1 AT x Hx)) as F. rewrite (Hother x Hx) in F. exact F. }
  split.
  - intros x Hx. destruct (Rt x Hx) as (y & Ey & Hy).
    pose proof (Fx x Hx) as F.
    assert (Esx : sT s x = if Atom.eq_dec y a then apT rho T else typ_Var y).
    { rewrite (Hsx x), Ey.
      change (apT (sbT a (apT rho T)) (typ_Var y)) with (sT (sbT a (apT rho T)) y). cbn [sT sbT]. reflexivity. }
    rewrite Esx in F |- *.
    revert F. destruct (Atom.eq_dec y a) as [Hya|Hya]; intro F.
    + exact (conj P1 (conj A1 (conj PS F))).
    + exact (conj I (conj (atT_V n' y (old_ren n n' x y Hl Hx Hy)) (conj I F))).
  - intros q Hq. destruct (Rr q Hq) as (q' & Eq' & Hq').
    assert (Esr : sR s q = row_Var q').
    { rewrite (Hsr q), Eq'.
      change (apR (sbT a (apT rho T)) (row_Var q')) with (sR (sbT a (apT rho T)) q'). reflexivity. }
    pose proof (Fr q Hq) as F. rewrite Esr in F |- *.
    exact (conj I (conj (atR_V n' q' (old_ren n n' q q' Hl Hq Hq')) (conj I F))).
Qed.

(* A variable of sort [Any] or [Eq] bound to a type of the fragment: the sort is
   pushed onto the variables of the type, which are renamed to fresh ones. *)
Lemma pkg_bind_prop_ae : forall (D : denv) Sg a T n,
  DOk D n -> Dsrt D Sg -> KR D DT Sg -> old n a -> pf T -> atT n T -> ps Sg T ->
  a `notin` ftv_typ T -> (D a = k_Any \/ D a = k_Eq) -> teq (sT Sg a) (apT Sg T) ->
  exists s D' n' S2, bind_prop D a T n = Some (s, D', n') /\ Pkg Sg n s D' n' S2.
Proof.
  intros D Sg a T n Hd Hs Hk Ha HT AT PT Hocc HaE Heq.
  assert (Hlc : lcb 0 T = true) by exact (proj1 pf_lcb T HT 0).
  assert (Hfld : fld DT Sg (D a) T) by exact (proj1 (ps_fld Sg (D a) HaE) T HT PT).
  assert (Hna : na T = true) by exact (proj1 (ps_na Sg) T HT PT).
  destruct (bind_prop0_sorted_complete false D DT Sg a T n Hd Hk Ha Hocc (proj1 AT) (proj2 AT)
              (fun b _ => cmpb_any_eq _ _ HaE) (fun q _ => cmpb_any_eq _ _ HaE) HT Hlc Hna Hfld Heq)
    as (s & D' & n' & S2 & E & Hk' & Hl & Hd' & Fx & Fr & _ & Cv).
  destruct (bind_prop_unfold D a T n s D' n' E Hna) as (sp & D1 & n1 & sr & Ep & Er & Es).
  assert (Holdl : forall b, In b (AtomSetImpl.elements (ftv_typ T)) -> old n b)
    by (intros b Hb; apply (proj1 AT); apply in_elts; exact Hb).
  assert (R1 : RenN n n1 sp) by exact (RenN_push _ _ _ _ _ _ _ Ep Holdl
                                          (fun b _ => cmpb_any_eq _ _ HaE)).
  assert (Holdr : forall q, In q (AtomSetImpl.elements (frv_typ T)) -> old n1 q).
  { intros q Hq. exact (old_le n n1 q (proj1 R1) (proj2 AT q (proj1 (in_elts _ _) Hq))). }
  assert (R2 : RenN n1 n' sr) by exact (RenN_push_r _ _ _ _ _ _ _ Er Holdr).
  assert (Rho : RenN n n' (scomp sr sp)) by exact (RenN_comp _ _ _ _ _ R1 R2).
  destruct (push_sort_facts _ _ _ _ _ _ _ Ep Holdl) as (_ & _ & _ & _ & P5 & _).
  destruct (push_sort_r_facts _ _ _ _ _ _ _ Er Holdr) as (Q1 & _ & Q3 & _ & _ & _ & _).
  assert (HD1a : D1 a = D a) by exact (P5 a Ha).
  assert (Hrow1 : Drow D1) by exact (push_sort_drow _ _ _ _ _ _ _ Ep (proj1 Hs) HaE).
  assert (Hrow' : Drow D') by exact (push_sort_r_drow _ _ _ _ _ _ _ Er Hrow1 (eq_ind_r (fun k => k = k_Any \/ k = k_Eq) HaE HD1a)).
  assert (Hcomp : apT sr (apT sp T) = apT (scomp sr sp) T) by exact (apT_comp sr sp T).
  rewrite Hcomp in Es.
  destruct (pkg_close_T Sg S2 n n' a T (scomp sr sp) s Rho Ha HT AT PT Hocc
              (fun x => ltac:(rewrite Es; reflexivity)) (fun q => ltac:(rewrite Es; reflexivity))
              Fx (fun q Hq => ltac:(rewrite (Fr q Hq); apply req_refl))) as [Ct Cr].
  assert (HNN : NN D' S2).
  { intros y Hy R.
    assert (HD'y : NQ (D1 y)).
    { change (NQ (dsort D' y)) in Hy. rewrite Q3 in Hy. exact Hy. }
    destruct (push_sort_sorts _ _ _ _ _ _ _ Ep y) as [H1|H1].
    2: { rewrite H1 in HD'y. destruct HaE as [E1|E1]; rewrite E1 in HD'y; destruct HD'y as [Ez|Ez]; discriminate Ez. }
    rewrite H1 in HD'y.
    pose proof (nq_old D n y Hd HD'y) as Hyo.
    assert (Hya : y <> a).
    { intros ->. destruct HaE as [E1|E1]; rewrite E1 in HD'y; destruct HD'y as [Ez|Ez]; discriminate Ez. }
    assert (Hspy : sT sp y = typ_Var y).
    { refine (push_sort_keeps _ _ _ _ _ _ _ Ep y _ Hyo).
      destruct HD'y as [Ez|Ez]; rewrite Ez; destruct HaE as [E1|E1]; rewrite E1; reflexivity. }
    assert (Hsy : sT s y = typ_Var y).
    { rewrite Es. change (apT (sbT a (apT (scomp sr sp) T)) (apT sr (sT sp y)) = typ_Var y).
      rewrite Hspy. change (apT sr (typ_Var y)) with (sT sr y). rewrite (Q1 y).
      change (apT (sbT a (apT (scomp sr sp) T)) (typ_Var y)) with (sT (sbT a (apT (scomp sr sp) T)) y).
      cbn [sT sbT]. destruct (Atom.eq_dec y a) as [E1|_]; [ exfalso; exact (Hya E1) | reflexivity ]. }
    pose proof (Fx y Hyo) as F. rewrite Hsy in F.
    exact (teq_not_record _ _ F (proj2 Hs y HD'y) R). }
  exists s, D', n', S2. refine (conj (bind_prop_of0 _ _ _ _ _ E) _).
  exact (conj Hl (conj Hd' (conj (conj Hrow' HNN) (conj Hk' (conj Ct (conj Cr Cv)))))).
Qed.

(* A variable of sort [Numeric], [Literal] or [Quot] is bound to a scalar: the type can
   be neither an arrow nor a [Literal] record, and the substitution sends no [Numeric]
   or [Quot] variable to a record; a [Quot] variable takes no [Int].  No sort is pushed,
   because a scalar has no variable. *)
Lemma pkg_bind_prop_nl : forall (D : denv) Sg a T n,
  DOk D n -> Dsrt D Sg -> KR D DT Sg -> old n a -> pf T -> atT n T -> ps Sg T ->
  (forall v, T <> typ_Var v) -> (D a = k_Numeric \/ D a = k_Literal \/ D a = k_Quot) -> teq (sT Sg a) (apT Sg T) ->
  exists s D' n' S2, bind_prop D a T n = Some (s, D', n') /\ Pkg Sg n s D' n' S2.
Proof.
  intros D Sg a T n Hd Hs Hk Ha HT AT PT Hv HaN Heq.
  assert (Hsat : sat DT (D a) (apT Sg T)) by exact (sat_teq DT (D a) _ _ Heq (proj1 Hk a)).
  assert (Hsc : (T = typ_Int /\ D a <> k_Quot) \/ T = typ_Float).
  { destruct T as [ | | | | | A B | R | x | i | B | w A ]; try (right; reflexivity);
      try (simpl in HT; contradiction); try (exfalso; exact (Hv _ eq_refl));
      try (exfalso; destruct HaN as [E|[E|E]]; rewrite E in Hsat; simpl in Hsat;
           first [ discriminate Hsat | contradiction | (destruct Hsat as [H|H]; discriminate H) ]; fail).
    - left. split; [ reflexivity | intros E; rewrite E in Hsat; simpl in Hsat; exact Hsat ].
    - exfalso. destruct HaN as [E|[E|E]]; rewrite E in Hsat; simpl in Hsat.
      + exact (teq_not_record _ _ Heq (proj2 Hs a (or_introl E)) (apR Sg R) eq_refl).
      + exact Hsat.
      + exact (teq_not_record _ _ Heq (proj2 Hs a (or_intror E)) (apR Sg R) eq_refl). }
  assert (Hsb : sat_b D (D a) T = true).
  { destruct Hsc as [[HT0 HQ]|HT0]; rewrite HT0; destruct HaN as [E|[E|E]]; rewrite E; first [ reflexivity | (exfalso; exact (HQ E)) ]. }
  assert (Hscl : T = typ_Int \/ T = typ_Float \/ T = typ_Bool \/ T = typ_Unit \/ T = typ_String)
    by (destruct Hsc as [[H _]|H]; [ left; exact H | right; left; exact H ]).
  exists (scomp (sbT a T) (scomp sid sid)), D, n, Sg. split.
  - exact (bind_prop_scalar D a T n Hscl Hsb).
  - refine (conj (le_n n) (conj Hd (conj Hs (conj Hk (conj _ (conj _ (Cov_refl Sg))))))).
    + intros x Hx. change (pf (apT (sbT a T) (typ_Var x)) /\ atT n (apT (sbT a T) (typ_Var x)) /\
        ps Sg (apT (sbT a T) (typ_Var x)) /\ teq (sT Sg x) (apT Sg (apT (sbT a T) (typ_Var x)))).
      change (apT (sbT a T) (typ_Var x)) with (sT (sbT a T) x). cbn [sT sbT].
      destruct (Atom.eq_dec x a) as [->|Hne].
      * exact (conj HT (conj AT (conj PT Heq))).
      * refine (conj I (conj _ (conj I (teq_refl _)))). split; intros y Hy; simpl in Hy; [ | fsetdec ].
        apply AtomSetFacts.singleton_iff in Hy. subst. exact Hx.
    + intros q Hq. change (prf (apR (sbT a T) (row_Var q)) /\ atR n (apR (sbT a T) (row_Var q)) /\
        psr Sg (apR (sbT a T) (row_Var q)) /\ req (sR Sg q) (apR Sg (apR (sbT a T) (row_Var q)))).
      change (apR (sbT a T) (row_Var q)) with (sR (sbT a T) q). cbn [sR sbT idr].
      refine (conj I (conj _ (conj I (req_refl _)))). split; intros y Hy; simpl in Hy; [ fsetdec | ].
      apply AtomSetFacts.singleton_iff in Hy. subst. exact Hq.
Qed.

Lemma pkg_bind_prop : forall (D : denv) Sg a T n,
  DOk D n -> Dsrt D Sg -> KR D DT Sg -> old n a -> pf T -> atT n T -> ps Sg T -> (forall v, T <> typ_Var v) ->
  teq (sT Sg a) (apT Sg T) ->
  exists s D' n' S2, bind_prop D a T n = Some (s, D', n') /\ Pkg Sg n s D' n' S2.
Proof.
  intros D Sg a T n Hd Hs Hk Ha HT AT PT Hv Heq.
  assert (Hocc : a `notin` ftv_typ T).
  { intros Hin.
    assert (Hne : sT Sg a <> typ_Unit).
    { intros Hu. rewrite Hu in Heq. pose proof (teq_thead _ _ Heq) as Hh.
      destruct T; simpl in Hin; try fsetdec; try (exfalso; exact (Hv _ eq_refl));
        unfold apT in Hh; cbn [ap_typ thead_tag] in Hh; discriminate Hh. }
    refine (bind_prop_occ Sg D a T Hv (teq_teqD _ _ _ Heq) _ Hin).
    intros Hin'. exact (proj1 (ps_po Sg a Hne) T HT PT Hin'). }
  destruct (D a) eqn:Eda.
  - exact (pkg_bind_prop_ae D Sg a T n Hd Hs Hk Ha HT AT PT Hocc (or_introl Eda) Heq).
  - exact (pkg_bind_prop_ae D Sg a T n Hd Hs Hk Ha HT AT PT Hocc (or_intror Eda) Heq).
  - exact (pkg_bind_prop_nl D Sg a T n Hd Hs Hk Ha HT AT PT Hv (or_introl Eda) Heq).
  - exact (pkg_bind_prop_nl D Sg a T n Hd Hs Hk Ha HT AT PT Hv (or_intror (or_introl Eda)) Heq).
  - exact (pkg_bind_prop_nl D Sg a T n Hd Hs Hk Ha HT AT PT Hv (or_intror (or_intror Eda)) Heq).
Qed.

(* ---- binding a row variable ---- *)

Lemma bind_row_fin_unfold : forall r R sq D0 n0 s D' n',
  bind_row_fin r R sq D0 n0 = Some (s, D', n') ->
  exists sp, push_sort D0 (rk_sort (drk D0 r)) (AtomSetImpl.elements (ftv_row (apR sq R))) n0 = (sp, D', n') /\
    s = scomp (sbR r (apR sp (apR sq R))) (scomp sp sq).
Proof.
  intros r R sq D0 n0 s D' n' H. unfold bind_row_fin in H. cbv zeta in H.
  destruct (push_sort D0 (rk_sort (drk D0 r)) (AtomSetImpl.elements (ftv_row (apR sq R))) n0)
    as [[sp D1] n1] eqn:E.
  destruct (occR r (apR sp (apR sq R))); [ discriminate | ].
  destruct (rsat_b D1 (rk_sort (drk D1 r)) (apR sp (apR sq R)) && lacks_ok (drk D1 r) (apR sp (apR sq R)));
    [ | discriminate ].
  inversion H; subst. exists sp. split; first [ assumption | reflexivity ].
Qed.

Lemma bind_row_core_unfold : forall D r R n s D' n',
  bind_row_core D r R n = Some (s, D', n') ->
  (bind_row_fin r R sid D n = Some (s, D', n')) \/
  (exists q, bind_row_fin r R (sbR q (row_Var (ea n))) (rupd D (ea n) (rk_join (drk D r) (drk D q))) (S n)
               = Some (s, D', n')).
Proof.
  intros D r R n s D' n' H. unfold bind_row_core in H. destruct (occR r R); [ discriminate | ].
  destruct (row_tail R) as [q|].
  - right. exists q. exact H.
  - left. exact H.
Qed.

Lemma bind_row_unfold : forall D r R n s D' n',
  bind_row0 D r R n = Some (s, D', n') -> abs_vars (drk D r) R = nil ->
  exists sr D1 n1 s',
    push_sort_r D (rk_sort (drk D r)) (AtomSetImpl.elements (frv_row R)) n = (sr, D1, n1) /\
    bind_row_core D1 r (apR sr R) n1 = Some (s', D', n') /\
    s = scomp s' (scomp sr sid).
Proof.
  intros D r R n s D' n' H Hav. unfold bind_row0 in H. cbv zeta in H. rewrite Hav in H.
  cbn [forallb bool_sub] in H. rewrite apR_id in H.
  destruct (occR r R); [ discriminate | ].
  destruct (push_sort_r D (rk_sort (drk D r)) (AtomSetImpl.elements (frv_row R)) n) as [[sr D1] n1] eqn:E1.
  destruct (bind_row_core D1 r (apR sr R) n1) as [[[s1 D2] n2]|] eqn:E2; [ | discriminate ].
  inversion H; subst. exists sr, D1, n1, s1. repeat split; first [ assumption | reflexivity ].
Qed.

Lemma sT_comp3 : forall A B C x, sT (scomp (scomp A B) C) x = apT A (sT (scomp B C) x).
Proof.
  intros A B C x. change (apT (scomp A B) (sT C x) = apT A (apT B (sT C x))).
  rewrite <- apT_comp. reflexivity.
Qed.

Lemma sR_comp3 : forall A B C q, sR (scomp (scomp A B) C) q = apR A (sR (scomp B C) q).
Proof.
  intros A B C q. change (apR (scomp A B) (sR C q) = apR A (apR B (sR C q))).
  rewrite <- apR_comp. reflexivity.
Qed.

(* The step that binds [r] to [R] renamed by [rho]: the images of the old atoms are
   renamings, except [r], whose image is the renamed row. *)
Lemma pkg_close_R : forall Sg S2 n n' r R rho s,
  RenN n n' rho -> old n r -> prf R -> atR n R -> psr Sg R ->
  (forall x, sT s x = apT (sbR r (apR rho R)) (sT rho x)) ->
  (forall q, sR s q = apR (sbR r (apR rho R)) (sR rho q)) ->
  (forall x, old n x -> teq (sT Sg x) (apT S2 (sT s x))) ->
  (forall q, old n q -> req (sR Sg q) (apR S2 (sR s q))) ->
  (forall x, old n x -> pf (sT s x) /\ atT n' (sT s x) /\ ps S2 (sT s x) /\
     teq (sT Sg x) (apT S2 (sT s x))) /\
  (forall q, old n q -> prf (sR s q) /\ atR n' (sR s q) /\ psr S2 (sR s q) /\
     req (sR Sg q) (apR S2 (sR s q))).
Proof.
  intros Sg S2 n n' r R rho s Rho Hr HR AR PR Hsx Hsr Fx Fr.
  pose proof Rho as (Hl & Rt & Rr).
  destruct (ren_ap_R n n' rho R Rho HR AR) as [P1 A1].
  assert (Hty : forall x, old n x -> sT s x = sT rho x).
  { intros x Hx. rewrite (Hsx x). destruct (Rt x Hx) as (y & Ey & _). rewrite Ey. reflexivity. }
  assert (PS : psr S2 (apR rho R)).
  { refine (ren_ps_R Sg S2 rho n n' R Rho HR AR PR _). intros x Hx.
    pose proof (Fx x (proj1 AR x Hx)) as F. rewrite (Hty x (proj1 AR x Hx)) in F. exact F. }
  split.
  - intros x Hx. destruct (Rt x Hx) as (y & Ey & Hy).
    pose proof (Fx x Hx) as F. rewrite (Hty x Hx), Ey in F |- *.
    exact (conj I (conj (atT_V n' y (old_ren n n' x y Hl Hx Hy)) (conj I F))).
  - intros q Hq. destruct (Rr q Hq) as (q' & Eq' & Hq').
    pose proof (Fr q Hq) as F. rewrite (Hsr q), Eq' in F |- *.
    change (apR (sbR r (apR rho R)) (row_Var q')) with (sR (sbR r (apR rho R)) q') in F |- *.
    cbn [sR sbR] in F |- *.
    revert F. destruct (Atom.eq_dec q' r) as [Hqr|Hqr]; intro F.
    + exact (conj P1 (conj A1 (conj PS F))).
    + exact (conj I (conj (atR_V n' q' (old_ren n n' q q' Hl Hq Hq')) (conj I F))).
Qed.

Lemma pkg_bind_row : forall (D : denv) Sg r R n,
  DOk D n -> Dsrt D Sg -> KR D DT Sg -> old n r -> prf R -> atR n R -> psr Sg R ->
  (forall q, R = row_Var q -> q <> r) -> req (sR Sg r) (apR Sg R) ->
  exists s D' n' S2, bind_row D r R n = Some (s, D', n') /\ Pkg Sg n s D' n' S2.
Proof.
  intros D Sg r R n Hd Hae Hk Hr HR AR PR Hvar Hreq.
  assert (Hnot : r `notin` frv_row R).
  { intros Hin. destruct R as [ | q | l T R' | l P T R' ].
    - simpl in Hin. fsetdec.
    - simpl in Hin. apply AtomSetFacts.singleton_iff in Hin. exact (Hvar q eq_refl Hin).
    - exact (bind_row_occ Sg D r _ (req_reqD D _ _ Hreq)
               (fun Hin' => ps_pos_row Sg r _ HR PR Hin' (fun q E => ltac:(discriminate E))) Hin).
    - exact (bind_row_occ Sg D r _ (req_reqD D _ _ Hreq)
               (fun Hin' => ps_pos_row Sg r _ HR PR Hin' (fun q E => ltac:(discriminate E))) Hin). }
  assert (Hlc : lcrb 0 R = true) by exact (proj2 pf_lcb R HR 0).
  assert (Hrk : rkok DT (drk D r) (apR Sg R))
    by exact (rkok_reqD DT _ _ _ (req_reqD DT _ _ Hreq) (proj2 Hk r)).
  assert (Hav : abs_vars (drk D r) R = nil) by exact (ps_lacks Sg (drk D r) R HR PR (LK_rkok _ _ _ Hrk)).
  assert (Hfld : frld DT Sg (rk_sort (drk D r)) R)
    by exact (proj2 (ps_fld Sg _ (proj1 Hae r)) R HR PR).
  destruct (bind_row0_sorted_complete false D DT Sg r R n Hd Hk Hr (proj1 AR) (proj2 AR) HR Hlc Hnot
              (fun x _ => cmpb_any_eq _ _ (proj1 Hae r)) (fun q _ => cmpb_any_eq _ _ (proj1 Hae r))
              Hfld Hreq)
    as (s & D' & n' & S2 & E & Hk' & Hl & Hd' & Fx & Fr & Cv).
  destruct (bind_row_unfold D r R n s D' n' E Hav) as (sr & D1 & n1 & s' & Er & Ec & Es).
  assert (Holdr : forall q, In q (AtomSetImpl.elements (frv_row R)) -> old n q)
    by (intros q Hq; apply (proj2 AR); apply in_elts; exact Hq).
  assert (Rsr : RenN n n1 sr) by exact (RenN_push_r _ _ _ _ _ _ _ Er Holdr).
  destruct (push_sort_r_facts _ _ _ _ _ _ _ Er Holdr) as (Q1 & _ & Q3 & _ & Q5 & _ & _).
  assert (Hrsr : rren sr) by exact (conj Q1 Q5).
  assert (Hae1 : Drow D1) by exact (push_sort_r_drow _ _ _ _ _ _ _ Er (proj1 Hae) (proj1 Hae r)).
  assert (Hcase : exists sq D0 n0, rren sq /\ RenN n1 n0 sq /\ Drow D0 /\ (forall y, D0 y = D1 y) /\
            bind_row_fin r (apR sr R) sq D0 n0 = Some (s', D', n')).
  { destruct (bind_row_core_unfold _ _ _ _ _ _ _ Ec) as [Ef|[q Ef]].
    - exists sid, D1, n1. exact (conj rren_sid (conj (RenN_id n1) (conj Hae1 (conj (fun y => eq_refl) Ef)))).
    - exists (sbR q (row_Var (ea n1))), (rupd D1 (ea n1) (rk_join (drk D1 r) (drk D1 q))), (S n1).
      exact (conj (rren_sbR q (ea n1)) (conj (RenN_tail n1 q)
               (conj (Drow_rupd _ _ _ Hae1 (Drow_join D1 r q Hae1)) (conj (fun y => eq_refl) Ef)))). }
  destruct Hcase as (sq & D0 & n0 & Hrsq & Rsq & Hae0 & HD0 & Ef).
  destruct (bind_row_fin_unfold _ _ _ _ _ _ _ _ Ef) as (sp & Epp & Es').
  assert (Holdp : forall c, In c (AtomSetImpl.elements (ftv_row (apR sq (apR sr R)))) -> old n0 c).
  { intros c Hc. apply in_elts in Hc.
    rewrite (proj2 (ftv_rren sq Hrsq)), (proj2 (ftv_rren sr Hrsr)) in Hc.
    exact (old_le n n0 c (Nat.le_trans _ _ _ (proj1 Rsr) (proj1 Rsq)) (proj1 AR c Hc)). }
  assert (Rsp : RenN n0 n' sp) by exact (RenN_push _ _ _ _ _ _ _ Epp Holdp
                                           (fun b _ => cmpb_any_eq _ _ (Hae0 r))).
  assert (Hae' : Drow D') by exact (push_sort_drow _ _ _ _ _ _ _ Epp Hae0 (Hae0 r)).
  assert (Rsr' : RenN n n1 (scomp sr sid)) by exact (RenN_comp _ _ _ _ _ (RenN_id n) Rsr).
  assert (Rspq : RenN n1 n' (scomp sp sq)) by exact (RenN_comp _ _ _ _ _ Rsq Rsp).
  assert (Rho : RenN n n' (scomp (scomp sp sq) (scomp sr sid))) by exact (RenN_comp _ _ _ _ _ Rsr' Rspq).
  assert (HR1 : apR sp (apR sq (apR sr R)) = apR (scomp (scomp sp sq) (scomp sr sid)) R).
  { rewrite <- apR_comp, <- apR_comp, <- apR_comp, apR_id. reflexivity. }
  rewrite HR1 in Es'.
  assert (Hs : s = scomp (scomp (sbR r (apR (scomp (scomp sp sq) (scomp sr sid)) R)) (scomp sp sq))
                         (scomp sr sid)).
  { rewrite Es, Es'. reflexivity. }
  exists s, D', n', S2. refine (conj (bind_row_of0 _ _ _ _ _ E) _).
  destruct (pkg_close_R Sg S2 n n' r R (scomp (scomp sp sq) (scomp sr sid)) s Rho Hr HR AR PR
              (fun x => ltac:(rewrite Hs, sT_comp3; reflexivity))
              (fun q => ltac:(rewrite Hs, sR_comp3; reflexivity))
              Fx Fr) as [Ct Cr].
  assert (HNN : NN D' S2).
  { intros y Hy R'.
    destruct (push_sort_sorts _ _ _ _ _ _ _ Epp y) as [H1|H1].
    2: { rewrite H1 in Hy. destruct (Hae0 r) as [E1|E1]; rewrite E1 in Hy; destruct Hy as [Ez|Ez]; discriminate Ez. }
    rewrite H1, (HD0 y) in Hy. change (NQ (dsort D1 y)) in Hy. rewrite Q3 in Hy.
    change (NQ (D y)) in Hy.
    pose proof (nq_old D n y Hd Hy) as Hyo.
    assert (Hyo0 : old n0 y) by exact (old_le n n0 y (Nat.le_trans _ _ _ (proj1 Rsr) (proj1 Rsq)) Hyo).
    assert (Hspy : sT sp y = typ_Var y).
    { refine (push_sort_keeps _ _ _ _ _ _ _ Epp y _ Hyo0).
      assert (HD1y : NQ (D1 y)) by (change (NQ (dsort D1 y)); rewrite Q3; exact Hy).
      rewrite (HD0 y). destruct HD1y as [Ez|Ez]; rewrite Ez; destruct (Hae0 r) as [E1|E1]; rewrite E1; reflexivity. }
    assert (Hrho_y : sT (scomp (scomp sp sq) (scomp sr sid)) y = typ_Var y).
    { change (apT (scomp sp sq) (apT sr (typ_Var y)) = typ_Var y).
      change (apT sr (typ_Var y)) with (sT sr y). rewrite (proj1 Hrsr y).
      change (apT (scomp sp sq) (typ_Var y)) with (sT (scomp sp sq) y).
      change (sT (scomp sp sq) y) with (apT sp (sT sq y)). rewrite (proj1 Hrsq y).
      change (apT sp (typ_Var y)) with (sT sp y). exact Hspy. }
    assert (Hsy : sT s y = typ_Var y).
    { rewrite Hs, sT_comp3, Hrho_y.
      change (apT (sbR r (apR (scomp (scomp sp sq) (scomp sr sid)) R)) (typ_Var y)) with
        (sT (sbR r (apR (scomp (scomp sp sq) (scomp sr sid)) R)) y). reflexivity. }
    pose proof (Fx y Hyo) as F. rewrite Hsy in F.
    exact (teq_not_record _ _ F (proj2 Hae y Hy) R'). }
  exact (conj Hl (conj Hd' (conj (conj Hae' HNN) (conj Hk' (conj Ct (conj Cr Cv)))))).
Qed.

(* ---- rewriting a row to present a label ---- *)

(* What [rewrite_row] does to the type variables and the supply, with every sort [Any]:
   nothing to the type variables, and either nothing to the row variables or one row
   variable bound to an entry of fresh variables; or the entry it presents is absent. *)
Lemma rw_shape : forall l av R D n P' T' R' s0 D0 n1, Drow D ->
  rewrite_row l av D R n = Some (P', T', R', s0, D0, n1) ->
  n <= n1 /\ Drow D0 /\ (forall y, NQ (D0 y) -> NQ (D y)) /\
  (P' = typ_Bool \/ s0 = sid \/
   exists r, r `in` frv_row R /\ P' = typ_Var (ea n) /\ T' = typ_Var (ea (S n)) /\
     n1 = n + 3 /\
     s0 = sbR r (row_Maybe l (typ_Var (ea n)) (typ_Var (ea (S n))) (row_Var (ea (n + 2))))).
Proof.
  intros l av R. induction R as [ | r | l' T R IH | l' P T R IH ]; intros D n P' T' R' s0 D0 n1 HD E;
    cbn [rewrite_row] in E.
  - inversion E; subst. refine (conj _ (conj HD (conj (fun y H => H) (or_introl eq_refl)))). lia.
  - destruct (AtomSetImpl.mem r av); [ discriminate | ]. cbn zeta in E.
    pose proof (HD r) as Hrs.
    destruct (rk_lacks (drk D r) l) eqn:Hl; inversion E; subst.
    + refine (conj _ (conj _ (conj _ (or_introl eq_refl)))).
      * lia.
      * apply Drow_rupd; [ exact HD | exact Hrs ].
      * intros y H. exact H.
    + refine (conj _ (conj _ (conj _ (or_intror (or_intror (ex_intro _ r (conj _ (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))))))))).
      * lia.
      * apply Drow_rupd; [ intros q; cbn [upd drk]; apply HD | exact Hrs ].
      * intros y H. cbn [rupd upd dsort] in H. destruct (Atom.eq_dec y (ea (S n))) as [->|Hne].
        -- destruct Hrs as [E1|E1]; rewrite E1 in H; destruct H as [Ez|Ez]; discriminate Ez.
        -- exact H.
      * simpl. fsetdec.
  - destruct (Nat.eqb l l'); [ inversion E; subst; exact (conj (le_n _) (conj HD (conj (fun y H => H) (or_intror (or_introl eq_refl))))) | ].
    destruct (rewrite_row l av D R n) as [[[[[[P0 T0] R3] s] D1] n2]|] eqn:E1; [ | discriminate ].
    inversion E; subst. destruct (IH _ _ _ _ _ _ _ _ HD E1) as (H1 & H2 & H2' & H3).
    refine (conj H1 (conj H2 (conj H2' _))).
    destruct H3 as [H3|[H3|(r & Hr & H3)]]; [ left; exact H3 | right; left; exact H3 | right; right ].
    exists r. split; [ simpl; fsetdec | exact H3 ].
  - destruct (Nat.eqb l l'); [ inversion E; subst; exact (conj (le_n _) (conj HD (conj (fun y H => H) (or_intror (or_introl eq_refl))))) | ].
    destruct (rewrite_row l av D R n) as [[[[[[P0 T0] R3] s] D1] n2]|] eqn:E1; [ | discriminate ].
    inversion E; subst. destruct (IH _ _ _ _ _ _ _ _ HD E1) as (H1 & H2 & H2' & H3).
    refine (conj H1 (conj H2 (conj H2' _))).
    destruct H3 as [H3|[H3|(r & Hr & H3)]]; [ left; exact H3 | right; left; exact H3 | right; right ].
    exists r. split; [ simpl; fsetdec | exact H3 ].
Qed.

Lemma atT_var : forall n m, m < n -> atT n (typ_Var (ea m)).
Proof.
  intros n m Hm. split; simpl; intros y Hy; [ | fsetdec ].
  apply AtomSetFacts.singleton_iff in Hy. subst. exact (old_ea n m Hm).
Qed.

Lemma atR_var : forall n m, m < n -> atR n (row_Var (ea m)).
Proof.
  intros n m Hm. split; simpl; intros y Hy; [ fsetdec | ].
  apply AtomSetFacts.singleton_iff in Hy. subst. exact (old_ea n m Hm).
Qed.

Lemma atT_scalar : forall n T, (forall x, x `notin` ftv_typ T) -> (forall x, x `notin` frv_typ T) -> atT n T.
Proof. intros n T H1 H2. split; intros y Hy; [ exfalso; exact (H1 y Hy) | exfalso; exact (H2 y Hy) ]. Qed.

Lemma atR_ext_inv : forall n l T R, atR n (row_Ext l T R) -> atT n T /\ atR n R.
Proof.
  intros n l T R [H1 H2]. simpl in H1, H2. refine (conj (conj _ _) (conj _ _));
    intros y Hy; [ apply H1 | apply H2 | apply H1 | apply H2 ]; fsetdec.
Qed.

Lemma atR_maybe_inv : forall n l P T R, atR n (row_Maybe l P T R) -> atT n P /\ atT n T /\ atR n R.
Proof.
  intros n l P T R [H1 H2]. simpl in H1, H2. refine (conj (conj _ _) (conj (conj _ _) (conj _ _)));
    intros y Hy; [ apply H1 | apply H2 | apply H1 | apply H2 | apply H1 | apply H2 ]; fsetdec.
Qed.

Lemma atR_ext_mk : forall n l T R, atT n T -> atR n R -> atR n (row_Ext l T R).
Proof.
  intros n l T R [T1 T2] [R1 R2]. split; simpl; intros y Hy; apply AtomSetFacts.union_iff in Hy;
    destruct Hy as [Hy|Hy]; [ apply T1 | apply R1 | apply T2 | apply R2 ]; exact Hy.
Qed.

Lemma atR_maybe_mk : forall n l P T R, atT n P -> atT n T -> atR n R -> atR n (row_Maybe l P T R).
Proof.
  intros n l P T R [P1 P2] [T1 T2] [R1 R2]. split; simpl; intros y Hy;
    apply AtomSetFacts.union_iff in Hy; destruct Hy as [Hy|Hy];
    try (apply AtomSetFacts.union_iff in Hy; destruct Hy as [Hy|Hy]);
    first [ exact (P1 y Hy) | exact (T1 y Hy) | exact (R1 y Hy) | exact (P2 y Hy) | exact (T2 y Hy) | exact (R2 y Hy) ].
Qed.

(* The pieces [rewrite_row] returns are in the fragment, over the new supply, with every
   entry present under the extension [S2]. *)
Lemma rw_facts : forall l av Sg S2 s0 D0 n n1, Pkg Sg n s0 D0 n1 S2 ->
  forall R D P' T' R', Drow D -> rewrite_row l av D R n = Some (P', T', R', s0, D0, n1) ->
    prf R -> atR n R -> psr Sg R ->
    pf P' /\ atT n1 P' /\ pf T' /\ atT n1 T' /\ ps S2 T' /\ prf R' /\ atR n1 R' /\ psr S2 R'.
Proof.
  intros l av Sg S2 s0 D0 n n1 Hk.
  induction R as [ | r | l' T R IH | l' P T R IH ]; intros D P' T' R' HD E HR AR PR;
    cbn [rewrite_row] in E.
  - inversion E; subst. refine (conj I (conj _ (conj I (conj _ (conj I (conj I (conj _ I))))))).
    + apply atT_scalar; intros; simpl; fsetdec.
    + exact (atT_var _ _ (Nat.lt_succ_diag_r n)).
    + split; simpl; intros; fsetdec.
  - destruct (AtomSetImpl.mem r av); [ discriminate | ]. cbn zeta in E.
    destruct (rk_lacks (drk D r) l) eqn:Hl; inversion E; subst.
    + refine (conj I (conj _ (conj I (conj _ (conj I (conj I (conj _ I))))))).
      * apply atT_scalar; intros; simpl; fsetdec.
      * exact (atT_var (n + 2) n ltac:(lia)).
      * exact (atR_var (n + 2) (S n) ltac:(lia)).
    + refine (conj I (conj _ (conj I (conj _ (conj I (conj I (conj _ I))))))).
      * exact (atT_var (n + 3) n ltac:(lia)).
      * exact (atT_var (n + 3) (S n) ltac:(lia)).
      * exact (atR_var (n + 3) (n + 2) ltac:(lia)).
  - destruct (Nat.eqb l l') eqn:Ell.
    + inversion E; subst. destruct HR as [HT HR']. destruct (atR_ext_inv _ _ _ _ AR) as [AT AR'].
      destruct PR as [PT PR'].
      destruct (pkg_ap_T _ _ _ _ _ _ _ Hk HT AT PT) as (A1 & A2 & A3). rewrite apT_id in A1, A2, A3.
      destruct (pkg_ap_R _ _ _ _ _ _ _ Hk HR' AR' PR') as (B1 & B2 & B3). rewrite apR_id in B1, B2, B3.
      refine (conj I (conj _ (conj A1 (conj A2 (conj A3 (conj B1 (conj B2 B3))))))).
      apply atT_scalar; intros; simpl; fsetdec.
    + destruct (rewrite_row l av D R n) as [[[[[[P0 T0] R3] s] D1] n2]|] eqn:E1; [ | discriminate ].
      inversion E; subst. destruct HR as [HT HR']. destruct (atR_ext_inv _ _ _ _ AR) as [AT AR'].
      destruct PR as [PT PR'].
      destruct (IH D _ _ _ HD E1 HR' AR' PR') as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8).
      destruct (pkg_ap_T _ _ _ _ _ _ _ Hk HT AT PT) as (A1 & A2 & A3).
      refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj (conj A1 I6) (conj (atR_ext_mk _ _ _ _ A2 I7) (conj A3 I8)))))))).
  - destruct (Nat.eqb l l') eqn:Ell.
    + inversion E; subst. destruct HR as [HP [HT HR']]. destruct (atR_maybe_inv _ _ _ _ _ AR) as [AP [AT AR']].
      destruct PR as [PP [PT PR']].
      destruct (pkg_ap_T _ _ _ _ _ _ _ Hk HT AT PT) as (A1 & A2 & A3). rewrite apT_id in A1, A2, A3.
      destruct (pkg_ap_R _ _ _ _ _ _ _ Hk HR' AR' PR') as (B1 & B2 & B3). rewrite apR_id in B1, B2, B3.
      refine (conj HP (conj (atT_mono _ _ _ (proj1 Hk) AP) (conj A1 (conj A2 (conj A3 (conj B1 (conj B2 B3))))))).
    + destruct (rewrite_row l av D R n) as [[[[[[P0 T0] R3] s] D1] n2]|] eqn:E1; [ | discriminate ].
      inversion E; subst. destruct HR as [HP [HT HR']]. destruct (atR_maybe_inv _ _ _ _ _ AR) as [AP [AT AR']].
      destruct PR as [PP [PT PR']].
      destruct (IH D _ _ _ HD E1 HR' AR' PR') as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8).
      destruct (pkg_ap_R _ _ _ _ _ _ (row_Maybe l' P T R) Hk (conj HP (conj HT HR')) AR (conj PP (conj PT PR')))
        as (A1 & A2 & A3).
      destruct A1 as (A1P & A1T & _). destruct A3 as (A3P & A3T & _).
      destruct (atR_maybe_inv _ _ _ _ _ A2) as (A2P & A2T & _).
      refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj (conj A1P (conj A1T I6)) (conj (atR_maybe_mk _ _ _ _ _ A2P A2T I7) (conj A3P (conj A3T I8))))))))).
Qed.

Lemma pkg_rewrite : forall (D : denv) Sg R1 R2 l P T R1' n,
  DOk D n -> Dsrt D Sg -> KR D DT Sg -> row_head R1 = Some (l, P, T, R1') -> apT Sg P = typ_Unit ->
  req (apR Sg R1) (apR Sg R2) -> prf R2 -> atR n R2 -> psr Sg R2 ->
  exists P' T' R2' s0 D0 n1 S2,
    rewrite_row l (side_av R1) D R2 n = Some (P', T', R2', s0, D0, n1) /\ Pkg Sg n s0 D0 n1 S2 /\
    apT S2 P' = typ_Unit /\ pf P' /\ atT n1 P' /\ pf T' /\ atT n1 T' /\ ps S2 T' /\
    prf R2' /\ atR n1 R2' /\ psr S2 R2' /\
    teq (apT S2 T') (apT Sg T) /\ req (apR S2 R2') (apR Sg R1').
Proof.
  intros D Sg R1 R2 l P T R1' n Hd Ht Hk Hh HP Hreq HR AR PR.
  assert (HPt : teq (apT Sg P) typ_Unit) by (rewrite HP; apply teq_refl).
  destruct (rewrite_row_complete Sg R1 R2 l P T R1' D n DT Hh HPt Hreq Hd Hk (proj1 AR) (proj2 AR))
    as (P' & T' & R2' & s0 & D0 & n1 & S2 & E & Hk0 & Hn & Hd0 & Hf1 & Hf2 & HPP & HTT & HRR & Hcv0).
  destruct (rw_shape l (side_av R1) R2 D n P' T' R2' s0 D0 n1 (proj1 Ht) E) as (_ & Hrow0 & Hnum & Hsh0).
  assert (HPU : apT S2 P' = typ_Unit).
  { rewrite HP in HPP. exact (teq_Unit_inv _ (teq_sym _ _ HPP)). }
  assert (Hsh : s0 = sid \/ exists r, r `in` frv_row R2 /\ P' = typ_Var (ea n) /\ T' = typ_Var (ea (S n)) /\
     n1 = n + 3 /\
     s0 = sbR r (row_Maybe l (typ_Var (ea n)) (typ_Var (ea (S n))) (row_Var (ea (n + 2))))).
  { destruct Hsh0 as [-> | H]; [ | exact H ]. exfalso. unfold apT in HPU. cbn [ap_typ] in HPU. discriminate HPU. }
  assert (Hsx : forall x, sT s0 x = typ_Var x).
  { intros x. destruct Hsh as [-> | (r & _ & _ & _ & _ & ->)]; reflexivity. }
  assert (Ht0 : Dsrt D0 S2).
  { refine (conj Hrow0 _). intros y Hy. pose proof (nq_old D n y Hd (Hnum y Hy)) as Hold.
    pose proof (Hf1 y Hold) as F. rewrite (Hsx y) in F.
    exact (teq_not_record _ _ F (proj2 Ht y (Hnum y Hy))). }
  assert (Hpk : Pkg Sg n s0 D0 n1 S2).
  { refine (conj Hn (conj Hd0 (conj Ht0 (conj Hk0 (conj _ (conj _ Hcv0)))))).
    - intros x Hx. rewrite (Hsx x). refine (conj I (conj _ (conj I _))).
      + split; simpl; intros y Hy; [ | fsetdec ]. apply AtomSetFacts.singleton_iff in Hy. subst.
        exact (old_le n n1 _ Hn Hx).
      + rewrite <- (Hsx x). exact (Hf1 x Hx).
    - intros q Hq. destruct Hsh as [-> | (r & Hr & HP' & HT' & Hn1 & ->)].
      + cbn [sR sid idr]. refine (conj I (conj _ (conj I _))).
        * split; simpl; intros y Hy; [ fsetdec | ]. apply AtomSetFacts.singleton_iff in Hy. subst.
          exact (old_le n n1 _ Hn Hq).
        * exact (Hf2 q Hq).
      + cbn [sR sbR]. destruct (Atom.eq_dec q r) as [->|Hne].
        * subst P'. refine (conj _ (conj _ (conj _ _))).
          -- exact (conj I (conj I I)).
          -- rewrite Hn1. apply atR_maybe_mk; [ exact (atT_var (n + 3) n ltac:(lia)) | exact (atT_var (n + 3) (S n) ltac:(lia))
                                           | exact (atR_var (n + 3) (n + 2) ltac:(lia)) ].
          -- exact (conj HPU (conj I I)).
          -- pose proof (Hf2 r Hq) as Hf. cbn [sR sbR] in Hf. rewrite dec_same in Hf. exact Hf.
        * refine (conj I (conj _ (conj I _))).
          -- split; simpl; intros y Hy; [ fsetdec | ]. apply AtomSetFacts.singleton_iff in Hy. destruct Hy.
             exact (old_le n n1 _ Hn Hq).
          -- pose proof (Hf2 q Hq) as Hf. cbn [sR sbR] in Hf. rewrite (dec_diff _ _ _ _ _ Hne) in Hf. exact Hf. }
  destruct (rw_facts l (side_av R1) Sg S2 s0 D0 n n1 Hpk R2 D P' T' R2' (proj1 Ht) E HR AR PR)
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  exists P', T', R2', s0, D0, n1, S2. exact (conj E (conj Hpk (conj HPU (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 (conj F7 (conj F8 (conj HTT HRR)))))))))))).
Qed.

(* ---- the induction ---- *)

Definition UT (m : nat) : Prop := forall (Sg : sub) (D : denv) T1 T2 n,
  tsz (apT Sg T1) < m -> DOk D n -> Dsrt D Sg -> KR D DT Sg -> pf T1 -> pf T2 -> atT n T1 -> atT n T2 ->
  ps Sg T1 -> ps Sg T2 -> teq (apT Sg T1) (apT Sg T2) ->
  exists s D' n' S2, Stable (fun f => unify_tD f D T1 T2 n = Some (s, D', n') /\
                                       unify_t f D T1 T2 n = Some (s, D', n')) /\ Pkg Sg n s D' n' S2.

Definition UR (m : nat) : Prop := forall (Sg : sub) (D : denv) R1 R2 n,
  rsz (apR Sg R1) < m -> DOk D n -> Dsrt D Sg -> KR D DT Sg -> prf R1 -> prf R2 -> atR n R1 -> atR n R2 ->
  psr Sg R1 -> psr Sg R2 -> req (apR Sg R1) (apR Sg R2) ->
  exists s D' n' S2, Stable (fun f => unify_rD f D R1 R2 n = Some (s, D', n') /\
                                       unify_r f D R1 R2 n = Some (s, D', n')) /\ Pkg Sg n s D' n' S2.

Lemma tsz_pos : forall T, 1 <= tsz T.
Proof. intros T. destruct T; simpl; lia. Qed.

(* The first entry of a row of the fragment whose entries are all present. *)
Lemma row_front : forall Sg n R1 l P T R1', row_head R1 = Some (l, P, T, R1') ->
  prf R1 -> atR n R1 -> psr Sg R1 ->
  apT Sg P = typ_Unit /\ pf P /\ pf T /\ prf R1' /\ atT n P /\ atT n T /\ atR n R1' /\
  ps Sg T /\ psr Sg R1' /\ rsz (apR Sg R1) = S (tsz (apT Sg T) + rsz (apR Sg R1')).
Proof.
  intros Sg n R1 l P T R1' Hh HR AR PR. destruct R1 as [ | | l0 T0 R0 | l0 P0 T0 R0 ]; simpl in Hh;
    try discriminate; inversion Hh; subst.
  - destruct HR as [HT HR']. destruct (atR_ext_inv _ _ _ _ AR) as [AT AR']. destruct PR as [PT PR'].
    refine (conj eq_refl (conj I (conj HT (conj HR' (conj _ (conj AT (conj AR' (conj PT (conj PR' _))))))))).
    + apply atT_scalar; intros; simpl; fsetdec.
    + rewrite apR_Ext. reflexivity.
  - destruct HR as [HP [HT HR']]. destruct (atR_maybe_inv _ _ _ _ _ AR) as [AP [AT AR']].
    destruct PR as [PP [PT PR']].
    refine (conj PP (conj HP (conj HT (conj HR' (conj AP (conj AT (conj AR' (conj PT (conj PR' _))))))))).
    rewrite apR_Maybe. cbn [rsz]. change (ap_typ (sT Sg) (sR Sg) P) with (apT Sg P). rewrite PP.
    reflexivity.
Qed.

Lemma Pkg_sbT : forall Sg D n a a', DOk D n -> Dsrt D Sg -> KR D DT Sg -> old n a' ->
  teq (sT Sg a) (sT Sg a') -> Pkg Sg n (sbT a (typ_Var a')) D n Sg.
Proof.
  intros Sg D n a a' Hd Ht Hk Ha' Heq. refine (conj (le_n n) (conj Hd (conj Ht (conj Hk (conj _ (conj _ (Cov_refl Sg))))))).
  - intros x Hx. cbn [sT sbT]. destruct (Atom.eq_dec x a) as [->|Hne].
    + refine (conj I (conj _ (conj I Heq))). split; simpl; intros y Hy; [ | fsetdec ].
      apply AtomSetFacts.singleton_iff in Hy. destruct Hy. exact Ha'.
    + refine (conj I (conj _ (conj I (teq_refl _)))). split; simpl; intros y Hy; [ | fsetdec ].
      apply AtomSetFacts.singleton_iff in Hy. destruct Hy. exact Hx.
  - intros q Hq. cbn [sR sbT idr]. refine (conj I (conj _ (conj I (req_refl _)))).
    split; simpl; intros y Hy; [ fsetdec | ]. apply AtomSetFacts.singleton_iff in Hy. destruct Hy. exact Hq.
Qed.

(* The unifier [unify_tD] reads rows at the environment and [unify_t] reads them
   plain, and the two agree on every call the induction makes: each leaf below is
   stated for both, and the induction concludes both from one run. *)
Lemma stable2_bind_l : forall D a T n r,
  bind_prop D a T n = Some r -> (forall v, T <> typ_Var v) ->
  Stable (fun f => unify_tD f D (typ_Var a) T n = Some r /\ unify_t f D (typ_Var a) T n = Some r).
Proof.
  intros D a T n r E Hv. exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  destruct T; try (exfalso; exact (Hv _ eq_refl)); exact (conj E E).
Qed.

Lemma stable2_bind_r : forall D a T n r,
  bind_prop D a T n = Some r -> (forall v, T <> typ_Var v) ->
  Stable (fun f => unify_tD f D T (typ_Var a) n = Some r /\ unify_t f D T (typ_Var a) n = Some r).
Proof.
  intros D a T n r E Hv. exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  destruct T; try (exfalso; exact (Hv _ eq_refl)); exact (conj E E).
Qed.

Lemma stable2_scalar : forall D c n,
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) ->
  Stable (fun f => unify_tD f D c c n = Some (sid, D, n) /\ unify_t f D c c n = Some (sid, D, n)).
Proof.
  intros D c n Hc. exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; split; reflexivity.
Qed.

Lemma stable2_varvar : forall D a a' n,
  Stable (fun f => unify_tD f D (typ_Var a) (typ_Var a') n =
    Some (if Atom.eq_dec a a' then sid else if finer_b (D a') (D a) then sbT a (typ_Var a')
          else if finer_b (D a) (D a') then sbT a' (typ_Var a) else meet_float a a', D, n) /\
    unify_t f D (typ_Var a) (typ_Var a') n =
    Some (if Atom.eq_dec a a' then sid else if finer_b (D a') (D a) then sbT a (typ_Var a')
          else if finer_b (D a) (D a') then sbT a' (typ_Var a) else meet_float a a', D, n)).
Proof.
  intros D a a' n. exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  cbn [unify_tD unify_t]. destruct (Atom.eq_dec a a') as [->|Hne]; [ split; reflexivity | ].
  destruct (finer_b (D a') (D a)) eqn:E1; [ split; reflexivity | ].
  destruct (finer_b (D a) (D a')); split; reflexivity.
Qed.

(* A [Literal] type and a [Quot] type that are one type are [Float]: no variable has
   both sorts, [Int] is not [Quot], and a record is not [Literal]. *)
Lemma lit_quot_float : forall Ta Tb, sat DT k_Literal Ta -> sat DT k_Quot Tb -> teq Ta Tb -> teq Ta typ_Float.
Proof.
  intros Ta Tb Hl Hq H.
  destruct Ta as [ | | | | | A B | R | x | i | B | w A ]; simpl in Hl; try contradiction;
    try (destruct Hl as [E|E]; discriminate E); try discriminate Hl.
  - rewrite (teq_Int_inv _ H) in Hq. simpl in Hq. contradiction.
  - apply teq_refl.
  - pose proof (teq_thead _ _ H) as Hh. destruct Tb as [ | | | | | A' B' | R' | b | i' | B' | w' A' ]; simpl in Hh; try discriminate Hh.
    rewrite <- (teq_var_eq _ _ H x b eq_refl eq_refl) in Hq. simpl in Hq.
    assert (E1 : DT x = k_Literal) by (inversion Hl; congruence).
    rewrite E1 in Hq. inversion Hq; try discriminate; congruence.
Qed.

Lemma Pkg_float : forall Sg D n a, DOk D n -> Dsrt D Sg -> KR D DT Sg -> old n a ->
  teq (sT Sg a) typ_Float -> Pkg Sg n (sbT a typ_Float) D n Sg.
Proof.
  intros Sg D n a Hd Ht Hk Ha Heq. refine (conj (le_n n) (conj Hd (conj Ht (conj Hk (conj _ (conj _ (Cov_refl Sg))))))).
  - intros x Hx. change (pf (apT (sbT a typ_Float) (typ_Var x)) /\ atT n (apT (sbT a typ_Float) (typ_Var x)) /\
      ps Sg (apT (sbT a typ_Float) (typ_Var x)) /\ teq (sT Sg x) (apT Sg (apT (sbT a typ_Float) (typ_Var x)))).
    change (apT (sbT a typ_Float) (typ_Var x)) with (sT (sbT a typ_Float) x). cbn [sT sbT].
    destruct (Atom.eq_dec x a) as [->|Hne].
    + refine (conj I (conj _ (conj I Heq))). split; intros y Hy; simpl in Hy; fsetdec.
    + refine (conj I (conj _ (conj I (teq_refl _)))). split; intros y Hy; simpl in Hy; [ | fsetdec ].
      apply AtomSetFacts.singleton_iff in Hy. subst. exact Hx.
  - intros q Hq. change (prf (apR (sbT a typ_Float) (row_Var q)) /\ atR n (apR (sbT a typ_Float) (row_Var q)) /\
      psr Sg (apR (sbT a typ_Float) (row_Var q)) /\ req (sR Sg q) (apR Sg (apR (sbT a typ_Float) (row_Var q)))).
    change (apR (sbT a typ_Float) (row_Var q)) with (sR (sbT a typ_Float) q). cbn [sR sbT idr].
    refine (conj I (conj _ (conj I (req_refl _)))). split; intros y Hy; simpl in Hy; [ fsetdec | ].
    apply AtomSetFacts.singleton_iff in Hy. subst. exact Hq.
Qed.

(* Neither of two variables is the finer: one is [Literal] and the other [Quot], and
   the substitution sends both to [Float], which [meet_float] binds. *)
Lemma Pkg_meet : forall Sg D n a a', DOk D n -> Dsrt D Sg -> KR D DT Sg -> old n a -> old n a' ->
  finer_b (D a') (D a) = false -> finer_b (D a) (D a') = false ->
  teq (sT Sg a) (sT Sg a') -> Pkg Sg n (meet_float a a') D n Sg.
Proof.
  intros Sg D n a a' Hd Ht Hk Ha Ha' F1 F2 Heq.
  assert (Hf : teq (sT Sg a) typ_Float /\ teq (sT Sg a') typ_Float).
  { destruct (finer_b_cmp _ _ F1 F2) as [[E1 E2]|[E1 E2]].
    - (* D a' is Literal and D a is Quot *)
      pose proof (proj1 Hk a) as Sa. pose proof (proj1 Hk a') as Sa'. rewrite E2 in Sa. rewrite E1 in Sa'.
      assert (Hb : teq (sT Sg a') typ_Float) by exact (lit_quot_float _ _ Sa' Sa (teq_sym _ _ Heq)).
      exact (conj (teq_trans _ _ _ Heq Hb) Hb).
    - pose proof (proj1 Hk a) as Sa. pose proof (proj1 Hk a') as Sa'. rewrite E2 in Sa. rewrite E1 in Sa'.
      assert (Hb : teq (sT Sg a) typ_Float) by exact (lit_quot_float _ _ Sa Sa' Heq).
      exact (conj Hb (teq_trans _ _ _ (teq_sym _ _ Heq) Hb)). }
  unfold meet_float.
  exact (Pkg_comp Sg n (sbT a typ_Float) D n Sg (sbT a' typ_Float) D n Sg
           (Pkg_float Sg D n a Hd Ht Hk Ha (proj1 Hf)) (Pkg_float Sg D n a' Hd Ht Hk Ha' (proj2 Hf))).
Qed.

Lemma stable2_rbind_l : forall D r R n res, bind_row D r R n = Some res ->
  (forall s, R = row_Var s -> s <> r) ->
  Stable (fun f => unify_rD f D (row_Var r) R n = Some res /\ unify_r f D (row_Var r) R n = Some res).
Proof.
  intros D r R n res E Hv. exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  destruct R as [ | s | l T R' | l P T R' ]; cbn [unify_rD unify_r]; try exact (conj E E).
  destruct (Atom.eq_dec r s) as [->|Hne]; [ exfalso; exact (Hv s eq_refl eq_refl) | exact (conj E E) ].
Qed.

Lemma stable2_rbind_r : forall D s R n res, bind_row D s R n = Some res ->
  (forall r, R <> row_Var r) ->
  Stable (fun f => unify_rD f D R (row_Var s) n = Some res /\ unify_r f D R (row_Var s) n = Some res).
Proof.
  intros D s R n res E Hv. exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  destruct R as [ | r | l T R' | l P T R' ]; cbn [unify_rD unify_r]; try exact (conj E E).
  exfalso. exact (Hv r eq_refl).
Qed.

Lemma drop_abs_ps : forall S R, prf R -> psr S R -> drop_abs R = R.
Proof.
  intros S R. induction R as [ | r | l T R IH | l P T R IH ]; intros HR PR; try reflexivity.
  - cbn [drop_abs]. rewrite (IH (proj2 HR) (proj2 PR)). reflexivity.
  - destruct HR as [HP [HT HR']]. destruct PR as [PP [PT PR']]. cbn [drop_abs].
    rewrite (IH HR' PR'). rewrite (pres_not_abs S P HP PP). reflexivity.
Qed.

Lemma unify_r_rw : forall f D R1 R2 n l P T R1' P' T' R2' s0 D0 n1 sp D1 n2 s1 D2 n3 s2 D3 n4,
  row_head R1 = Some (l, P, T, R1') -> (forall r, R1 <> row_Var r) -> (forall s, R2 <> row_Var s) ->
  rewrite_row l (side_av R1) D R2 n = Some (P', T', R2', s0, D0, n1) ->
  unify_t f D0 (apT s0 P) P' n1 = Some (sp, D1, n2) ->
  unify_t f D1 (apT sp (apT s0 T)) (apT sp T') n2 = Some (s1, D2, n3) ->
  unify_r f D2 (drop_abs (apR s1 (apR sp (apR s0 R1')))) (drop_abs (apR s1 (apR sp R2'))) n3 = Some (s2, D3, n4) ->
  unify_r (S f) D R1 R2 n = Some (scomp s2 (scomp s1 (scomp sp s0)), D3, n4).
Proof.
  intros f D R1 R2 n l P T R1' P' T' R2' s0 D0 n1 sp D1 n2 s1 D2 n3 s2 D3 n4 Hh Hn1 Hn2 E E1 E2 E3.
  destruct R1 as [ | r | l0 T0 R0 | l0 P0 T0 R0 ]; try (exfalso; exact (Hn1 r eq_refl));
    simpl in Hh; try discriminate; inversion Hh; subst;
    destruct R2 as [ | s | l2 T2 R2'' | l2 P2 T2 R2'' ]; try (exfalso; exact (Hn2 s eq_refl));
    cbn [unify_r row_head]; rewrite E; cbn iota beta; rewrite E1; cbn iota beta; rewrite E2; cbn iota beta;
    rewrite E3; reflexivity.
Qed.

Lemma unify_rD_rw : forall f D R1 R2 n l P T R1' P' T' R2' s0 D0 n1 sp D1 n2 s1 D2 n3 s2 D3 n4,
  row_head R1 = Some (l, P, T, R1') -> (forall r, R1 <> row_Var r) -> (forall s, R2 <> row_Var s) ->
  rewrite_row l (side_av R1) D R2 n = Some (P', T', R2', s0, D0, n1) ->
  unify_tD f D0 (apT s0 P) P' n1 = Some (sp, D1, n2) ->
  unify_tD f D1 (apT sp (apT s0 T)) (apT sp T') n2 = Some (s1, D2, n3) ->
  unify_rD f D2 (nfR D2 (apR s1 (apR sp (apR s0 R1')))) (nfR D2 (apR s1 (apR sp R2'))) n3 = Some (s2, D3, n4) ->
  unify_rD (S f) D R1 R2 n = Some (scomp s2 (scomp s1 (scomp sp s0)), D3, n4).
Proof.
  intros f D R1 R2 n l P T R1' P' T' R2' s0 D0 n1 sp D1 n2 s1 D2 n3 s2 D3 n4 Hh Hn1 Hn2 E E1 E2 E3.
  destruct R1 as [ | r | l0 T0 R0 | l0 P0 T0 R0 ]; try (exfalso; exact (Hn1 r eq_refl));
    simpl in Hh; try discriminate; inversion Hh; subst;
    destruct R2 as [ | s | l2 T2 R2'' | l2 P2 T2 R2'' ]; try (exfalso; exact (Hn2 s eq_refl));
    cbn [unify_rD row_head]; rewrite E; cbn iota beta; rewrite E1; cbn iota beta; rewrite E2; cbn iota beta;
    rewrite E3; reflexivity.
Qed.

(* The arm of [unify_rD] that rewrites the second row to present the label of the
   front entry of the first, then unifies the presences, the fields and the rests with
   the substitution threaded. *)
Lemma rw_arm : forall m, UT m -> UR m -> forall Sg D R1 R2 n l P T R1',
  row_head R1 = Some (l, P, T, R1') -> (forall r, R1 <> row_Var r) -> (forall s, R2 <> row_Var s) ->
  rsz (apR Sg R1) < S m -> DOk D n -> Dsrt D Sg -> KR D DT Sg -> prf R1 -> prf R2 -> atR n R1 -> atR n R2 ->
  psr Sg R1 -> psr Sg R2 -> req (apR Sg R1) (apR Sg R2) ->
  exists s D' n' S2, Stable (fun f => unify_rD f D R1 R2 n = Some (s, D', n') /\
                                       unify_r f D R1 R2 n = Some (s, D', n')) /\ Pkg Sg n s D' n' S2.
Proof.
  intros m IHt IHr Sg D R1 R2 n l P T R1' Hh Hn1 Hn2 Hlt Hd Ht Hk HR1 HR2 AR1 AR2 PR1 PR2 Hreq.
  destruct (row_front Sg n R1 l P T R1' Hh HR1 AR1 PR1)
    as (HP & Pp & Pt & Pr1' & Ap & At & Ar1' & Pst & Psr1' & Hsz).
  destruct (pkg_rewrite D Sg R1 R2 l P T R1' n Hd Ht Hk Hh HP Hreq HR2 AR2 PR2)
    as (P' & T' & R2' & s0 & D0 & n1 & S2 & E & K0 & HPU & Pp' & Ap' & Pt' & At' & Pst' & Pr2' & Ar2' & Psr2' & HT'eq & HR'eq).
  pose proof (tsz_pos (apT Sg T)) as Hpos.
  assert (Hm2 : tsz (apT Sg T) + rsz (apR Sg R1') < m) by lia.
  pose proof K0 as K0'. destruct K0 as (Hl0 & Hd0 & Ht0 & Hk0 & _).
  pose proof (ps_pres Sg P Pp HP) as PsP.
  destruct (pkg_ap_T Sg n s0 D0 n1 S2 P K0' Pp Ap PsP) as (A1 & A2 & A3).
  (* the presences *)
  assert (mA : tsz (apT S2 (apT s0 P)) < m).
  { rewrite <- (teq_tsz _ _ (pkg_fac_T Sg n s0 D0 n1 S2 P K0' Ap)). rewrite HP. simpl. lia. }
  assert (hA : teq (apT S2 (apT s0 P)) (apT S2 P')).
  { rewrite HPU. eapply teq_trans; [ apply teq_sym; exact (pkg_fac_T Sg n s0 D0 n1 S2 P K0' Ap) | ].
    rewrite HP. apply teq_refl. }
  destruct (IHt S2 D0 (apT s0 P) P' n1 mA Hd0 Ht0 Hk0 A1 Pp' A2 Ap' A3 (ps_pres S2 P' Pp' HPU) hA)
    as (sp & D1 & n2 & S3 & EA & KA).
  pose proof KA as KA'. destruct KA as (Hl1 & Hd1 & Ht1 & Hk1 & _).
  (* the fields *)
  destruct (pkg_ap_T Sg n s0 D0 n1 S2 T K0' Pt At Pst) as (B1 & B2 & B3).
  destruct (pkg_ap_T S2 n1 sp D1 n2 S3 (apT s0 T) KA' B1 B2 B3) as (C1 & C2 & C3).
  destruct (pkg_ap_T S2 n1 sp D1 n2 S3 T' KA' Pt' At' Pst') as (C1' & C2' & C3').
  assert (mB : tsz (apT S3 (apT sp (apT s0 T))) < m).
  { rewrite <- (teq_tsz _ _ (pkg_fac_T S2 n1 sp D1 n2 S3 _ KA' B2)).
    rewrite <- (teq_tsz _ _ (pkg_fac_T Sg n s0 D0 n1 S2 T K0' At)). lia. }
  assert (hB : teq (apT S3 (apT sp (apT s0 T))) (apT S3 (apT sp T'))).
  { eapply teq_trans; [ apply teq_sym; exact (pkg_fac_T S2 n1 sp D1 n2 S3 _ KA' B2) | ].
    eapply teq_trans; [ apply teq_sym; exact (pkg_fac_T Sg n s0 D0 n1 S2 T K0' At) | ].
    eapply teq_trans; [ apply teq_sym; exact HT'eq | ].
    exact (pkg_fac_T S2 n1 sp D1 n2 S3 _ KA' At'). }
  destruct (IHt S3 D1 (apT sp (apT s0 T)) (apT sp T') n2 mB Hd1 Ht1 Hk1 C1 C1' C2 C2' C3 C3' hB)
    as (s1 & D2 & n3 & S4 & EB & KB).
  pose proof KB as KB'. destruct KB as (Hl2 & Hd2 & Ht2 & Hk2 & _).
  (* the rests *)
  destruct (pkg_ap_R Sg n s0 D0 n1 S2 R1' K0' Pr1' Ar1' Psr1') as (E1 & E2 & E3).
  destruct (pkg_ap_R S2 n1 sp D1 n2 S3 _ KA' E1 E2 E3) as (F1 & F2 & F3).
  destruct (pkg_ap_R S3 n2 s1 D2 n3 S4 _ KB' F1 F2 F3) as (G1 & G2 & G3).
  destruct (pkg_ap_R S2 n1 sp D1 n2 S3 R2' KA' Pr2' Ar2' Psr2') as (F1' & F2' & F3').
  destruct (pkg_ap_R S3 n2 s1 D2 n3 S4 _ KB' F1' F2' F3') as (G1' & G2' & G3').
  assert (Hf1 : req (apR Sg R1') (apR S4 (apR s1 (apR sp (apR s0 R1'))))).
  { eapply req_trans; [ exact (pkg_fac_R Sg n s0 D0 n1 S2 R1' K0' Ar1') | ].
    eapply req_trans; [ exact (pkg_fac_R S2 n1 sp D1 n2 S3 _ KA' E2) | ].
    exact (pkg_fac_R S3 n2 s1 D2 n3 S4 _ KB' F2). }
  assert (Hf2 : req (apR Sg R1') (apR S4 (apR s1 (apR sp R2')))).
  { eapply req_trans; [ apply req_sym; exact HR'eq | ].
    eapply req_trans; [ exact (pkg_fac_R S2 n1 sp D1 n2 S3 _ KA' Ar2') | ].
    exact (pkg_fac_R S3 n2 s1 D2 n3 S4 _ KB' F2'). }
  assert (mC : rsz (apR S4 (apR s1 (apR sp (apR s0 R1')))) < m).
  { rewrite <- (req_rsz _ _ Hf1). lia. }
  destruct (IHr S4 D2 (apR s1 (apR sp (apR s0 R1'))) (apR s1 (apR sp R2')) n3 mC
              Hd2 Ht2 Hk2 G1 G1' G2 G2' G3 G3'
              (req_trans _ _ _ (req_sym _ _ Hf1) Hf2))
    as (s2 & D3 & n4 & S5 & EC & KC).
  exists (scomp s2 (scomp s1 (scomp sp s0))), D3, n4, S5. split.
  - assert (EC' : Stable (fun f => unify_rD f D2 (nfR D2 (apR s1 (apR sp (apR s0 R1'))))
                                    (nfR D2 (apR s1 (apR sp R2'))) n3 = Some (s2, D3, n4) /\
                                  unify_r f D2 (drop_abs (apR s1 (apR sp (apR s0 R1'))))
                                    (drop_abs (apR s1 (apR sp R2'))) n3 = Some (s2, D3, n4))).
    { eapply Stable_mono; [ | exact EC ]. intros f [Hu1 Hu2].
      rewrite (proj2 (ps_nf D2 S4) _ G1 G3), (proj2 (ps_nf D2 S4) _ G1' G3').
      rewrite (drop_abs_ps S4 _ G1 G3), (drop_abs_ps S4 _ G1' G3'). exact (conj Hu1 Hu2). }
    eapply Stable_mono; [ | exact (Stable_below _ (Stable_and _ _ EA (Stable_and _ _ EB EC'))) ].
    intros [|f] Hf; [ contradiction | ].
    destruct Hf as ((Ha1 & Ha2) & (Hb1 & Hb2) & (Hc1 & Hc2)). split.
    + exact (unify_rD_rw f D R1 R2 n l P T R1' P' T' R2' s0 D0 n1 sp D1 n2 s1 D2 n3 s2 D3 n4
               Hh Hn1 Hn2 E Ha1 Hb1 Hc1).
    + exact (unify_r_rw f D R1 R2 n l P T R1' P' T' R2' s0 D0 n1 sp D1 n2 s1 D2 n3 s2 D3 n4
               Hh Hn1 Hn2 E Ha2 Hb2 Hc2).
  - exact (Pkg_comp _ _ _ _ _ _ _ _ _ _ (Pkg_comp _ _ _ _ _ _ _ _ _ _ (Pkg_comp _ _ _ _ _ _ _ _ _ _ K0' KA') KB') KC).
Qed.

Lemma atT_arrow_inv : forall n A B, atT n (typ_Arrow A B) -> atT n A /\ atT n B.
Proof.
  intros n A B [H1 H2]. simpl in H1, H2. refine (conj (conj _ _) (conj _ _));
    intros y Hy; [ apply H1 | apply H2 | apply H1 | apply H2 ]; fsetdec.
Qed.

Lemma atT_record_inv : forall n R, atT n (typ_Record R) -> atR n R.
Proof. intros n R [H1 H2]. exact (conj H1 H2). Qed.

Lemma front_nonempty : forall Sg n R l P T R1', row_head R = Some (l, P, T, R1') ->
  prf R -> atR n R -> psr Sg R -> rsz (apR Sg R) <> 0.
Proof.
  intros Sg n R l P T R1' Hh HR AR PR.
  destruct (row_front Sg n R l P T R1' Hh HR AR PR) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsz).
  rewrite Hsz. discriminate.
Qed.

Lemma row_case_var_l : forall Sg D r R2 n, DOk D n -> Dsrt D Sg -> KR D DT Sg -> prf R2 -> atR n (row_Var r) -> atR n R2 ->
  psr Sg R2 -> req (apR Sg (row_Var r)) (apR Sg R2) ->
  exists s D' n' S2, Stable (fun f => unify_rD f D (row_Var r) R2 n = Some (s, D', n') /\
                                       unify_r f D (row_Var r) R2 n = Some (s, D', n')) /\ Pkg Sg n s D' n' S2.
Proof.
  intros Sg D r R2 n Hd Ht Hk HR2 AR1 AR2 PR2 Hreq.
  assert (Hr : old n r) by (apply (proj2 AR1 r); simpl; fsetdec).
  assert (H : R2 = row_Var r \/ (forall s, R2 = row_Var s -> s <> r)).
  { destruct R2 as [ | s | l T R' | l P T R' ]; try (right; intros s E; discriminate E).
    destruct (Atom.eq_dec s r) as [->|Hne]; [ left; reflexivity | right; intros s' E; inversion E; congruence ]. }
  destruct H as [-> | Hvar].
  - exists sid, D, n, Sg. split; [ | exact (Pkg_id Sg D n Hd Ht Hk) ].
    exists 1. intros [|f] Hf; [ lia | ]. cbn [unify_rD unify_r].
    destruct (Atom.eq_dec r r); [ split; reflexivity | congruence ].
  - destruct (pkg_bind_row D Sg r R2 n Hd Ht Hk Hr HR2 AR2 PR2 Hvar Hreq) as (s & D' & n' & S2 & E & K).
    exists s, D', n', S2. exact (conj (stable2_rbind_l D r R2 n _ E Hvar) K).
Qed.

Lemma row_case_var_r : forall Sg D R1 s n, DOk D n -> Dsrt D Sg -> KR D DT Sg -> prf R1 -> atR n R1 -> atR n (row_Var s) ->
  psr Sg R1 -> (forall r, R1 <> row_Var r) -> req (apR Sg R1) (apR Sg (row_Var s)) ->
  exists s0 D' n' S2, Stable (fun f => unify_rD f D R1 (row_Var s) n = Some (s0, D', n') /\
                                        unify_r f D R1 (row_Var s) n = Some (s0, D', n')) /\ Pkg Sg n s0 D' n' S2.
Proof.
  intros Sg D R1 s n Hd Ht Hk HR1 AR1 AR2 PR1 Hnv Hreq.
  assert (Hs : old n s) by (apply (proj2 AR2 s); simpl; fsetdec).
  destruct (pkg_bind_row D Sg s R1 n Hd Ht Hk Hs HR1 AR1 PR1 (fun q E => ltac:(exfalso; exact (Hnv q E)))
              (req_sym _ _ Hreq)) as (s0 & D' & n' & S2 & E & K).
  exists s0, D', n', S2. exact (conj (stable2_rbind_r D s R1 n _ E Hnv) K).
Qed.

Ltac neq := intros ? Hnv; discriminate Hnv.

Theorem unify_pres_aux : forall m, UT m /\ UR m.
Proof.
  induction m as [|m IH].
  - split; [ intros Sg D T1 T2 n Hlt | intros Sg D R1 R2 n Hlt ]; lia.
  - destruct IH as [IHt IHr]. split.
    + intros Sg D T1 T2 n Hlt Hd Ht Hk P1 P2 A1 A2 S1 S2 Hteq.
      destruct T1 as [ | | | | | A B | R | a | i | B1 | w A1' ]; try (simpl in P1; contradiction);
      destruct T2 as [ | | | | | A' B' | R' | a' | i' | B1' | w' A1'' ];
        try (simpl in P2; contradiction);
        try (exfalso; pose proof (teq_thead _ _ Hteq) as Hh; unfold apT in Hh;
             cbn [ap_typ thead_tag] in Hh; discriminate Hh).
      all: try (exists sid, D, n, Sg; split; [ apply stable2_scalar; tauto | exact (Pkg_id Sg D n Hd Ht Hk) ]; fail).
      all: try (destruct (pkg_bind_prop D Sg a _ n Hd Ht Hk (proj1 A1 a ltac:(simpl; fsetdec)) P2 A2 S2 ltac:(neq) Hteq)
                  as (s & D' & n' & S3 & E & K);
                exists s, D', n', S3; split; [ exact (stable2_bind_l D a _ n _ E ltac:(neq)) | exact K ]; fail).
      all: try (destruct (pkg_bind_prop D Sg a' _ n Hd Ht Hk (proj1 A2 a' ltac:(simpl; fsetdec)) P1 A1 S1 ltac:(neq)
                            (teq_sym _ _ Hteq))
                  as (s & D' & n' & S3 & E & K);
                exists s, D', n', S3; split; [ exact (stable2_bind_r D a' _ n _ E ltac:(neq)) | exact K ]; fail).
      * (* Arrow, Arrow *)
        destruct P1 as [PA PB], P2 as [PA' PB'], S1 as [SA SB], S2 as [SA' SB'].
        destruct (atT_arrow_inv _ _ _ A1) as [AA AB]. destruct (atT_arrow_inv _ _ _ A2) as [AA' AB'].
        change (apT Sg (typ_Arrow A B)) with (typ_Arrow (apT Sg A) (apT Sg B)) in Hlt, Hteq.
        change (apT Sg (typ_Arrow A' B')) with (typ_Arrow (apT Sg A') (apT Sg B')) in Hteq.
        cbn [tsz] in Hlt.
        destruct (teq_Arrow_inv _ _ _ Hteq) as (X & Y & EX & H1 & H2). injection EX as <- <-.
        destruct (IHt Sg D A A' n ltac:(lia) Hd Ht Hk PA PA' AA AA' SA SA' H1) as (s1 & D1 & n1 & S3 & E1 & K1).
        pose proof K1 as K1'. destruct K1 as (Hl1 & Hd1 & Ht1 & Hk1 & _).
        destruct (pkg_ap_T Sg n s1 D1 n1 S3 B K1' PB AB SB) as (B1 & B2 & B3).
        destruct (pkg_ap_T Sg n s1 D1 n1 S3 B' K1' PB' AB' SB') as (B1' & B2' & B3').
        pose proof (pkg_fac_T Sg n s1 D1 n1 S3 B K1' AB) as FB.
        pose proof (pkg_fac_T Sg n s1 D1 n1 S3 B' K1' AB') as FB'.
        destruct (IHt S3 D1 (apT s1 B) (apT s1 B') n1 ltac:(rewrite <- (teq_tsz _ _ FB); lia) Hd1 Ht1 Hk1
                    B1 B1' B2 B2' B3 B3'
                    (teq_trans _ _ _ (teq_sym _ _ FB) (teq_trans _ _ _ H2 FB')))
          as (s2 & D2 & n2 & S4 & E2 & K2).
        exists (scomp s2 s1), D2, n2, S4. split.
        -- eapply Stable_mono; [ | exact (Stable_below _ (Stable_and _ _ E1 E2)) ].
           intros [|f] Hf; [ contradiction | ]. destruct Hf as [(Ha1 & Ha2) (Hb1 & Hb2)].
           cbn [unify_tD unify_t]. rewrite Ha1, Hb1, Ha2, Hb2. split; reflexivity.
        -- exact (Pkg_comp _ _ _ _ _ _ _ _ _ _ K1' K2).
      * (* Record, Record *)
        change (apT Sg (typ_Record R)) with (typ_Record (apR Sg R)) in Hlt, Hteq.
        change (apT Sg (typ_Record R')) with (typ_Record (apR Sg R')) in Hteq.
        cbn [tsz] in Hlt.
        destruct (teq_Record_inv _ _ Hteq) as (X & EX & H1). injection EX as <-.
        destruct (IHr Sg D R R' n ltac:(lia) Hd Ht Hk P1 P2 (atT_record_inv _ _ A1) (atT_record_inv _ _ A2)
                    S1 S2 H1) as (s & D' & n' & S3 & E & K).
        exists s, D', n', S3. split; [ | exact K ].
        eapply Stable_mono; [ | exact (Stable_below _ E) ].
        intros [|f] Hf; [ contradiction | ]. cbn [unify_tD unify_t].
        rewrite (proj2 (ps_nf D Sg) R P1 S1), (proj2 (ps_nf D Sg) R' P2 S2),
          (drop_abs_ps Sg R P1 S1), (drop_abs_ps Sg R' P2 S2). exact Hf.
      * (* Var, Var *)
        destruct (Atom.eq_dec a a') as [->|Hne].
        -- exists sid, D, n, Sg. split; [ | exact (Pkg_id Sg D n Hd Ht Hk) ].
           eapply Stable_mono; [ | exact (stable2_varvar D a' a' n) ].
           intros f [Hf1 Hf2]. rewrite Hf1, Hf2. destruct (Atom.eq_dec a' a'); [ split; reflexivity | congruence ].
        -- destruct (finer_b (D a') (D a)) eqn:Ef.
           ++ exists (sbT a (typ_Var a')), D, n, Sg. split.
              ** eapply Stable_mono; [ | exact (stable2_varvar D a a' n) ].
                 intros f [Hf1 Hf2]. rewrite Hf1, Hf2. destruct (Atom.eq_dec a a'); [ congruence | ]. rewrite Ef.
                 split; reflexivity.
              ** exact (Pkg_sbT Sg D n a a' Hd Ht Hk (proj1 A2 a' ltac:(simpl; fsetdec)) Hteq).
           ++ destruct (finer_b (D a) (D a')) eqn:Ef2.
              ** exists (sbT a' (typ_Var a)), D, n, Sg. split.
                 --- eapply Stable_mono; [ | exact (stable2_varvar D a a' n) ].
                     intros f [Hf1 Hf2]. rewrite Hf1, Hf2. destruct (Atom.eq_dec a a'); [ congruence | ]. rewrite Ef, Ef2.
                     split; reflexivity.
                 --- exact (Pkg_sbT Sg D n a' a Hd Ht Hk (proj1 A1 a ltac:(simpl; fsetdec)) (teq_sym _ _ Hteq)).
              ** exists (meet_float a a'), D, n, Sg. split.
                 --- eapply Stable_mono; [ | exact (stable2_varvar D a a' n) ].
                     intros f [Hf1 Hf2]. rewrite Hf1, Hf2. destruct (Atom.eq_dec a a'); [ congruence | ]. rewrite Ef, Ef2.
                     split; reflexivity.
                 --- exact (Pkg_meet Sg D n a a' Hd Ht Hk (proj1 A1 a ltac:(simpl; fsetdec)) (proj1 A2 a' ltac:(simpl; fsetdec)) Ef Ef2 Hteq).
      * (* Group, Group *)
        destruct P1 as [PA1 _], P2 as [PA2 _].
        change (apT Sg (typ_Grp w A1')) with (typ_Grp w (apT Sg A1')) in Hlt, Hteq.
        change (apT Sg (typ_Grp w' A1'')) with (typ_Grp w' (apT Sg A1'')) in Hteq.
        cbn [tsz] in Hlt.
        destruct (teq_Grp_inv _ _ _ Hteq) as (X & EX & H1). injection EX as Ew Ex. subst X w'.
        destruct (IHt Sg D A1' A1'' n ltac:(lia) Hd Ht Hk PA1 PA2 A1 A2 S1 S2 H1) as (s & D' & n' & S3 & E & K).
        exists s, D', n', S3. split; [ | exact K ].
        eapply Stable_mono; [ | exact (Stable_below _ E) ].
        intros [|f] Hf; [ contradiction | ]. cbn [unify_tD unify_t].
        destruct (gdecl_eq_dec w w) as [_|N]; [ | exfalso; exact (N eq_refl) ]. exact (conj (proj2 Hf) (proj2 Hf)).
    + intros Sg D R1 R2 n Hlt Hd Ht Hk HR1 HR2 AR1 AR2 PR1 PR2 Hreq.
      destruct R1 as [ | r | l T R1' | l P T R1' ].
      * destruct R2 as [ | s | l2 T2 R2' | l2 P2 T2 R2' ].
        -- exists sid, D, n, Sg. split; [ | exact (Pkg_id Sg D n Hd Ht Hk) ].
           exists 1. intros [|f] Hf; [ lia | split; reflexivity ].
        -- exact (row_case_var_r Sg D row_Empty s n Hd Ht Hk HR1 AR1 AR2 PR1 ltac:(neq) Hreq).
        -- exfalso. exact (front_nonempty Sg n (row_Ext l2 T2 R2') l2 typ_Unit T2 R2' eq_refl HR2 AR2 PR2 (eq_sym (req_rsz _ _ Hreq))).
        -- exfalso. exact (front_nonempty Sg n (row_Maybe l2 P2 T2 R2') l2 P2 T2 R2' eq_refl HR2 AR2 PR2 (eq_sym (req_rsz _ _ Hreq))).
      * exact (row_case_var_l Sg D r R2 n Hd Ht Hk HR2 AR1 AR2 PR2 Hreq).
      * destruct R2 as [ | s | l2 T2 R2' | l2 P2 T2 R2' ].
        -- exfalso. exact (front_nonempty Sg n (row_Ext l T R1') l typ_Unit T R1' eq_refl HR1 AR1 PR1 (req_rsz _ _ Hreq)).
        -- exact (row_case_var_r Sg D _ s n Hd Ht Hk HR1 AR1 AR2 PR1 ltac:(neq) Hreq).
        -- exact (rw_arm m IHt IHr Sg D (row_Ext l T R1') (row_Ext l2 T2 R2') n l typ_Unit T R1' eq_refl ltac:(neq) ltac:(neq) Hlt Hd Ht Hk HR1 HR2
                    AR1 AR2 PR1 PR2 Hreq).
        -- exact (rw_arm m IHt IHr Sg D (row_Ext l T R1') (row_Maybe l2 P2 T2 R2') n l typ_Unit T R1' eq_refl ltac:(neq) ltac:(neq) Hlt Hd Ht Hk HR1 HR2
                    AR1 AR2 PR1 PR2 Hreq).
      * destruct R2 as [ | s | l2 T2 R2' | l2 P2 T2 R2' ].
        -- exfalso. exact (front_nonempty Sg n (row_Maybe l P T R1') l P T R1' eq_refl HR1 AR1 PR1 (req_rsz _ _ Hreq)).
        -- exact (row_case_var_r Sg D _ s n Hd Ht Hk HR1 AR1 AR2 PR1 ltac:(neq) Hreq).
        -- exact (rw_arm m IHt IHr Sg D (row_Maybe l P T R1') (row_Ext l2 T2 R2') n l P T R1' eq_refl ltac:(neq) ltac:(neq) Hlt Hd Ht Hk HR1 HR2
                    AR1 AR2 PR1 PR2 Hreq).
        -- exact (rw_arm m IHt IHr Sg D (row_Maybe l P T R1') (row_Maybe l2 P2 T2 R2') n l P T R1' eq_refl ltac:(neq) ltac:(neq) Hlt Hd Ht Hk HR1 HR2
                    AR1 AR2 PR1 PR2 Hreq).
Qed.

(* A step's promise read at the conversion the rest of the development states it in. *)
Corollary Pkg_sem : forall Sg n s D' n' S2, Pkg Sg n s D' n' S2 ->
  KR D' DT S2 /\ DOk D' n' /\ n <= n' /\
  (forall x, old n x -> teqD DT (sT Sg x) (apT S2 (sT s x))) /\
  (forall q, old n q -> reqD DT (sR Sg q) (apR S2 (sR s q))).
Proof.
  intros Sg n s D' n' S2 (Hl & Hd & Ht & Hk & Hx & Hq & _).
  refine (conj Hk (conj Hd (conj Hl (conj _ _)))).
  - intros x Hx'. exact (teq_teqD _ _ _ (proj2 (proj2 (proj2 (Hx x Hx'))))).
  - intros q Hq'. exact (req_reqD _ _ _ (proj2 (proj2 (proj2 (Hq q Hq'))))).
Qed.

(* A bound on the atoms the images of [Sg] mention bounds the extension's. *)
Corollary Pkg_bnd : forall Sg n s D' n' S2 E F, Pkg Sg n s D' n' S2 -> Bnd E F Sg -> Bnd E F S2.
Proof.
  intros Sg n s D' n' S2 E F (_ & _ & _ & _ & _ & _ & Cv) HB. exact (Cv E F HB).
Qed.

Corollary Pkg_ftv : forall Sg n s D' n' S2 (B : atoms), Pkg Sg n s D' n' S2 ->
  (forall z, ftv_typ (sT Sg z) [<=] B) -> (forall r, ftv_row (sR Sg r) [<=] B) ->
  forall y, ftv_typ (sT S2 y) [<=] B.
Proof.
  intros Sg n s D' n' S2 B HP Ht Hr y a Ha.
  pose proof (Pkg_bnd Sg n s D' n' S2 (fun a => a `in` B) (fun _ => True) HP
                (conj (fun z a Ha => Ht z a Ha) (conj (fun _ _ _ => I) (conj (fun r a Ha => Hr r a Ha) (fun _ _ _ => I)))))
    as (B1 & _). exact (B1 y a Ha).
Qed.

(* The unifier W calls is complete on the types of the fragment: given a substitution
   under which every presence entry is present and which unifies the two types, in an
   environment whose row kinds are [Any] or [Eq] and that [Sg] respects (the labels a
   row variable lacks, the sorts of the type variables, and no [Numeric] variable sent
   to a record), it succeeds from some fuel on, and [Sg] factors through its result by
   an extension [S2] of [Sg] to the fresh variables, which respects the environment
   the unifier returns and whose images are in the fragment over atoms below the new
   supply.  The plain unifier [unify_t] succeeds with the same result at the same
   fuel: the group arm of [unify_tD] hands its payload to it. *)
Theorem unify_tD_complete_full : forall (D : denv) Sg T1 T2 n,
  DOk D n -> Dsrt D Sg -> KR D DT Sg -> pf T1 -> pf T2 -> atT n T1 -> atT n T2 ->
  ps Sg T1 -> ps Sg T2 -> teq (apT Sg T1) (apT Sg T2) ->
  exists s D' n' S2, Stable (fun f => unify_tD f D T1 T2 n = Some (s, D', n') /\
                                       unify_t f D T1 T2 n = Some (s, D', n')) /\
    Pkg Sg n s D' n' S2.
Proof.
  intros D Sg T1 T2 n Hd Ht Hk P1 P2 A1 A2 S1 S2 Hteq.
  exact (proj1 (unify_pres_aux (S (tsz (apT Sg T1)))) Sg D T1 T2 n (Nat.lt_succ_diag_r _)
           Hd Ht Hk P1 P2 A1 A2 S1 S2 Hteq).
Qed.

Theorem unify_rD_complete_full : forall (D : denv) Sg R1 R2 n,
  DOk D n -> Dsrt D Sg -> KR D DT Sg -> prf R1 -> prf R2 -> atR n R1 -> atR n R2 ->
  psr Sg R1 -> psr Sg R2 -> req (apR Sg R1) (apR Sg R2) ->
  exists s D' n' S2, Stable (fun f => unify_rD f D R1 R2 n = Some (s, D', n') /\
                                       unify_r f D R1 R2 n = Some (s, D', n')) /\
    Pkg Sg n s D' n' S2.
Proof.
  intros D Sg R1 R2 n Hd Ht Hk P1 P2 A1 A2 S1 S2 Hreq.
  exact (proj2 (unify_pres_aux (S (rsz (apR Sg R1)))) Sg D R1 R2 n (Nat.lt_succ_diag_r _)
           Hd Ht Hk P1 P2 A1 A2 S1 S2 Hreq).
Qed.

End Sorted.

(* A group over one parameter, whose tag uses that parameter, is in the fragment. *)
Example pf_group_param : forall w a, (exists cs, In cs (gtags w) /\ In 6 cs) ->
  pf (typ_Grp w (typ_Arrow (typ_Var a) typ_Unit)).
Proof. intros w a H. exact (conj (conj I I) (conj H I)). Qed.
