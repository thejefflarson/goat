(* Completeness of algorithm W, stage 7.6g: [bind_prop] with sorts
   (docs/design/phase7-proof-plan.md).

   [bind_prop] binds a variable [a] to a type [T] at the sort of [a]: each
   variable of [T] coarser than the sort is renamed to a fresh one of that sort
   ([push_sort]), likewise each row variable ([push_sort_r]), the renamed type
   may not mention [a], and it must satisfy the sort.  Given a substitution
   [Sg] that unifies [a] and [T], [bind_prop_sorted_complete] shows the run
   succeeds, and that the extension [S2] of [Sg] to the fresh variables (the
   one [push_sort_complete] and [push_sort_r_complete] invent) factors [Sg]
   through the substitution the run returns.

   Three hypotheses say what the sort of [a] does not give:
   - [pf T]: the type is plain, with no recursive type, group or index;
   - the atoms of [T] and [a] are below the supply [n] ([old]);
   - [fld]: the image of the field of an entry with a presence variable
     satisfies the sort.  The calculus's [rsat] leaves the field of an absent
     entry unconstrained and [bind_prop] checks it, so a [Sg] that makes the
     presence absent and the field unfit for the sort unifies a pair [bind_prop]
     refuses.  It is the same corner as [Hfield] in [GoatCompleteSorts.v].

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
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatSatTeq.
Require Import Goat.GoatCompleteSorts.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

Definition old (n : nat) (x : atom) : Prop := forall m, n <= m -> x <> ea m.

Lemma in_elts : forall S x, In x (AtomSetImpl.elements S) <-> x `in` S.
Proof.
  intros S x. split.
  - intros H. apply AtomSetFacts.elements_iff. apply SetoidList.In_InA; [ exact eq_equivalence | exact H ].
  - intros H. apply AtomSetFacts.elements_iff in H. apply SetoidList.InA_alt in H.
    destruct H as [y [E H]]. subst. exact H.
Qed.

(* ---- what [push_sort] and [push_sort_r] leave behind ---- *)

Lemma push_sort_facts : forall l D k n sp D' n',
  push_sort D k l n = (sp, D', n') -> (forall b, In b l -> old n b) ->
  (forall r, sR sp r = row_Var r) /\ n <= n' /\
  (forall x, ~ In x l -> sT sp x = typ_Var x) /\
  (forall x, exists y, sT sp x = typ_Var y /\ (y = x \/ exists m, n <= m /\ y = ea m)) /\
  (forall x, old n x -> D' x = D x) /\
  (forall x, In x l -> exists y, sT sp x = typ_Var y /\ finer_b (D' y) k = true).
Proof.
  induction l as [|b l IH]; intros D k n sp D' n' H Hold; cbn [push_sort] in H.
  - inversion H; subst; clear H. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + intros r. reflexivity.
    + lia.
    + intros x _. reflexivity.
    + intros x. exists x. split; [ reflexivity | left; reflexivity ].
    + intros x _. reflexivity.
    + intros x [].
  - destruct (finer_b (D b) k) eqn:Ef.
    + destruct (IH D k n sp D' n' H (fun c Hc => Hold c (or_intror Hc)))
        as (H1 & H2 & H3 & H4 & H5 & H6).
      refine (conj H1 (conj H2 (conj _ (conj H4 (conj H5 _))))).
      * intros x Hx. apply H3. intros Hin. apply Hx. right. exact Hin.
      * intros x [->|Hx].
        -- destruct (in_dec Atom.eq_dec x l) as [Hin|Hnin].
           ++ exact (H6 x Hin).
           ++ exists x. rewrite (H3 x Hnin). split; [ reflexivity | ].
              rewrite (H5 x (Hold x (or_introl eq_refl))). exact Ef.
        -- exact (H6 x Hx).
    + destruct (push_sort (upd D (ea n) k) k l (Datatypes.S n)) as [[s1 D1] n1] eqn:E.
      inversion H; subst; clear H.
      assert (Hold' : forall c, In c l -> old (Datatypes.S n) c).
      { intros c Hc m Hm. apply (Hold c (or_intror Hc)). lia. }
      destruct (IH _ _ _ _ _ _ E Hold') as (H1 & H2 & H3 & H4 & H5 & H6).
      assert (Hbn : forall m, n <= m -> b <> ea m) by exact (Hold b (or_introl eq_refl)).
      assert (Hnl : ~ In (ea n) l).
      { intros Hin. exact (Hold (ea n) (or_intror Hin) n (le_n n) eq_refl). }
      assert (Hs1 : sT s1 (ea n) = typ_Var (ea n)) by exact (H3 _ Hnl).
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * intros r. change (apR s1 (sR (sbT b (typ_Var (ea n))) r) = row_Var r).
        cbn [sR sbT]. unfold idr. cbn [apR ap_row]. exact (H1 r).
      * lia.
      * intros x Hx. change (apT s1 (sT (sbT b (typ_Var (ea n))) x) = typ_Var x).
        cbn [sT sbT]. destruct (Atom.eq_dec x b) as [->|Hne].
        -- exfalso. apply Hx. left. reflexivity.
        -- change (sT s1 x = typ_Var x). apply H3. intros Hin. apply Hx. right. exact Hin.
      * intros x. change (exists y, apT s1 (sT (sbT b (typ_Var (ea n))) x) = typ_Var y /\
          (y = x \/ exists m, n <= m /\ y = ea m)).
        cbn [sT sbT]. destruct (Atom.eq_dec x b) as [->|Hne].
        -- exists (ea n). split; [ exact Hs1 | right; exists n; split; [ lia | reflexivity ] ].
        -- destruct (H4 x) as (y & Hy & Hc). exists y. split; [ exact Hy | ].
           destruct Hc as [->|[m [Hm ->]]]; [ left; reflexivity | right; exists m; split; [ lia | reflexivity ] ].
      * intros x Hx. rewrite (H5 x).
        -- cbn [upd dsort]. destruct (Atom.eq_dec x (ea n)) as [E2|_]; [ | reflexivity ].
           exfalso. exact (Hx n (le_n n) E2).
        -- intros m Hm. apply Hx. lia.
      * intros x Hx. destruct (Atom.eq_dec x b) as [->|Hxb].
        -- exists (ea n). split.
           ++ change (apT s1 (sT (sbT b (typ_Var (ea n))) b) = typ_Var (ea n)).
              cbn [sT sbT]. rewrite dec_same. exact Hs1.
           ++ rewrite (H5 (ea n)).
              ** cbn [upd dsort]. rewrite dec_same. destruct k; reflexivity.
              ** intros m Hm E2. apply ea_inj in E2. lia.
        -- assert (Hx' : In x l) by (destruct Hx as [Eq0|Hx]; [ exfalso; apply Hxb; symmetry; exact Eq0 | exact Hx ]).
           destruct (H6 x Hx') as (y & Hy & Hf). exists y. split; [ | exact Hf ].
           change (apT s1 (sT (sbT b (typ_Var (ea n))) x) = typ_Var y).
           cbn [sT sbT]. rewrite (dec_diff _ _ _ _ _ Hxb). exact Hy.
Qed.

Lemma finer_b_refl : forall k, finer_b k k = true.
Proof. intros []; reflexivity. Qed.

Lemma push_sort_r_facts : forall l D k n sr D' n',
  push_sort_r D k l n = (sr, D', n') -> (forall q, In q l -> old n q) ->
  (forall x, sT sr x = typ_Var x) /\ n <= n' /\ dsort D' = dsort D /\
  (forall q, ~ In q l -> sR sr q = row_Var q) /\
  (forall q, exists q', sR sr q = row_Var q') /\
  (forall q, old n q -> drk D' q = drk D q) /\
  (forall q, In q l -> exists q', sR sr q = row_Var q' /\ finer_b (rk_sort (drk D' q')) k = true).
Proof.
  induction l as [|b l IH]; intros D k n sr D' n' H Hold; cbn [push_sort_r] in H.
  - inversion H; subst; clear H. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    + intros x. reflexivity.
    + lia.
    + reflexivity.
    + intros q _. reflexivity.
    + intros q. exists q. reflexivity.
    + intros q _. reflexivity.
    + intros q [].
  - destruct (finer_b (rk_sort (drk D b)) k) eqn:Ef.
    + destruct (IH D k n sr D' n' H (fun c Hc => Hold c (or_intror Hc)))
        as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
      refine (conj H1 (conj H2 (conj H3 (conj _ (conj H5 (conj H6 _)))))).
      * intros q Hq. apply H4. intros Hin. apply Hq. right. exact Hin.
      * intros q [->|Hq].
        -- destruct (in_dec Atom.eq_dec q l) as [Hin|Hnin].
           ++ exact (H7 q Hin).
           ++ exists q. rewrite (H4 q Hnin). split; [ reflexivity | ].
              rewrite (H6 q (Hold q (or_introl eq_refl))). exact Ef.
        -- exact (H7 q Hq).
    + destruct (push_sort_r (rupd D (ea n) (RK k (rk_lacks (drk D b)))) k l (Datatypes.S n))
        as [[s1 D1] n1] eqn:E.
      inversion H; subst; clear H.
      assert (Hold' : forall c, In c l -> old (Datatypes.S n) c).
      { intros c Hc m Hm. apply (Hold c (or_intror Hc)). lia. }
      destruct (IH _ _ _ _ _ _ E Hold') as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
      assert (Hnl : ~ In (ea n) l).
      { intros Hin. exact (Hold (ea n) (or_intror Hin) n (le_n n) eq_refl). }
      assert (Hs1 : sR s1 (ea n) = row_Var (ea n)) by exact (H4 _ Hnl).
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      * intros x. change (apT s1 (sT (sbR b (row_Var (ea n))) x) = typ_Var x).
        cbn [sT sbR]. unfold idt. cbn [apT ap_typ]. exact (H1 x).
      * lia.
      * rewrite H3. reflexivity.
      * intros q Hq. change (apR s1 (sR (sbR b (row_Var (ea n))) q) = row_Var q).
        cbn [sR sbR]. destruct (Atom.eq_dec q b) as [->|Hne].
        -- exfalso. apply Hq. left. reflexivity.
        -- change (sR s1 q = row_Var q). apply H4. intros Hin. apply Hq. right. exact Hin.
      * intros q. change (exists q', apR s1 (sR (sbR b (row_Var (ea n))) q) = row_Var q').
        cbn [sR sbR]. destruct (Atom.eq_dec q b) as [->|Hne].
        -- exists (ea n). exact Hs1.
        -- exact (H5 q).
      * intros q Hq. rewrite (H6 q).
        -- cbn [drk rupd]. destruct (Atom.eq_dec q (ea n)) as [E2|_]; [ | reflexivity ].
           exfalso. exact (Hq n (le_n n) E2).
        -- intros m Hm. apply Hq. lia.
      * intros q Hq. destruct (Atom.eq_dec q b) as [->|Hqb].
        -- exists (ea n). split.
           ++ change (apR s1 (sR (sbR b (row_Var (ea n))) b) = row_Var (ea n)).
              cbn [sR sbR]. rewrite dec_same. exact Hs1.
           ++ rewrite (H6 (ea n)).
              ** cbn [drk rupd]. rewrite dec_same. cbn [rk_sort]. apply finer_b_refl.
              ** intros m Hm E2. apply ea_inj in E2. lia.
        -- assert (Hx' : In q l) by (destruct Hq as [Eq0|Hq]; [ exfalso; apply Hqb; symmetry; exact Eq0 | exact Hq ]).
           destruct (H7 q Hx') as (y & Hy & Hf). exists y. split; [ | exact Hf ].
           change (apR s1 (sR (sbR b (row_Var (ea n))) q) = row_Var y).
           cbn [sR sbR]. rewrite (dec_diff _ _ _ _ _ Hqb). exact Hy.
Qed.

Lemma push_sort_dok : forall l D k n sp D' n',
  push_sort D k l n = (sp, D', n') -> DOk D n -> DOk D' n'.
Proof.
  induction l as [|b l IH]; intros D k n sp D' n' H Hd; cbn [push_sort] in H.
  - inversion H; subst. exact Hd.
  - destruct (finer_b (D b) k).
    + exact (IH _ _ _ _ _ _ H Hd).
    + destruct (push_sort (upd D (ea n) k) k l (Datatypes.S n)) as [[s1 D1] n1] eqn:E.
      inversion H; subst. exact (IH _ _ _ _ _ _ E (DOk_upd D n k Hd)).
Qed.

Lemma push_sort_r_dok : forall l D k n sr D' n',
  push_sort_r D k l n = (sr, D', n') -> DOk D n -> DOk D' n'.
Proof.
  induction l as [|b l IH]; intros D k n sr D' n' H Hd; cbn [push_sort_r] in H.
  - inversion H; subst. exact Hd.
  - destruct (finer_b (rk_sort (drk D b)) k).
    + exact (IH _ _ _ _ _ _ H Hd).
    + destruct (push_sort_r (rupd D (ea n) (RK k (rk_lacks (drk D b)))) k l (Datatypes.S n))
        as [[s1 D1] n1] eqn:E.
      inversion H; subst. exact (IH _ _ _ _ _ _ E (DOk_rupd D n _ Hd)).
Qed.

(* ---- a plain type, and the entries whose field the sort reaches ---- *)

Fixpoint pf (T : typ) {struct T} : Prop :=
  match T with
  | typ_Int | typ_Float | typ_Bool | typ_Unit | typ_String | typ_Var _ => True
  | typ_Arrow A B => pf A /\ pf B
  | typ_Record R => prf R
  | _ => False
  end
with prf (R : row) {struct R} : Prop :=
  match R with
  | row_Empty | row_Var _ => True
  | row_Ext _ T R' => pf T /\ prf R'
  | row_Maybe _ P T R' => pf P /\ pf T /\ prf R'
  end.

(* An entry whose presence [S] makes absent keeps a field that satisfies the
   sort, as the algorithm checks it. *)
Fixpoint fld (D1 : denv) (S : sub) (k : sort) (T : typ) {struct T} : Prop :=
  match T with
  | typ_Arrow A B => fld D1 S k A /\ fld D1 S k B
  | typ_Record R => frld D1 S k R
  | _ => True
  end
with frld (D1 : denv) (S : sub) (k : sort) (R : row) {struct R} : Prop :=
  match R with
  | row_Ext _ T R' => fld D1 S k T /\ frld D1 S k R'
  | row_Maybe _ P T R' =>
      (apT S P = typ_Bool -> sat D1 k (apT S T)) /\ sat D1 k (apT S P) /\
      fld D1 S k P /\ fld D1 S k T /\ frld D1 S k R'
  | _ => True
  end.

(* A type whose variables [ren] sends to variables of a finer sort satisfies
   the sort when its image under [Sg] does, given the field condition. *)
Lemma sat_ren_mut : forall (D2 D1 : denv) Sg ren k,
  (forall T, pf T -> fld D1 Sg k T ->
     (forall x, x `in` ftv_typ T -> exists y, sT ren x = typ_Var y /\ finer (D2 y) k) ->
     (forall q, q `in` frv_typ T -> exists q', sR ren q = row_Var q' /\ finer (rk_sort (drk D2 q')) k) ->
     sat D1 k (apT Sg T) -> sat D2 k (apT ren T)) /\
  (forall R, prf R -> frld D1 Sg k R ->
     (forall x, x `in` ftv_row R -> exists y, sT ren x = typ_Var y /\ finer (D2 y) k) ->
     (forall q, q `in` frv_row R -> exists q', sR ren q = row_Var q' /\ finer (rk_sort (drk D2 q')) k) ->
     rsat D1 k (apR Sg R) -> rsat D2 k (apR ren R)).
Proof.
  intros D2 D1 Sg ren k. unfold apT, apR. apply typ_row_mutind.
  - intros _ _ _ _ Hs. simpl in Hs |- *. exact Hs.
  - intros _ _ _ _ Hs. simpl in Hs |- *. exact Hs.
  - intros _ _ _ _ Hs. simpl in Hs |- *. exact Hs.
  - intros _ _ _ _ Hs. simpl in Hs |- *. exact Hs.
  - intros _ _ _ _ Hs. simpl in Hs |- *. exact Hs.
  - intros A IHA B IHB _ _ _ _ Hs. simpl in Hs |- *. exact Hs.
  - intros R IH Hpf Hfld Hv Hq Hs. simpl in Hpf, Hfld, Hv, Hq, Hs |- *.
    destruct k; first [ exact I | contradiction | exact (IH Hpf Hfld Hv Hq Hs) ].
  - intros x _ _ Hv _ _. simpl.
    destruct (Hv x ltac:(simpl; fsetdec)) as (y & E & Hf). rewrite E. simpl. exact Hf.
  - intros i Hpf. simpl in Hpf. contradiction.
  - intros B IH Hpf. simpl in Hpf. contradiction.
  - intros w B IH Hpf. simpl in Hpf. contradiction.
  - intros _ _ _ _ _. simpl. exact I.
  - intros r _ _ _ Hq _. simpl.
    destruct (Hq r ltac:(simpl; fsetdec)) as (q' & E & Hf). rewrite E. simpl. exact Hf.
  - intros l T IHT R IHR Hpf Hfld Hv Hq Hs. simpl in Hpf, Hfld, Hs |- *.
    destruct Hpf as [HpT HpR]. destruct Hfld as [HfT HfR]. destruct Hs as [HsT HsR]. split.
    + apply IHT; [ exact HpT | exact HfT | | | exact HsT ];
        [ intros x Hx; apply Hv; simpl; fsetdec | intros q Hx; apply Hq; simpl; fsetdec ].
    + apply IHR; [ exact HpR | exact HfR | | | exact HsR ];
        [ intros x Hx; apply Hv; simpl; fsetdec | intros q Hx; apply Hq; simpl; fsetdec ].
  - intros l P IHP T IHT R IHR Hpf Hfld Hv Hq Hs. simpl in Hpf, Hfld, Hs |- *.
    destruct Hpf as [HpP [HpT HpR]]. destruct Hfld as [HeP [_ [_ [HfT HfR]]]].
    destruct Hs as [HsP HsR]. split.
    + right. apply IHT; [ exact HpT | exact HfT | | | ];
        [ intros x Hx; apply Hv; simpl; fsetdec | intros q Hx; apply Hq; simpl; fsetdec | ].
      destruct HsP as [E|HsT]; [ exact (HeP E) | exact HsT ].
    + apply IHR; [ exact HpR | exact HfR | | | exact HsR ];
        [ intros x Hx; apply Hv; simpl; fsetdec | intros q Hx; apply Hq; simpl; fsetdec ].
Qed.

(* ---- the sort reaches the variables of a type that satisfies it ---- *)

Lemma sat_reach_mut : forall (D1 : denv) S k,
  (forall T, pf T -> fld D1 S k T -> sat D1 k (apT S T) ->
     (forall b, b `in` ftv_typ T -> sat D1 k (sT S b)) /\
     (forall q, q `in` frv_typ T -> rsat D1 k (sR S q))) /\
  (forall R, prf R -> frld D1 S k R -> rsat D1 k (apR S R) ->
     (forall b, b `in` ftv_row R -> sat D1 k (sT S b)) /\
     (forall q, q `in` frv_row R -> rsat D1 k (sR S q))).
Proof.
  intros D1 S k. unfold apT, apR. apply typ_row_mutind.
  - intros _ _ _. split; intros x Hx; exfalso; simpl in Hx; fsetdec.
  - intros _ _ _. split; intros x Hx; exfalso; simpl in Hx; fsetdec.
  - intros _ _ _. split; intros x Hx; exfalso; simpl in Hx; fsetdec.
  - intros _ _ _. split; intros x Hx; exfalso; simpl in Hx; fsetdec.
  - intros _ _ _. split; intros x Hx; exfalso; simpl in Hx; fsetdec.
  - intros A IHA B IHB _ _ Hs. simpl in Hs. subst k. split; intros; [ apply sat_any | apply rsat_any ].
  - intros R IH Hpf Hfld Hs. simpl in Hpf, Hfld, Hs |- *.
    destruct k; first [ split; intros; [ apply sat_any | apply rsat_any ] | contradiction
                      | exact (IH Hpf Hfld Hs) ].
  - intros x _ _ Hs. simpl in Hs |- *. split.
    + intros b Hb. apply AtomSetFacts.singleton_iff in Hb. subst. exact Hs.
    + intros q Hq. exfalso. fsetdec.
  - intros i Hpf. simpl in Hpf. contradiction.
  - intros B IH Hpf. simpl in Hpf. contradiction.
  - intros w B IH Hpf. simpl in Hpf. contradiction.
  - intros _ _ _. split; intros x Hx; exfalso; simpl in Hx; fsetdec.
  - intros r _ _ Hs. simpl in Hs |- *. split.
    + intros b Hb. exfalso. fsetdec.
    + intros q Hq. apply AtomSetFacts.singleton_iff in Hq. subst. exact Hs.
  - intros l T IHT R IHR Hpf Hfld Hs. simpl in Hpf, Hfld, Hs |- *.
    destruct Hpf as [HpT HpR]. destruct Hfld as [HfT HfR]. destruct Hs as [HsT HsR].
    destruct (IHT HpT HfT HsT) as [T1 T2]. destruct (IHR HpR HfR HsR) as [R1 R2]. split.
    + intros b Hb. apply AtomSetFacts.union_iff in Hb. destruct Hb as [H|H]; [ apply T1 | apply R1 ]; exact H.
    + intros q Hq. apply AtomSetFacts.union_iff in Hq. destruct Hq as [H|H]; [ apply T2 | apply R2 ]; exact H.
  - intros l P IHP T IHT R IHR Hpf Hfld Hs. simpl in Hpf, Hfld, Hs |- *.
    destruct Hpf as [HpP [HpT HpR]]. destruct Hfld as [HeP [HsPP [HfP [HfT HfR]]]].
    destruct Hs as [HsP HsR].
    assert (HsT : sat D1 k (ap_typ (sT S) (sR S) T))
      by (destruct HsP as [E|H]; [ exact (HeP E) | exact H ]).
    destruct (IHP HpP HfP HsPP) as [P1 P2].
    destruct (IHT HpT HfT HsT) as [T1 T2]. destruct (IHR HpR HfR HsR) as [R1 R2]. split.
    + intros b Hb. apply AtomSetFacts.union_iff in Hb. destruct Hb as [H|H]; [ apply P1; exact H | ].
      apply AtomSetFacts.union_iff in H. destruct H as [H|H]; [ apply T1 | apply R1 ]; exact H.
    + intros q Hq. apply AtomSetFacts.union_iff in Hq. destruct Hq as [H|H]; [ apply P2; exact H | ].
      apply AtomSetFacts.union_iff in H. destruct H as [H|H]; [ apply T2 | apply R2 ]; exact H.
Qed.

(* ---- renaming by variables keeps a type locally closed ---- *)

Lemma lcb_ap_var : forall (st : tsub) (sr : rsub),
  (forall x, exists y, st x = typ_Var y) -> (forall q, exists q', sr q = row_Var q') ->
  (forall T k, lcb k (ap_typ st sr T) = lcb k T) /\
  (forall R k, lcrb k (ap_row st sr R) = lcrb k R).
Proof.
  intros st sr Hs Hr. apply typ_row_mutind; simpl; intros; try reflexivity.
  - rewrite H, H0. reflexivity.
  - apply H.
  - destruct (Hs a) as [y ->]. reflexivity.
  - apply H.
  - apply H.
  - destruct (Hr r) as [q ->]. reflexivity.
  - rewrite H, H0. reflexivity.
  - rewrite H, H0, H1. reflexivity.
Qed.

Lemma ftv_ren : forall sp sr T y,
  (forall x, exists y', sT sp x = typ_Var y') -> (forall x, sT sr x = typ_Var x) ->
  (forall r, exists r', sR sp r = row_Var r') -> (forall r, exists r', sR sr r = row_Var r') ->
  y `in` ftv_typ (apT sr (apT sp T)) -> exists x, x `in` ftv_typ T /\ sT sp x = typ_Var y.
Proof.
  intros sp sr T y Hp Hr Hpr Hrr H. unfold apT in H.
  apply ftv_ap_typ in H. destruct H as [[b [Hb H]]|[p [Hp' H]]].
  - rewrite (Hr b) in H. simpl in H. apply AtomSetFacts.singleton_iff in H. subst b.
    apply ftv_ap_typ in Hb. destruct Hb as [[x [Hx Hy]]|[p [Hp' Hy]]].
    + destruct (Hp x) as [y' E]. rewrite E in Hy. simpl in Hy.
      apply AtomSetFacts.singleton_iff in Hy. subst y'. exists x. split; [ exact Hx | exact E ].
    + destruct (Hpr p) as [r' E]. rewrite E in Hy. simpl in Hy. exfalso. fsetdec.
  - destruct (Hrr p) as [r' E]. rewrite E in H. simpl in H. exfalso. fsetdec.
Qed.

(* ---- [bind_prop] with sorts ---- *)

(* The sort of a variable's image carries across conversion at the
   environment: [nfT D] only drops absent entries, which no sort reads. *)
Lemma sat_teqD : forall D k T T', teqD D T T' -> sat D k T -> sat D k T'.
Proof.
  intros D k T T' H Hs. apply (proj1 (sat_nf D k T')). apply (sat_teq D k _ _ H).
  apply (proj2 (sat_nf D k T)). exact Hs.
Qed.

(* The theorem below reads its hypothesis and states its factoring at one of two
   conversions: [teqD] at the environment ([b = true]), or plain [teq] ([b = false]),
   which a caller whose types carry no absent entry to normalize needs. *)
Definition teqX (b : bool) (D : denv) (T T' : typ) : Prop :=
  if b then teqD D T T' else teq T T'.

Lemma teqX_refl : forall b D T, teqX b D T T.
Proof. intros [] D T; [ apply teqD_refl | apply teq_refl ]. Qed.

Lemma sat_teqX : forall b D k T T', teqX b D T T' -> sat D k T -> sat D k T'.
Proof.
  intros [] D k T T' H Hs; [ exact (sat_teqD D k T T' H Hs) | exact (sat_teq D k T T' H Hs) ].
Qed.

Section PropX.

Variable bx : bool.

Theorem bind_prop_sorted_complete : forall (D D1 : denv) Sg a T n,
  DOk D n -> KR D D1 Sg -> old n a -> a `notin` ftv_typ T ->
  (forall b, b `in` ftv_typ T -> old n b) -> (forall q, q `in` frv_typ T -> old n q) ->
  pf T -> lcb 0 T = true -> fld D1 Sg (D a) T -> teqX bx D1 (sT Sg a) (apT Sg T) ->
  exists s D' n' S2, bind_prop D a T n = Some (s, D', n') /\ KR D' D1 S2 /\
    n <= n' /\ DOk D' n' /\
    (forall x, old n x -> teqX bx D1 (sT Sg x) (apT S2 (sT s x))) /\
    (forall r, old n r -> sR Sg r = apR S2 (sR s r)).
Proof.
  intros D D1 Sg a T n Hd HK Ha Hna Hot Hoq Hpf Hlc Hfld Heq.
  assert (Hsa : sat D1 (D a) (apT Sg T)).
  { apply (sat_teqX bx D1 (D a) (sT Sg a) (apT Sg T) Heq). exact (proj1 HK a). }
  destruct (sat_reach_mut D1 Sg (D a)) as [Hrt _].
  destruct (Hrt T Hpf Hfld Hsa) as [Hreach_t Hreach_r].
  assert (Holdl : forall b, In b (AtomSetImpl.elements (ftv_typ T)) -> old n b)
    by (intros b Hb; apply Hot; apply in_elts; exact Hb).
  assert (Holdr : forall q, In q (AtomSetImpl.elements (frv_typ T)) -> old n q)
    by (intros q Hq; apply Hoq; apply in_elts; exact Hq).
  assert (Hnl : ~ In a (AtomSetImpl.elements (ftv_typ T))) by (intros H; apply Hna; apply in_elts; exact H).
  assert (Hocc : occT a T = false).
  { unfold occT. apply Bool.orb_false_iff. split.
    - apply AtomSetFacts.not_mem_iff. exact Hna.
    - rewrite Hlc. reflexivity. }
  unfold bind_prop. rewrite Hocc.
  destruct (push_sort D (D a) (AtomSetImpl.elements (ftv_typ T)) n) as [[sp D1'] n1] eqn:Ep.
  destruct (push_sort_facts _ _ _ _ _ _ _ Ep Holdl) as (P1 & P2 & P3 & P4 & P5 & P6).
  pose proof (push_sort_dok _ _ _ _ _ _ _ Ep Hd) as Hd1.
  destruct (push_sort_complete _ _ _ _ Sg D1 Hd HK
              (fun b Hb => Hreach_t b (proj1 (in_elts _ _) Hb)) Holdl sp D1' n1 Ep)
    as (S2a & K1 & R1 & F1).
  rewrite (P5 a Ha). cbn match.
  destruct (push_sort_r D1' (D a) (AtomSetImpl.elements (frv_typ T)) n1) as [[sr D2] n2] eqn:Er.
  assert (Holdr1 : forall q, In q (AtomSetImpl.elements (frv_typ T)) -> old n1 q).
  { intros q Hq m Hm. apply (Holdr q Hq). lia. }
  destruct (push_sort_r_facts _ _ _ _ _ _ _ Er Holdr1) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  destruct (push_sort_r_complete _ _ _ (D a) S2a D1 Hd1 K1
              (fun q Hq => ltac:(rewrite R1; exact (Hreach_r q (proj1 (in_elts _ _) Hq)))) Holdr1
              sr D2 n2 Er) as (S2b & K2 & T2 & Rq).
  assert (Hvp : forall x, exists y, sT sp x = typ_Var y)
    by (intros x; destruct (P4 x) as (y & E & _); exists y; exact E).
  assert (Hsrx : forall r, exists r', sR sp r = row_Var r')
    by (intros r; exists r; apply P1).
  set (T' := apT sr (apT sp T)).
  assert (Hocc' : occT a T' = false).
  { unfold occT. apply Bool.orb_false_iff. split.
    - apply AtomSetFacts.not_mem_iff. intros Hin.
      destruct (ftv_ren sp sr T a Hvp Q1 Hsrx Q5 Hin) as (x & Hx & E).
      destruct (P4 x) as (y & E' & Hc). rewrite E in E'. injection E' as Hay.
      destruct Hc as [Hy|[m [Hm Hy]]].
      + apply Hna. rewrite Hay, Hy. exact Hx.
      + exact (Ha m Hm (eq_trans Hay Hy)).
    - unfold T', apT. rewrite (proj1 (lcb_ap_var (sT sr) (sR sr) (fun x => ex_intro _ x (Q1 x)) Q5) _ 0).
      rewrite (proj1 (lcb_ap_var (sT sp) (sR sp) Hvp Hsrx) T 0). rewrite Hlc. reflexivity. }
  cbn zeta. rewrite Hocc'.
  assert (Hsat : sat D2 (D a) T').
  { assert (HD2 : forall y, D2 y = D1' y) by (intros y; change (dsort D2 y = dsort D1' y); rewrite Q3; reflexivity).
    unfold T'. rewrite (apT_comp sr sp T).
    apply (proj1 (sat_ren_mut D2 D1 Sg (scomp sr sp) (D a)) T Hpf Hfld).
    - intros x Hx. destruct (P6 x (proj2 (in_elts _ _) Hx)) as (y & Ey & Hf).
      exists y. split.
      + change (apT sr (sT sp x) = typ_Var y). rewrite Ey. unfold apT. simpl. apply Q1.
      + rewrite HD2. apply finer_b_iff. exact Hf.
    - intros q Hq. destruct (Q7 q (proj2 (in_elts _ _) Hq)) as (q' & Eq0 & Hf).
      exists q'. split.
      + change (apR sr (sR sp q) = row_Var q'). rewrite (P1 q). unfold apR. simpl. exact Eq0.
      + apply finer_b_iff. exact Hf.
    - exact Hsa. }
  assert (Hsb : sat_b D2 (D a) T' = true).
  { apply sat_b_iff. exact Hsat. }
  assert (HD2a : D2 a = D a).
  { change (dsort D2 a = D a). rewrite Q3. exact (P5 a Ha). }
  rewrite HD2a, Hsb.
  assert (Hrv : forall y, apT sr (typ_Var y) = typ_Var y) by (intros y; unfold apT; simpl; apply Q1).
  assert (Hsv : forall S y, apT S (typ_Var y) = sT S y) by (intros S y; reflexivity).
  assert (Hagree : apT S2b T' = apT Sg T).
  { unfold T'. rewrite (apT_comp sr sp T), (apT_comp S2b (scomp sr sp) T). unfold apT. apply ap_typ_ext.
    - intros x Hx. change (apT S2b (apT sr (sT sp x)) = sT Sg x).
      destruct (Hvp x) as [y Ey]. rewrite Ey, Hrv, Hsv.
      rewrite (F1 x (Hot x Hx)), Ey, Hsv, T2. reflexivity.
    - intros q Hq. change (apR S2b (apR sr (sR sp q)) = sR Sg q).
      rewrite (P1 q). unfold apR at 2. simpl.
      pose proof (Rq q (fun m Hm => Hoq q Hq m ltac:(lia))) as E. rewrite R1 in E.
      symmetry. exact E. }
  eexists. exists D2, n2, S2b. split; [ reflexivity | ]. split; [ exact K2 | ].
  split; [ lia | split; [ exact (push_sort_r_dok _ _ _ _ _ _ _ Er Hd1) | split ] ].
  - intros x Hx. destruct (Atom.eq_dec x a) as [->|Hne].
    + change (teqX bx D1 (sT Sg a) (apT S2b (apT (sbT a T') (apT sr (sT sp a))))).
      rewrite (P3 a Hnl), Hrv, Hsv. cbn [sT sbT]. rewrite dec_same.
      rewrite Hagree. exact Heq.
    + change (teqX bx D1 (sT Sg x) (apT S2b (apT (sbT a T') (apT sr (sT sp x))))).
      destruct (P4 x) as (y & Ey & Hy). rewrite Ey, Hrv, Hsv.
      assert (Hya : y <> a).
      { intros ->. destruct Hy as [Hy|[m [Hm Hy]]]; [ apply Hne; symmetry; exact Hy | exact (Ha m Hm Hy) ]. }
      cbn [sT sbT]. rewrite (dec_diff _ _ _ _ _ Hya).
      rewrite (F1 x Hx), Ey, Hsv, Hsv, T2. apply teqX_refl.
  - intros r Hr. change (sR Sg r = apR S2b (apR (sbT a T') (apR sr (sR sp r)))).
    rewrite (P1 r). destruct (Q5 r) as [r' E'].
    assert (Hrr : apR sr (row_Var r) = row_Var r') by (unfold apR; simpl; exact E').
    assert (Hb : apR (sbT a T') (row_Var r') = row_Var r') by reflexivity.
    rewrite Hrr, Hb.
    pose proof (Rq r (fun m Hm => Hr m ltac:(lia))) as E. rewrite R1, E' in E.
    exact E.
Qed.

End PropX.
