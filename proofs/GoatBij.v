(* Freshening infrastructure toward the two remaining HM admits in GoatSubst.v
   (typing_weaken = L4, typing_tsubst_fix = L5; issue #151).

   Closing those lemmas' [T-Let] case means renaming the let-generalized type/row
   variables to atoms fresh for the inserted/substituted context before [gen]
   lines up.  Because the variables are metalib [atom]s, that renaming is a
   concrete finite permutation, built here and fed to [GoatSubst.typing_rename]:

   - [transp]/[perm]: a finite composition of atom transpositions, with
     [perm_invol] (an involution on a duplicate-free support, so it is its own
     inverse -- exactly the bijection [typing_rename] wants).
   - [fresh_list], [mk_rename]: package a bijection that fixes a chosen finite
     set and maps a chosen finite set [V] to atoms fresh for an avoid-set.
   - [sch_more_gen_ren]: alpha-renaming a scheme's quantified variables (any
     bijection fixing the scheme's FREE variables) preserves its instance set --
     the step that lets [typing_ftv_mono] swap a renamed generalization in.  The
     instance witness is rebuilt pointwise using decidable [atom] membership,
     which is what the set representation (#151) unlocks.
   - [ctx_more_gen_ren]: the same, pointwise over a context.

   This is the reusable core of the sub-development ADR 0008 budgets separately.
   It does not itself discharge an admit: the remaining obstruction is the case
   where a generalized variable occurs free in BOTH the result type and the
   inserted block, which forces re-choosing the body's instance substitutions
   rather than renaming atoms (see the [typing_weaken] comment in GoatSubst.v). *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Coq.Lists.List.
Import ListNotations.


Definition transp (a b x : atom) : atom :=
  if x == a then b else if x == b then a else x.

Lemma transp_fix : forall a b x, x <> a -> x <> b -> transp a b x = x.
Proof. intros a b x Ha Hb. unfold transp. destruct (x == a); [contradiction|]. destruct (x==b); [contradiction|]. reflexivity. Qed.

Lemma transp_l : forall a b, transp a b a = b.
Proof. intros a b. unfold transp. destruct (a==a);[reflexivity|contradiction]. Qed.

Lemma transp_invol : forall a b x, transp a b (transp a b x) = x.
Proof.
  intros a b x. unfold transp.
  destruct (x==a) as [E1|N1].
  - subst x. destruct (b==a) as [E2|N2].
    + subst b. destruct (a==a);[reflexivity|contradiction].
    + destruct (b==b);[reflexivity|contradiction].
  - destruct (x==b) as [E2|N2].
    + subst x. destruct (a==a);[reflexivity|contradiction].
    + destruct (x==a);[contradiction|]. destruct (x==b);[contradiction|reflexivity].
Qed.

Lemma transp_in : forall a b x, transp a b x = a \/ transp a b x = b \/ transp a b x = x.
Proof.
  intros a b x. unfold transp. destruct (x==a). right;left;auto.
  destruct (x==b). left;auto. right;right;auto.
Qed.

Fixpoint perm (l : list (atom*atom)) (x:atom) : atom :=
  match l with
  | [] => x
  | (a,b)::l' => transp a b (perm l' x)
  end.

Fixpoint supp (l : list (atom*atom)) : list atom :=
  match l with [] => [] | (a,b)::l' => a :: b :: supp l' end.

Lemma perm_fix : forall l x, ~ In x (supp l) -> perm l x = x.
Proof.
  induction l as [|[a b] l IH]; intros x H; simpl in *.
  - reflexivity.
  - assert (x <> a) by (intro; subst; apply H; simpl; auto).
    assert (x <> b) by (intro; subst; apply H; simpl; auto).
    rewrite IH by (intro HC; apply H; simpl; auto).
    apply transp_fix; auto.
Qed.

Lemma perm_range : forall l x, perm l x = x \/ In (perm l x) (supp l).
Proof.
  induction l as [|[a b] l IH]; intros x; simpl.
  - left; auto.
  - destruct (transp_in a b (perm l x)) as [E|[E|E]]; rewrite E.
    + right. left. reflexivity.
    + right. right. left. reflexivity.
    + destruct (IH x) as [E2|E2].
      * left; exact E2.
      * right. right. right. exact E2.
Qed.

Lemma perm_transp_comm : forall l a b y,
  ~ In a (supp l) -> ~ In b (supp l) ->
  perm l (transp a b y) = transp a b (perm l y).
Proof.
  intros l a b y Ha Hb.
  assert (Fa : perm l a = a) by (apply perm_fix; auto).
  assert (Fb : perm l b = b) by (apply perm_fix; auto).
  destruct (y == a) as [Ey|Ny].
  - subst y. rewrite transp_l, Fb, Fa, transp_l. reflexivity.
  - destruct (y == b) as [Eyb|Nyb].
    + subst y. rewrite Fb. apply perm_fix.
      destruct (transp_in a b b) as [E|[E|E]]; rewrite E; auto.
    + rewrite (transp_fix a b y Ny Nyb).
      assert (Pa: perm l y <> a) by
        (destruct (perm_range l y) as [Eq|Hin]; [ rewrite Eq; auto | intro HC; apply Ha; rewrite <- HC; auto ]).
      assert (Pb: perm l y <> b) by
        (destruct (perm_range l y) as [Eq|Hin]; [ rewrite Eq; auto | intro HC; apply Hb; rewrite <- HC; auto ]).
      rewrite (transp_fix a b (perm l y) Pa Pb). reflexivity.
Qed.

Lemma perm_invol : forall l,
  NoDup (supp l) ->
  forall x, perm l (perm l x) = x.
Proof.
  induction l as [|[a b] l IH]; intros Hnd x; simpl.
  - reflexivity.
  - simpl in Hnd. inversion Hnd as [|? ? Ha Hnd']; subst.
    inversion Hnd' as [|? ? Hb Hnd'']; subst.
    assert (~ In a (supp l)) by (intro; apply Ha; simpl; auto).
    assert (~ In b (supp l)) by (intro; apply Hb; auto).
    rewrite perm_transp_comm by auto.
    rewrite transp_invol.
    apply IH; auto.
Qed.

(* build a fresh distinct list of length n, avoiding a set *)
Fixpoint fresh_list (n:nat) (avoid:atoms) : list atom :=
  match n with
  | 0 => []
  | S k => let a := proj1_sig (atom_fresh avoid) in a :: fresh_list k (avoid \u {{a}})
  end.

Lemma fresh_list_length : forall n avoid, length (fresh_list n avoid) = n.
Proof. induction n; intros; simpl; auto. Qed.

(* every element of the list avoids the original avoid set *)
Lemma fresh_list_avoid : forall n avoid x,
  In x (fresh_list n avoid) -> x `notin` avoid.
Proof.
  induction n as [|k IH]; intros avoid x H; simpl in H.
  - inversion H.
  - destruct (atom_fresh avoid) as [a Ha]. simpl in H.
    destruct H as [E|H].
    + subst x; auto.
    + specialize (IH _ _ H). fsetdec.
Qed.

Lemma fresh_list_nodup : forall n avoid, NoDup (fresh_list n avoid).
Proof.
  induction n as [|k IH]; intros avoid; simpl.
  - constructor.
  - destruct (atom_fresh avoid) as [a Ha]. simpl. constructor.
    + intro HC. apply (fresh_list_avoid k (avoid \u {{a}}) a) in HC. fsetdec.
    + apply IH.
Qed.

Lemma In_supp_combine : forall vl nl x,
  length vl = length nl ->
  (In x (supp (combine vl nl)) <-> In x vl \/ In x nl).
Proof.
  induction vl as [|v vl IH]; intros nl x Hlen; destruct nl as [|n nl]; simpl in *; try discriminate.
  - tauto.
  - inversion Hlen as [Hlen']. specialize (IH nl x Hlen'). simpl. tauto.
Qed.

Lemma nodup_supp_combine : forall vl nl,
  length vl = length nl ->
  NoDup vl -> NoDup nl -> (forall x, In x vl -> ~ In x nl) ->
  NoDup (supp (combine vl nl)).
Proof.
  induction vl as [|v vl IH]; intros nl Hlen Hv Hn Hdisj; destruct nl as [|n nl]; simpl in *; try discriminate.
  - constructor.
  - inversion Hlen as [Hlen']. inversion Hv as [|? ? Hvv Hv']; subst.
    inversion Hn as [|? ? Hnn Hn']; subst.
    assert (Hd' : forall x, In x vl -> ~ In x nl) by (intros x Hx HC; apply (Hdisj x); simpl; auto).
    assert (Hsub := IH nl Hlen' Hv' Hn' Hd').
    constructor.
    + (* v not in n :: supp(combine vl nl) *)
      simpl. intros [E|HC].
      * subst n. apply (Hdisj v); simpl; auto.
      * apply In_supp_combine in HC; auto. destruct HC as [HC|HC].
        -- contradiction.
        -- apply (Hdisj v); simpl; auto.
    + constructor.
      * (* n not in supp(combine vl nl) *)
        intro HC. apply In_supp_combine in HC; auto. destruct HC as [HC|HC].
        -- apply (Hdisj n); simpl; auto.
        -- contradiction.
      * exact Hsub.
Qed.

Lemma perm_combine_img : forall vl nl,
  length vl = length nl ->
  NoDup vl -> NoDup nl -> (forall x, In x vl -> ~ In x nl) ->
  forall a, In a vl -> In (perm (combine vl nl) a) nl.
Proof.
  induction vl as [|v vl IH]; intros nl Hlen Hv Hn Hdisj a Ha; destruct nl as [|n nl]; simpl in *; try discriminate.
  - inversion Ha.
  - inversion Hlen as [Hlen']. inversion Hv as [|? ? Hvv Hv']; subst.
    inversion Hn as [|? ? Hnn Hn']; subst.
    assert (Hd' : forall x, In x vl -> ~ In x nl) by (intros x Hx HC; apply (Hdisj x); simpl; auto).
    destruct Ha as [E|Ha].
    + subst a. rewrite perm_fix.
      * rewrite transp_l. simpl; auto.
      * rewrite In_supp_combine by auto. intros [HC|HC]; [ contradiction | apply (Hdisj v); simpl; auto ].
    + assert (Hin := IH nl Hlen' Hv' Hn' Hd' a Ha).
      assert (Hmv : perm (combine vl nl) a <> v).
      { intro HC. apply (Hdisj v (or_introl eq_refl)). right. rewrite <- HC. exact Hin. }
      assert (Hmn : perm (combine vl nl) a <> n).
      { intro HC. apply Hnn. rewrite <- HC. exact Hin. }
      rewrite (transp_fix v n (perm (combine vl nl) a) Hmv Hmn).
      right; exact Hin.
Qed.

Lemma In_elements : forall a S, In a (AtomSetImpl.elements S) <-> a `in` S.
Proof.
  intros a S. split; intro H.
  - apply AtomSetImpl.elements_2. apply (In_InA eq_equivalence). exact H.
  - apply AtomSetImpl.elements_1 in H. apply InA_alt in H.
    destruct H as [y [Hy Hin]]. subst; auto.
Qed.

Lemma NoDup_elements : forall S, NoDup (AtomSetImpl.elements S).
Proof.
  intros S. pose proof (AtomSetImpl.elements_3w S) as H.
  induction H as [|x l Hx Hl IH]; constructor; auto.
  intro HC. apply Hx. apply In_InA; [ apply eq_equivalence | exact HC ].
Qed.

Lemma mk_rename : forall (V B : atoms),
  exists (f : atom -> atom) (N : list atom),
    (forall x, f (f x) = x) /\
    (forall x, In x N -> x `notin` B) /\
    (forall x, In x N -> x `notin` V) /\
    (forall x, x `in` V -> In (f x) N) /\
    (forall x, x `notin` V -> ~ In x N -> f x = x).
Proof.
  intros V B.
  set (vl := AtomSetImpl.elements V).
  set (nt := fresh_list (length vl) (B \u V)).
  assert (Hlen : length vl = length nt) by (unfold nt; rewrite fresh_list_length; reflexivity).
  assert (Hnv : NoDup vl) by apply NoDup_elements.
  assert (Hnn : NoDup nt) by (unfold nt; apply fresh_list_nodup).
  assert (Hntavoid : forall x, In x nt -> x `notin` (B \u V))
    by (intros x Hx; unfold nt in Hx; apply (fresh_list_avoid _ _ _ Hx)).
  assert (Hdisj : forall x, In x vl -> ~ In x nt).
  { intros x Hx HC. apply (Hntavoid x HC). apply In_elements in Hx. fsetdec. }
  exists (perm (combine vl nt)), nt.
  repeat split.
  - apply perm_invol. apply nodup_supp_combine; auto.
  - intros x Hx. specialize (Hntavoid x Hx). fsetdec.
  - intros x Hx. specialize (Hntavoid x Hx). fsetdec.
  - intros x Hx. apply perm_combine_img; auto. apply In_elements; auto.
  - intros x HxV HxN. apply perm_fix.
    rewrite In_supp_combine by auto. intros [HC|HC].
    + apply HxV. apply In_elements; auto.
    + contradiction.
Qed.

(* ============ alpha-renaming of a scheme preserves instances ============ *)

Lemma inj_of_invol : forall (f : atom -> atom), (forall a, f (f a) = a) -> forall a b, f a = f b -> a = b.
Proof. intros f Hinv a b H. rewrite <- (Hinv a), <- (Hinv b), H. reflexivity. Qed.

Lemma sch_more_gen_ren : forall f fr s,
  (forall a, a `in` ftv_sch s -> f a = a) ->
  (forall r, r `in` frv_sch s -> fr r = r) ->
  (forall a, f (f a) = a) -> (forall r, fr (fr r) = r) ->
  sch_more_gen (ren_sch f fr s) s.
Proof.
  intros f fr s Hf Hfr Hfi Hfri.
  assert (Hfinj := inj_of_invol f Hfi).
  assert (Hfrinj := inj_of_invol fr Hfri).
  split; [| split].
  - (* inst W (ren_sch f fr s) -> inst W s *)
    intros W [st [sr [Hst [Hsr HW]]]].
    cbn [s_tq s_rq s_body ren_sch] in Hst, Hsr, HW.
    exists (fun a => if AtomSetImpl.mem a (s_tq s) then st (f a) else typ_Var a),
           (fun r => if AtomSetImpl.mem r (s_rq s) then sr (fr r) else row_Var r).
    split; [| split].
    + intros a Ha. destruct (AtomSetImpl.mem a (s_tq s)) eqn:Em; [ apply AtomSetFacts.mem_iff in Em; contradiction | reflexivity ].
    + intros r Hr. destruct (AtomSetImpl.mem r (s_rq s)) eqn:Em; [ apply AtomSetFacts.mem_iff in Em; contradiction | reflexivity ].
    + rewrite HW. unfold ren_typ. rewrite ap_typ_comp.
      apply ap_typ_ext.
      * intros a Hain. unfold tcomp. simpl.
        destruct (AtomSetImpl.mem a (s_tq s)) eqn:E.
        -- reflexivity.
        -- apply AtomSetFacts.not_mem_iff in E.
           assert (Hfa : f a = a) by (apply Hf; unfold ftv_sch; apply AtomSetImpl.diff_3; auto).
           assert (Hni : a `notin` amap f (s_tq s)).
           { rewrite amap_in. intros [b [Hb Hfb]]. apply E.
             replace a with b; [ exact Hb | apply Hfinj; rewrite Hfb; symmetry; exact Hfa ]. }
           rewrite Hfa. rewrite (Hst a Hni). reflexivity.
      * intros r Hrin. unfold rcomp. simpl.
        destruct (AtomSetImpl.mem r (s_rq s)) eqn:E.
        -- reflexivity.
        -- apply AtomSetFacts.not_mem_iff in E.
           assert (Hfrr : fr r = r) by (apply Hfr; unfold frv_sch; apply AtomSetImpl.diff_3; auto).
           assert (Hni : r `notin` amap fr (s_rq s)).
           { rewrite amap_in. intros [b [Hb Hfb]]. apply E.
             replace r with b; [ exact Hb | apply Hfrinj; rewrite Hfb; symmetry; exact Hfrr ]. }
           rewrite Hfrr. rewrite (Hsr r Hni). reflexivity.
  - (* Ftv_sch s a -> Ftv_sch (ren_sch f fr s) a *)
    intros a Ha. apply (Ftv_sch_ren f f fr Hfi Hfi).
    assert (f a = a) by (apply Hf; exact Ha). rewrite H. exact Ha.
  - intros r Hr. apply (Frv_sch_ren f fr fr Hfri Hfri).
    assert (fr r = r) by (apply Hfr; exact Hr). rewrite H. exact Hr.
Qed.

Lemma ctx_more_gen_ren : forall f fr G,
  (forall a, a `in` ftv_ctx G -> f a = a) ->
  (forall r, r `in` frv_ctx G -> fr r = r) ->
  (forall a, f (f a) = a) -> (forall r, fr (fr r) = r) ->
  ctx_more_gen (ren_ctx f fr G) G.
Proof.
  intros f fr G Hf Hfr Hfi Hfri.
  induction G as [|[x s] G IH]; simpl.
  - constructor.
  - constructor.
    + simpl. split; [reflexivity|].
      apply sch_more_gen_ren; auto.
      * intros a Ha. apply Hf. simpl. fsetdec.
      * intros r Hr. apply Hfr. simpl. fsetdec.
    + apply IH.
      * intros a Ha. apply Hf. simpl. fsetdec.
      * intros r Hr. apply Hfr. simpl. fsetdec.
Qed.
