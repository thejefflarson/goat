(* Completeness of algorithm W, stage 7.6h: [bind_row] with sorts and kinds
   (docs/design/phase7-proof-plan.md).

   [bind_row] binds a row variable [r] to a row [R] at the kind of [r].  Its
   steps, and the lemma for each:
   - an entry of [R] for a label [r] lacks has its presence variable bound to
     [Bool] ([bool_sub], [abs_vars]);
   - the sort of [r] is pushed onto the row variables of the result
     ([push_sort_r]);
   - the variable at the tail is renamed to a fresh one of the join of the two
     kinds ([bind_row_core], [bind_row_tail_complete]);
   - the sort is pushed onto the type variables of the fields ([push_sort]);
   - the renamed row must satisfy the sort and lack what [r] lacks
     ([bind_row_fin]).

   Given a substitution [Sg] that unifies [r] with [R] up to [reqD DT],
   [bind_row_sorted_complete] shows the run succeeds and that the extension
   [S2] of [Sg] to the fresh variables factors [Sg] through the result.
   Hypotheses, in the order [bind_prop_sorted_complete] has them: the atoms of
   [R] are below the supply; [R] is plain ([prf]); locally closed; and the
   field condition [frld] (the sort of an absent field, GoatCompleteBind.v).
   The occurs check is the one the stage 7.6f ruling left as a hypothesis:
   [r] is not in [R].  A variable of [R] that [Sg] makes absent and that [r]
   binds back to is excluded by it, and so is an occurrence under a present
   entry, which size refutes ([leijen_tail] for the tail, [tsz_occ] for a
   field) and is not proved here for rows with variables.

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
Require Import Goat.GoatCompleteBind.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

(* ---- conversion at the environment ---- *)

(* A row the unifier compares is read through [nfR DT], so the sorts and
   kinds a unifier gives a variable's image carry across [reqD DT]. *)
Lemma rsat_reqD : forall D k R R', reqD D R R' -> rsat D k R -> rsat D k R'.
Proof.
  intros D k R R' H Hs. apply (proj1 (rsat_nf D k R')). apply (rsat_req D k _ _ H).
  apply (proj2 (rsat_nf D k R)). exact Hs.
Qed.

Lemma rkok_reqD : forall D K R R', reqD D R R' -> rkok D K R -> rkok D K R'.
Proof.
  intros D K R R' H [Hs Hl]. split; [ exact (rsat_reqD D _ _ _ H Hs) | ].
  intros l Hk. rewrite <- (nf_rlacksD D l R'), <- (req_rlacksD _ _ H D l), nf_rlacksD.
  exact (Hl l Hk).
Qed.

(* The binding lemmas below read their hypothesis and state the factoring of a row
   variable's image at one of two conversions: [reqD] at the environment
   ([b = true]), or plain [req] ([b = false]), which a caller whose rows carry no
   absent entry to normalize needs. *)
Definition reqX (b : bool) (D : denv) (R R' : row) : Prop :=
  if b then reqD D R R' else req R R'.

Lemma reqX_refl : forall b D R, reqX b D R R.
Proof. intros [] D R; [ apply reqD_refl | apply req_refl ]. Qed.

Lemma rsat_reqX : forall b D k R R', reqX b D R R' -> rsat D k R -> rsat D k R'.
Proof.
  intros [] D k R R' H Hs; [ exact (rsat_reqD D k R R' H Hs) | exact (rsat_req D k R R' H Hs) ].
Qed.

Lemma rkok_reqX : forall b D K R R', reqX b D R R' -> rkok D K R -> rkok D K R'.
Proof.
  intros [] D K R R' H Hk; [ exact (rkok_reqD D K R R' H Hk) | ].
  exact (rkok_req D K R R' H Hk).
Qed.

(* ---- renamings by variables ---- *)

Definition vren (s : sub) : Prop :=
  (forall x, exists y, sT s x = typ_Var y) /\ (forall q, exists q', sR s q = row_Var q').

Definition rren (s : sub) : Prop :=
  (forall x, sT s x = typ_Var x) /\ (forall q, exists q', sR s q = row_Var q').

Lemma rren_vren : forall s, rren s -> vren s.
Proof. intros s [H1 H2]. split; [ intros x; exists x; apply H1 | exact H2 ]. Qed.

Lemma ftv_rren : forall s, rren s ->
  (forall T, ftv_typ (apT s T) = ftv_typ T) /\ (forall R, ftv_row (apR s R) = ftv_row R).
Proof.
  intros s [Hs Hr]. unfold apT, apR. apply typ_row_mutind; simpl; try (intros; reflexivity).
  - intros A IHA B IHB. rewrite IHA, IHB. reflexivity.
  - intros R IH. exact IH.
  - intros a. rewrite (Hs a). reflexivity.
  - intros B IH. exact IH.
  - intros w B IH. exact IH.
  - intros r. destruct (Hr r) as [q E]. rewrite E. reflexivity.
  - intros l T IHT R IHR. rewrite IHT, IHR. reflexivity.
  - intros l P IHP T IHT R IHR. rewrite IHP, IHT, IHR. reflexivity.
Qed.

Lemma frv_vren_in : forall s, vren s -> forall R p,
  p `in` frv_row (apR s R) -> exists q, q `in` frv_row R /\ sR s q = row_Var p.
Proof.
  intros s [Hs Hr] R p H. unfold apR in H.
  destruct (proj2 frv_ap_mut R _ _ p H) as [[b [_ Hb]]|[q [Hq Hp]]].
  - destruct (Hs b) as [y E]. rewrite E in Hb. simpl in Hb. exfalso. fsetdec.
  - destruct (Hr q) as [q' E]. rewrite E in Hp. simpl in Hp.
    apply AtomSetFacts.singleton_iff in Hp. subst p. exists q. split; [ exact Hq | exact E ].
Qed.

Lemma is_abs_vren : forall s, (forall x, exists y, sT s x = typ_Var y) ->
  forall P, is_abs (ap_typ (sT s) (sR s) P) = is_abs P.
Proof.
  intros s Hs P. destruct P; try reflexivity.
  simpl. destruct (Hs a) as [y ->]. reflexivity.
Qed.

Lemma lacks_ok_vren : forall K s, vren s -> forall R, lacks_ok K (apR s R) = lacks_ok K R.
Proof.
  intros K s [Hs Hr] R. induction R; unfold apR in *; simpl in *.
  - reflexivity.
  - destruct (Hr r) as [q E]. unfold apR. simpl. rewrite E. reflexivity.
  - rewrite IHR. reflexivity.
  - rewrite IHR, (is_abs_vren s Hs). reflexivity.
Qed.

Lemma pf_ap : forall u,
  (forall x, pf (sT u x)) -> (forall q, exists q', sR u q = row_Var q') ->
  (forall T, pf T -> pf (apT u T)) /\ (forall R, prf R -> prf (apR u R)).
Proof.
  intros u Hs Hr. unfold apT, apR. apply typ_row_mutind; simpl;
    try (intros; exact I); try (intros; contradiction).
  - intros A IHA B IHB [HA HB]. split; auto.
  - intros R IH. exact IH.
  - intros a _. apply Hs.
  - intros v B IH [HB Hn]. exact (conj (IH HB) (spn_ap _ _ B v 0 Hn)).
  - intros r _. destruct (Hr r) as [q E]. rewrite E. exact I.
  - intros l T IHT R IHR [HT HR]. split; auto.
  - intros l P IHP T IHT R IHR [HP [HT HR]]. split; [ | split ]; auto.
Qed.

Lemma lcb_ap_closed : forall u,
  (forall x k, lcb k (sT u x) = true) -> (forall q, exists q', sR u q = row_Var q') ->
  (forall T k, lcb k T = true -> lcb k (apT u T) = true) /\
  (forall R k, lcrb k R = true -> lcrb k (apR u R) = true).
Proof.
  intros u Hs Hr. unfold apT, apR. apply typ_row_mutind; simpl; try (intros; reflexivity);
    try (intros; assumption).
  - intros A IHA B IHB k H. apply Bool.andb_true_iff in H. destruct H as [H1 H2].
    rewrite (IHA k H1), (IHB k H2). reflexivity.
  - intros R IH k H. exact (IH k H).
  - intros a k _. apply Hs.
  - intros B IH k H. exact (IH (Datatypes.S k) H).
  - intros w B IH k H. exact (IH k H).
  - intros r k _. destruct (Hr r) as [q E]. rewrite E. reflexivity.
  - intros l T IHT R IHR k H. apply Bool.andb_true_iff in H. destruct H as [H1 H2].
    rewrite (IHT k H1), (IHR k H2). reflexivity.
  - intros l P IHP T IHT R IHR k H. apply Bool.andb_true_iff in H. destruct H as [H H3].
    apply Bool.andb_true_iff in H. destruct H as [H1 H2].
    rewrite (IHP k H1), (IHT k H2), (IHR k H3). reflexivity.
Qed.

(* ---- agreement: [S] is [S'] after [u] ---- *)

Lemma ap_agree : forall S S' u,
  (forall T, (forall x, x `in` ftv_typ T -> sT S x = apT S' (sT u x)) ->
     (forall q, q `in` frv_typ T -> sR S q = apR S' (sR u q)) -> apT S' (apT u T) = apT S T) /\
  (forall R, (forall x, x `in` ftv_row R -> sT S x = apT S' (sT u x)) ->
     (forall q, q `in` frv_row R -> sR S q = apR S' (sR u q)) -> apR S' (apR u R) = apR S R).
Proof.
  intros S S' u. split.
  - intros T Hx Hq. rewrite apT_comp. unfold apT. apply ap_typ_ext.
    + intros a Ha. exact (eq_sym (Hx a Ha)).
    + intros q Hq'. exact (eq_sym (Hq q Hq')).
  - intros R Hx Hq. rewrite apR_comp. unfold apR. apply (proj2 ap_ext_mut).
    + intros a Ha. exact (eq_sym (Hx a Ha)).
    + intros q Hq'. exact (eq_sym (Hq q Hq')).
Qed.

(* The field condition survives a substitution [s] that [S'] after [s]
   agrees with [S] on. *)
Lemma fld_pull : forall D1 S S' k s,
  (forall x, fld D1 S' k (sT s x)) -> (forall q, frld D1 S' k (sR s q)) ->
  (forall T, pf T -> fld D1 S k T ->
     (forall x, x `in` ftv_typ T -> sT S x = apT S' (sT s x)) ->
     (forall q, q `in` frv_typ T -> sR S q = apR S' (sR s q)) -> fld D1 S' k (apT s T)) /\
  (forall R, prf R -> frld D1 S k R ->
     (forall x, x `in` ftv_row R -> sT S x = apT S' (sT s x)) ->
     (forall q, q `in` frv_row R -> sR S q = apR S' (sR s q)) -> frld D1 S' k (apR s R)).
Proof.
  intros D1 S S' k s Hs Hr. unfold apT, apR. apply typ_row_mutind; simpl;
    try (intros; exact I).
  - intros A IHA B IHB Hpf Hf Hx Hq. destruct Hpf as [HpA HpB]. destruct Hf as [HfA HfB]. split.
    + apply IHA; [ exact HpA | exact HfA | | ];
        [ intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ].
    + apply IHB; [ exact HpB | exact HfB | | ];
        [ intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ].
  - intros R IH Hpf Hf Hx Hq. exact (IH Hpf Hf Hx Hq).
  - intros a _ _ _ _. apply Hs.
  - intros v B IH Hpf Hf Hx Hq. exact (IH (proj1 Hpf) Hf Hx Hq).
  - intros r _ _ _ _. apply Hr.
  - intros l T IHT R IHR Hpf Hf Hx Hq. destruct Hpf as [HpT HpR]. destruct Hf as [HfT HfR]. split.
    + apply IHT; [ exact HpT | exact HfT | | ];
        [ intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ].
    + apply IHR; [ exact HpR | exact HfR | | ];
        [ intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ].
  - intros l P IHP T IHT R IHR Hpf Hf Hx Hq.
    destruct Hpf as [HpP [HpT HpR]]. destruct Hf as [HeP [HsP [HfP [HfT HfR]]]].
    assert (EP : apT S' (apT s P) = apT S P).
    { apply (proj1 (ap_agree S S' s)); [ intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]. }
    assert (ET : apT S' (apT s T) = apT S T).
    { apply (proj1 (ap_agree S S' s)); [ intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ]. }
    change (ap_typ (sT s) (sR s) P) with (apT s P). change (ap_typ (sT s) (sR s) T) with (apT s T).
    rewrite EP, ET.
    refine (conj HeP (conj HsP (conj _ (conj _ _)))).
    + apply IHP; [ exact HpP | exact HfP | | ];
        [ intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ].
    + apply IHT; [ exact HpT | exact HfT | | ];
        [ intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ].
    + apply IHR; [ exact HpR | exact HfR | | ];
        [ intros x Hx'; apply Hx; fsetdec | intros q Hq'; apply Hq; fsetdec ].
Qed.

(* ---- push_sort leaves the row kinds alone ---- *)

Lemma push_sort_drk : forall l D k n sp D' n',
  push_sort D k l n = (sp, D', n') -> drk D' = drk D.
Proof.
  induction l as [|b l IH]; intros D k n sp D' n' H; cbn [push_sort] in H.
  - inversion H; subst. reflexivity.
  - destruct (finer_b (D b) k).
    + exact (IH _ _ _ _ _ _ H).
    + destruct (finer_b k (D b)); [ | exact (IH _ _ _ _ _ _ H) ].
      destruct (push_sort (upd D (ea n) k) k l (Datatypes.S n)) as [[s1 D1] n1] eqn:E.
      inversion H; subst. exact (IH _ _ _ _ _ _ E).
Qed.

(* ---- where the renamed row variables go ---- *)

Lemma push_sort_r_new : forall l D k n sr D' n',
  push_sort_r D k l n = (sr, D', n') -> (forall c, In c l -> old n c) ->
  forall q q', old n q -> sR sr q = row_Var q' ->
    q' = q \/ exists m, n <= m /\ m < n' /\ q' = ea m.
Proof.
  induction l as [|b l IH]; intros D k n sr D' n' H Hold q q' Hq E; cbn [push_sort_r] in H.
  - inversion H; subst. cbn [sR sid idr] in E. injection E as <-. left. reflexivity.
  - destruct (finer_b (rk_sort (drk D b)) k).
    + exact (IH _ _ _ _ _ _ H (fun c Hc => Hold c (or_intror Hc)) q q' Hq E).
    + destruct (finer_b k (rk_sort (drk D b))) eqn:Ef2;
        [ | exact (IH _ _ _ _ _ _ H (fun c Hc => Hold c (or_intror Hc)) q q' Hq E) ].
      destruct (push_sort_r (rupd D (ea n) (RK k (rk_lacks (drk D b)))) k l (Datatypes.S n))
        as [[s1 D1] n1] eqn:E1.
      inversion H; subst.
      assert (Hold' : forall c, In c l -> old (Datatypes.S n) c).
      { intros c Hc m Hm. apply (Hold c (or_intror Hc)). lia. }
      destruct (push_sort_r_facts _ _ _ _ _ _ _ E1 Hold') as (_ & Hn1 & _ & H4 & _ & _ & _).
      change (apR s1 (sR (sbR b (row_Var (ea n))) q) = row_Var q') in E.
      cbn [sR sbR] in E. destruct (Atom.eq_dec q b) as [->|Hne].
      * assert (Hnl : ~ In (ea n) l).
        { intros Hin. exact (Hold (ea n) (or_intror Hin) n (le_n n) eq_refl). }
        cbn [apR ap_row sR] in E. fold (sR s1 (ea n)) in E. rewrite (H4 _ Hnl) in E.
        injection E as <-. right. exists n. split; [ lia | split; [ lia | reflexivity ] ].
      * change (sR s1 q = row_Var q') in E.
        assert (Hq' : old (Datatypes.S n) q) by (intros m Hm; apply Hq; lia).
        destruct (IH _ _ _ _ _ _ E1 Hold' q q' Hq' E) as [->|[m [Hm1 [Hm2 ->]]]].
        -- left. reflexivity.
        -- right. exists m. split; [ lia | split; [ exact Hm2 | reflexivity ] ].
Qed.

(* ---- the tail of a row, and what a kind says of it ---- *)

Lemma row_tail_in : forall R q, row_tail R = Some q -> q `in` frv_row R.
Proof.
  induction R; simpl; intros q H; try discriminate.
  - inversion H; subst. fsetdec.
  - apply IHR in H. fsetdec.
  - apply IHR in H. fsetdec.
Qed.

Lemma rkok_ext_tail : forall D K l T R, rkok D K (row_Ext l T R) -> rkok D K R.
Proof.
  intros D K l T R [Hs Hl]. split; [ exact (proj2 Hs) | ].
  intros l' Hl'. specialize (Hl l' Hl'). cbn [rlacksD] in Hl.
  exact (proj2 (andb_prop _ _ Hl)).
Qed.

Lemma rkok_tail : forall D K S R q,
  row_tail R = Some q -> rkok D K (apR S R) -> rkok D K (sR S q).
Proof.
  intros D K S R. induction R; simpl; intros q H Hk; try discriminate.
  - inversion H; subst. exact Hk.
  - rewrite apR_Ext in Hk. exact (IHR q H (rkok_ext_tail _ _ _ _ _ Hk)).
  - rewrite apR_Maybe in Hk. exact (IHR q H (rkok_maybe_tail _ _ _ _ _ _ Hk)).
Qed.

(* ---- the entries for a label the kind lacks ---- *)

Definition LK (D : denv) (K : rkind) (R : row) : Prop :=
  forall l, rk_lacks K l = true -> rlacksD D l R = true.

Lemma LK_ext : forall D K l T R, LK D K (row_Ext l T R) -> LK D K R.
Proof.
  intros D K l T R H l' Hl'. specialize (H l' Hl'). cbn [rlacksD] in H.
  exact (proj2 (andb_prop _ _ H)).
Qed.

Lemma LK_maybe : forall D K l P T R, LK D K (row_Maybe l P T R) -> LK D K R.
Proof.
  intros D K l P T R H l' Hl'. specialize (H l' Hl'). cbn [rlacksD] in H.
  destruct (Nat.eqb l' l); [ exact (proj2 (andb_prop _ _ H)) | exact H ].
Qed.

Lemma LK_rkok : forall D K R, rkok D K R -> LK D K R.
Proof. intros D K R [_ H]. exact H. Qed.

Lemma abs_vars_bool : forall D1 K S R, LK D1 K (apR S R) ->
  forall p, In p (abs_vars K R) -> sT S p = typ_Bool.
Proof.
  intros D1 K S R. induction R as [|r|l T R IHR|l P T R IHR]; simpl; intros HL p Hp;
    try contradiction.
  - rewrite apR_Ext in HL. exact (IHR (LK_ext _ _ _ _ _ HL) p Hp).
  - rewrite apR_Maybe in HL. destruct P as [ | | | | | | | a | | | ];
      try exact (IHR (LK_maybe _ _ _ _ _ _ HL) p Hp).
    destruct (rk_lacks K l) eqn:Ek.
    + destruct Hp as [<-|Hp].
      * pose proof (HL l Ek) as H. cbn [rlacksD] in H. rewrite Nat.eqb_refl in H.
        apply andb_prop in H. destruct H as [H _]. apply is_abs_Bool in H. exact H.
      * exact (IHR (LK_maybe _ _ _ _ _ _ HL) p Hp).
    + exact (IHR (LK_maybe _ _ _ _ _ _ HL) p Hp).
Qed.

(* ---- the Bool substitution ---- *)

Lemma bool_sub_in : forall ps x, In x ps -> sT (bool_sub ps) x = typ_Bool.
Proof.
  induction ps as [|p ps IH]; intros x Hx; [ destruct Hx | ].
  change (ap_typ (sT (bool_sub ps)) (sR (bool_sub ps)) (sT (sbT p typ_Bool) x) = typ_Bool).
  cbn [sT sbT]. destruct (Atom.eq_dec x p) as [->|Hne]; [ reflexivity | ].
  destruct Hx as [E|Hx]; [ exfalso; apply Hne; symmetry; exact E | exact (IH x Hx) ].
Qed.

Lemma bool_sub_out : forall ps x, ~ In x ps -> sT (bool_sub ps) x = typ_Var x.
Proof.
  induction ps as [|p ps IH]; intros x Hx; [ reflexivity | ].
  change (ap_typ (sT (bool_sub ps)) (sR (bool_sub ps)) (sT (sbT p typ_Bool) x) = typ_Var x).
  cbn [sT sbT]. destruct (Atom.eq_dec x p) as [->|Hne].
  - exfalso. apply Hx. left. reflexivity.
  - exact (IH x (fun H => Hx (or_intror H))).
Qed.

Lemma bool_sub_R : forall ps q, sR (bool_sub ps) q = row_Var q.
Proof.
  induction ps as [|p ps IH]; intros q; [ reflexivity | ].
  change (ap_row (sT (bool_sub ps)) (sR (bool_sub ps)) (sR (sbT p typ_Bool) q) = row_Var q).
  cbn [sR sbT]. exact (IH q).
Qed.

Lemma bool_sub_T_cases : forall ps x, sT (bool_sub ps) x = typ_Var x \/ sT (bool_sub ps) x = typ_Bool.
Proof.
  intros ps x. destruct (in_dec Atom.eq_dec x ps) as [H|H];
    [ right; exact (bool_sub_in ps x H) | left; exact (bool_sub_out ps x H) ].
Qed.

Lemma bool_sub_agree : forall Sg ps, (forall p, In p ps -> sT Sg p = typ_Bool) ->
  (forall x, sT Sg x = apT Sg (sT (bool_sub ps) x)) /\ (forall q, sR Sg q = apR Sg (sR (bool_sub ps) q)).
Proof.
  intros Sg ps H. split.
  - intros x. destruct (in_dec Atom.eq_dec x ps) as [Hin|Hin].
    + rewrite (bool_sub_in ps x Hin). exact (H x Hin).
    + rewrite (bool_sub_out ps x Hin). reflexivity.
  - intros q. rewrite bool_sub_R. reflexivity.
Qed.

Lemma is_abs_nonvar : forall S P, (forall v, P <> typ_Var v) -> is_abs (apT S P) = is_abs P.
Proof. intros S P H. destruct P; try reflexivity. exfalso. exact (H a eq_refl). Qed.

(* The entries for a label the kind lacks are absent once the presence
   variables [ps] are [Bool]. *)
Lemma lacks_ok_bs : forall D1 K Sg R ps, LK D1 K (apR Sg R) ->
  (forall p, In p (abs_vars K R) -> In p ps) ->
  lacks_ok K (apR (bool_sub ps) R) = true.
Proof.
  intros D1 K Sg R. induction R as [|r|l T R IHR|l P T R IHR]; intros ps HL Hin.
  - reflexivity.
  - change (lacks_ok K (sR (bool_sub ps) r) = true). rewrite bool_sub_R. reflexivity.
  - rewrite apR_Ext. cbn [lacks_ok]. destruct (rk_lacks K l) eqn:Ek.
    + exfalso. pose proof (HL l Ek) as H. rewrite apR_Ext in H. cbn [rlacksD] in H.
      rewrite Nat.eqb_refl in H. discriminate H.
    + cbn [negb]. cbn iota. rewrite apR_Ext in HL.
      exact (IHR ps (LK_ext _ _ _ _ _ HL) Hin).
  - rewrite apR_Maybe. cbn [lacks_ok].
    rewrite apR_Maybe in HL.
    assert (Hin' : forall p, In p (abs_vars K R) -> In p ps).
    { intros p0 Hp0. apply Hin. simpl. destruct P; try exact Hp0.
      destruct (rk_lacks K l); [ right; exact Hp0 | exact Hp0 ]. }
    rewrite (IHR ps (LK_maybe _ _ _ _ _ _ HL) Hin'). rewrite Bool.andb_true_r.
    destruct (rk_lacks K l) eqn:Ek; [ | reflexivity ].
    cbn [negb orb]. pose proof (HL l Ek) as H. cbn [rlacksD] in H. rewrite Nat.eqb_refl in H.
    apply andb_prop in H. destruct H as [H _].
    destruct P as [ | | | | | | | a | | | ].
    all: try (rewrite (is_abs_nonvar (bool_sub ps)) by discriminate;
              rewrite (is_abs_nonvar Sg) in H by discriminate; exact H).
    simpl in Hin. rewrite Ek in Hin.
    change (is_abs (sT (bool_sub ps) a) = true).
    rewrite (bool_sub_in ps a (Hin a (or_introl eq_refl))). reflexivity.
Qed.

Lemma bs_ftv_in : forall u, (forall x, sT u x = typ_Var x \/ sT u x = typ_Bool) ->
  (forall q, sR u q = row_Var q) -> forall R a,
  a `in` ftv_row (apR u R) -> a `in` ftv_row R.
Proof.
  intros u Hu1 Hu2 R a H. unfold apR in H.
  destruct (proj2 ftv_ap_mut R _ _ a H) as [[b [Hb Ha]]|[q [Hq Ha]]].
  - destruct (Hu1 b) as [E|E]; rewrite E in Ha; simpl in Ha;
      [ apply AtomSetFacts.singleton_iff in Ha; subst; exact Hb | exfalso; fsetdec ].
  - rewrite Hu2 in Ha. simpl in Ha. exfalso. fsetdec.
Qed.

Lemma bs_frv_in : forall u, (forall x, sT u x = typ_Var x \/ sT u x = typ_Bool) ->
  (forall q, sR u q = row_Var q) -> forall R p,
  p `in` frv_row (apR u R) -> p `in` frv_row R.
Proof.
  intros u Hu1 Hu2 R p H. unfold apR in H.
  destruct (proj2 frv_ap_mut R _ _ p H) as [[b [Hb Ha]]|[q [Hq Ha]]].
  - destruct (Hu1 b) as [E|E]; rewrite E in Ha; simpl in Ha; exfalso; fsetdec.
  - rewrite Hu2 in Ha. simpl in Ha. apply AtomSetFacts.singleton_iff in Ha. subst. exact Hq.
Qed.

Section RowX.

Variable bx : bool.

(* ---- the second half of [bind_row] ---- *)

Lemma bind_row_fin_complete : forall (D0 DT : denv) Sg0 r R Rx sq n0,
  apR sq R = Rx ->
  DOk D0 n0 -> KR D0 DT Sg0 -> rren sq -> old n0 r -> sR sq r = row_Var r ->
  (forall q0, sR sq q0 = row_Var r -> q0 = r) ->
  (forall q0, old n0 q0 -> sR Sg0 q0 = apR Sg0 (sR sq q0)) ->
  (forall x, x `in` ftv_row Rx -> old n0 x) ->
  prf Rx -> lcrb 0 Rx = true -> r `notin` frv_row Rx ->
  (forall q, q `in` frv_row Rx -> finer (rk_sort (drk D0 q)) (rk_sort (drk D0 r))) ->
  frld DT Sg0 (rk_sort (drk D0 r)) Rx -> lacks_ok (drk D0 r) Rx = true ->
  reqX bx DT (sR Sg0 r) (apR Sg0 Rx) ->
  exists s D' n' S2, bind_row_fin r R sq D0 n0 = Some (s, D', n') /\ KR D' DT S2 /\
    n0 <= n' /\ DOk D' n' /\
    (forall x, old n0 x -> teq (sT Sg0 x) (apT S2 (sT s x))) /\
    (forall q, old n0 q -> reqX bx DT (sR Sg0 q) (apR S2 (sR s q))).
Proof.
  intros D0 DT Sg0 r R Rx sq n0 HRx Hd HK Hsq Hr Hsqr Hsqinv Hsqag Hold Hpf Hlc Hnr Hrf Hfld Hlo Hreq.
  assert (Hrsat : rsat DT (rk_sort (drk D0 r)) (apR Sg0 Rx)).
  { apply (rsat_reqX bx DT _ (sR Sg0 r) _ Hreq). exact (proj1 (proj2 HK r)). }
  destruct (sat_reach_mut DT Sg0 (rk_sort (drk D0 r))) as [_ Hrr].
  destruct (Hrr Rx Hpf Hfld Hrsat) as [Hreach_t _].
  unfold bind_row_fin. cbn zeta. rewrite HRx.
  assert (Holdl : forall b, In b (AtomSetImpl.elements (ftv_row Rx)) -> old n0 b)
    by (intros b Hb; apply Hold; apply in_elts; exact Hb).
  destruct (push_sort D0 (rk_sort (drk D0 r)) (AtomSetImpl.elements (ftv_row Rx)) n0)
    as [[sp D1] n1] eqn:Ep.
  destruct (push_sort_facts _ _ _ _ _ _ _ Ep Holdl) as (P1 & P2 & P3 & P4 & P5 & P6).
  pose proof (push_sort_dok _ _ _ _ _ _ _ Ep Hd) as Hd1.
  pose proof (push_sort_drk _ _ _ _ _ _ _ Ep) as Hdrk.
  destruct (push_sort_complete _ _ _ _ Sg0 DT Hd HK
              (fun b Hb => Hreach_t b (proj1 (in_elts _ _) Hb)) Holdl sp D1 n1 Ep)
    as (S2 & K2 & R2 & F2 & _).
  assert (Hvp : forall x, exists y, sT sp x = typ_Var y)
    by (intros x; destruct (P4 x) as (y & E & _); exists y; exact E).
  assert (Hsrx : forall q, exists q', sR sp q = row_Var q') by (intros q; exists q; apply P1).
  assert (Hvsp : vren sp) by (split; [ exact Hvp | exact Hsrx ]).
  assert (Hocc : occR r (apR sp Rx) = false).
  { unfold occR. apply Bool.orb_false_iff. split.
    - apply AtomSetFacts.not_mem_iff. intros Hin.
      destruct (frv_vren_in sp Hvsp Rx r Hin) as (q & Hq & E). rewrite P1 in E.
      injection E as ->. exact (Hnr Hq).
    - unfold apR. rewrite (proj2 (lcb_ap_var (sT sp) (sR sp) Hvp Hsrx) Rx 0). rewrite Hlc. reflexivity. }
  rewrite Hocc. cbn iota. rewrite Hdrk.
  assert (Hsat : rsat D1 (rk_sort (drk D0 r)) (apR sp Rx)).
  { apply (proj2 (sat_ren_mut D1 DT Sg0 sp (rk_sort (drk D0 r))) Rx Hpf Hfld).
    - intros x Hx. destruct (P6 x (proj2 (in_elts _ _) Hx)) as (y & Ey & Hf).
      exists y. split; [ exact Ey | apply finer_b_iff; exact Hf ].
    - intros q Hq. exists q. split; [ apply P1 | ]. rewrite Hdrk. exact (Hrf q Hq).
    - exact Hrsat. }
  rewrite (proj2 (rsat_b_iff _ _ _) Hsat). cbn iota.
  assert (Hlo' : lacks_ok (drk D0 r) (apR sp Rx) = true).
  { rewrite (lacks_ok_vren _ sp Hvsp). exact Hlo. }
  rewrite Hlo'. cbn iota.
  assert (Hagree : apR S2 (apR sp Rx) = apR Sg0 Rx).
  { apply (proj2 (ap_agree Sg0 S2 sp)).
    - intros x Hx. exact (F2 x (Hold x Hx)).
    - intros q Hq. rewrite P1. cbn [apR ap_row]. fold (sR S2 q). rewrite R2. reflexivity. }
  eexists. exists D1, n1, S2. split; [ reflexivity | ].
  refine (conj K2 (conj P2 (conj Hd1 (conj _ _)))).
  - intros x Hx. destruct (P4 x) as (y & Ey & _).
    change (teq (sT Sg0 x) (apT S2 (apT (sbR r (apR sp Rx)) (apT sp (sT sq x))))).
    rewrite (proj1 Hsq x). change (apT sp (typ_Var x)) with (sT sp x). rewrite Ey.
    change (apT (sbR r (apR sp Rx)) (typ_Var y)) with (typ_Var y).
    rewrite (F2 x Hx), Ey. apply teq_refl.
  - intros q Hq.
    change (reqX bx DT (sR Sg0 q) (apR S2 (apR (sbR r (apR sp Rx)) (apR sp (sR sq q))))).
    destruct (Atom.eq_dec q r) as [->|Hne].
    + rewrite Hsqr. change (apR sp (row_Var r)) with (sR sp r). rewrite P1.
      change (apR (sbR r (apR sp Rx)) (row_Var r)) with (sR (sbR r (apR sp Rx)) r).
      cbn [sR sbR]. rewrite dec_same. rewrite Hagree. exact Hreq.
    + destruct (proj2 Hsq q) as [z Ez]. rewrite Ez.
      assert (Hzr : z <> r) by (intros ->; exact (Hne (Hsqinv q Ez))).
      change (apR sp (row_Var z)) with (sR sp z). rewrite P1.
      change (apR (sbR r (apR sp Rx)) (row_Var z)) with (sR (sbR r (apR sp Rx)) z).
      cbn [sR sbR]. rewrite (dec_diff _ _ _ _ _ Hzr).
      change (apR S2 (row_Var z)) with (sR S2 z). rewrite R2.
      rewrite (Hsqag q Hq), Ez. apply reqX_refl.
Qed.

(* ---- the tail renaming ---- *)

(* [bind_row_tail_complete], with the extension spelled out. *)
Lemma bind_row_tail_ext : forall D n r q DT Sg,
  DOk D n -> KR D DT Sg -> rkok DT (drk D r) (sR Sg q) ->
  exists S2, KR (rupd D (ea n) (rk_join (drk D r) (drk D q))) DT S2 /\
    sT S2 = sT Sg /\ sR S2 (ea n) = sR Sg q /\ (forall q', old n q' -> sR S2 q' = sR Sg q').
Proof.
  intros D n r q DT Sg Hd HK Hr. exists (srupd Sg (ea n) (sR Sg q)).
  refine (conj _ (conj eq_refl (conj _ _))).
  - split.
    + intros a. cbn [sT srupd dsort rupd]. exact (proj1 HK a).
    + intros r'. cbn [sR srupd drk rupd]. destruct (Atom.eq_dec r' (ea n)) as [->|Hne].
      * exact (rk_join_ok _ _ _ _ Hr (proj2 HK q)).
      * exact (proj2 HK r').
  - cbn [sR srupd]. rewrite dec_same. reflexivity.
  - intros q' Hq'. cbn [sR srupd]. rewrite (dec_diff _ _ _ _ _ (fun E => Hq' n (le_n n) E)). reflexivity.
Qed.

Lemma rren_sid : rren sid.
Proof. split; [ intros x; reflexivity | intros q; exists q; reflexivity ]. Qed.

Lemma rren_sbR : forall q z, rren (sbR q (row_Var z)).
Proof.
  intros q z. split; [ intros x; reflexivity | ].
  intros q0. cbn [sR sbR]. destruct (Atom.eq_dec q0 q); eexists; reflexivity.
Qed.

(* ---- [bind_row_core] ---- *)

Lemma bind_row_core_complete : forall (D DT : denv) Sg r R n,
  DOk D n -> KR D DT Sg -> old n r ->
  (forall x, x `in` ftv_row R -> old n x) -> (forall q, q `in` frv_row R -> old n q) ->
  prf R -> lcrb 0 R = true -> r `notin` frv_row R ->
  (forall q, q `in` frv_row R -> finer (rk_sort (drk D q)) (rk_sort (drk D r))) ->
  frld DT Sg (rk_sort (drk D r)) R -> lacks_ok (drk D r) R = true ->
  reqX bx DT (sR Sg r) (apR Sg R) ->
  exists s D' n' S2, bind_row_core D r R n = Some (s, D', n') /\ KR D' DT S2 /\
    n <= n' /\ DOk D' n' /\
    (forall x, old n x -> teq (sT Sg x) (apT S2 (sT s x))) /\
    (forall q, old n q -> reqX bx DT (sR Sg q) (apR S2 (sR s q))).
Proof.
  intros D DT Sg r R n Hd HK Hr Hot Hoq Hpf Hlc Hnr Hrf Hfld Hlo Hreq.
  assert (Hocc : occR r R = false).
  { unfold occR. apply Bool.orb_false_iff. split.
    - apply AtomSetFacts.not_mem_iff. exact Hnr.
    - rewrite Hlc. reflexivity. }
  unfold bind_row_core. rewrite Hocc. cbn iota.
  destruct (row_tail R) as [q|] eqn:Et.
  - assert (Hqin : q `in` frv_row R) by exact (row_tail_in R q Et).
    assert (Hrq : r <> q) by (intros ->; exact (Hnr Hqin)).
    assert (Hrkq : rkok DT (drk D r) (sR Sg q)).
    { exact (rkok_tail DT _ Sg R q Et (rkok_reqX bx DT _ _ _ Hreq (proj2 HK r))). }
    destruct (bind_row_tail_ext D n r q DT Sg Hd HK Hrkq) as (S2b & KRb & Tb & Rbn & Rbo).
    assert (Hrn : r <> ea n) by (intros E; exact (Hr n (le_n n) E)).
    assert (Hqn : q <> ea n) by (intros E; exact (Hoq q Hqin n (le_n n) E)).
    set (sq := sbR q (row_Var (ea n))).
    set (D0 := rupd D (ea n) (rk_join (drk D r) (drk D q))).
    assert (HD0r : drk D0 r = drk D r) by exact (rupd_other D (ea n) _ r Hrn).
    assert (Hagt : forall x, sT Sg x = apT S2b (sT sq x)).
    { intros x. change (sT Sg x = apT S2b (typ_Var x)). change (apT S2b (typ_Var x)) with (sT S2b x).
      rewrite Tb. reflexivity. }
    assert (Hagr : forall q0, old n q0 -> sR Sg q0 = apR S2b (sR sq q0)).
    { intros q0 Hq0. subst sq. cbn [sR sbR]. destruct (Atom.eq_dec q0 q) as [->|Hne].
      - change (apR S2b (row_Var (ea n))) with (sR S2b (ea n)). rewrite Rbn. reflexivity.
      - change (apR S2b (row_Var q0)) with (sR S2b q0). rewrite (Rbo q0 Hq0). reflexivity. }
    assert (Happ : apR S2b (apR sq R) = apR Sg R).
    { apply (proj2 (ap_agree Sg S2b sq)).
      - intros x _. apply Hagt.
      - intros q0 Hq0. apply Hagr. apply Hoq. exact Hq0. }
    assert (Hvs : rren sq) by exact (rren_sbR q (ea n)).
    destruct (bind_row_fin_complete D0 DT S2b r R (apR sq R) sq (Datatypes.S n) eq_refl
                (DOk_rupd D n _ Hd) KRb Hvs ltac:(intros m Hm; apply Hr; lia)
                ltac:(subst sq; cbn [sR sbR]; rewrite (dec_diff _ _ _ _ _ Hrq); reflexivity)
                ltac:(intros q0 E; subst sq; cbn [sR sbR] in E;
                      destruct (Atom.eq_dec q0 q) as [->|Hne];
                      [ injection E as E; exfalso; exact (Hrn (eq_sym E))
                      | injection E as ->; reflexivity ])
                ltac:(intros q0 Hq0; subst sq; cbn [sR sbR];
                      destruct (Atom.eq_dec q0 q) as [->|Hne];
                      [ change (apR S2b (row_Var (ea n))) with (sR S2b (ea n)); rewrite Rbn;
                        exact (Rbo q (fun m Hm => Hoq q Hqin m Hm))
                      | change (apR S2b (row_Var q0)) with (sR S2b q0); reflexivity ])
                ltac:(intros x Hx; rewrite (proj2 (ftv_rren sq Hvs)) in Hx;
                      intros m Hm; apply (Hot x Hx m); lia)
                ltac:(apply (proj2 (pf_ap sq (fun x => I) (proj2 Hvs))); exact Hpf)
                ltac:(unfold apR; rewrite (proj2 (lcb_ap_var (sT sq) (sR sq)
                        (fun x => ex_intro _ x (proj1 Hvs x)) (proj2 Hvs)) R 0); exact Hlc)
                ltac:(intros Hin; destruct (frv_vren_in sq (rren_vren sq Hvs) R r Hin) as (q0 & Hq0 & E);
                      assert (q0 = r) by (subst sq; cbn [sR sbR] in E;
                        destruct (Atom.eq_dec q0 q) as [->|Hne];
                        [ injection E as E; exfalso; exact (Hrn (eq_sym E)) | injection E as ->; reflexivity ]);
                      subst q0; exact (Hnr Hq0))
                ltac:(intros z Hz; destruct (frv_vren_in sq (rren_vren sq Hvs) R z Hz) as (q0 & Hq0 & E);
                      rewrite HD0r; subst sq; cbn [sR sbR] in E;
                      destruct (Atom.eq_dec q0 q) as [->|Hne];
                      [ injection E as <-; unfold D0; rewrite rupd_same; cbn [rk_join rk_sort];
                        destruct (finer_b (rk_sort (drk D r)) (rk_sort (drk D q))) eqn:Ef;
                        [ apply finer_refl | exact (Hrf q Hqin) ]
                      | injection E as <-; unfold D0; rewrite (rupd_other D (ea n) _ q0
                          (fun E2 => Hoq q0 Hq0 n (le_n n) E2)); exact (Hrf q0 Hq0) ])
                ltac:(rewrite HD0r; refine (proj2 (fld_pull DT Sg S2b _ sq (fun x => I) _) R Hpf Hfld _ _);
                      [ intros q0; subst sq; cbn [sR sbR]; destruct (Atom.eq_dec q0 q); exact I
                      | intros x _; apply Hagt
                      | intros q0 Hq0; apply Hagr; apply Hoq; exact Hq0 ])
                ltac:(rewrite HD0r; rewrite (lacks_ok_vren _ sq (rren_vren sq Hvs)); exact Hlo)
                ltac:(rewrite Happ; replace (sR S2b r) with (sR Sg r); [ exact Hreq | ];
                      symmetry; exact (Rbo r Hr)))
      as (s & D' & n' & S2 & E & K & Hn & Hd' & Ft & Fr).
    exists s, D', n', S2. refine (conj E (conj K (conj _ (conj Hd' (conj _ _))))).
    + lia.
    + intros x Hx. rewrite <- Tb. exact (Ft x (fun m Hm => Hx m ltac:(lia))).
    + intros q0 Hq0. rewrite <- (Rbo q0 Hq0). exact (Fr q0 (fun m Hm => Hq0 m ltac:(lia))).
  - destruct (bind_row_fin_complete D DT Sg r R R sid n (apR_id R) Hd HK rren_sid Hr eq_refl
                ltac:(intros q0 E; cbn [sR sid idr] in E; injection E as ->; reflexivity)
                ltac:(intros q0 _; reflexivity)
                Hot Hpf Hlc Hnr Hrf Hfld Hlo Hreq)
      as (s & D' & n' & S2 & E & K & Hn & Hd' & Ft & Fr).
    exists s, D', n', S2. exact (conj E (conj K (conj Hn (conj Hd' (conj Ft Fr))))).
Qed.

(* ---- the sort reaches the row variables ---- *)

Lemma bind_row_mid_complete : forall (D DT : denv) Sg r R n,
  DOk D n -> KR D DT Sg -> old n r ->
  (forall x, x `in` ftv_row R -> old n x) -> (forall q, q `in` frv_row R -> old n q) ->
  prf R -> lcrb 0 R = true -> r `notin` frv_row R ->
  frld DT Sg (rk_sort (drk D r)) R -> lacks_ok (drk D r) R = true ->
  reqX bx DT (sR Sg r) (apR Sg R) ->
  exists sr D1 n1 s D' n' S2,
    push_sort_r D (rk_sort (drk D r)) (AtomSetImpl.elements (frv_row R)) n = (sr, D1, n1) /\
    bind_row_core D1 r (apR sr R) n1 = Some (s, D', n') /\ KR D' DT S2 /\ n <= n' /\ DOk D' n' /\
    (forall x, old n x -> teq (sT Sg x) (apT S2 (sT (scomp s sr) x))) /\
    (forall q, old n q -> reqX bx DT (sR Sg q) (apR S2 (sR (scomp s sr) q))).
Proof.
  intros D DT Sg r R n Hd HK Hr Hot Hoq Hpf Hlc Hnr Hfld Hlo Hreq.
  assert (Hrsat : rsat DT (rk_sort (drk D r)) (apR Sg R)).
  { apply (rsat_reqX bx DT _ (sR Sg r) _ Hreq). exact (proj1 (proj2 HK r)). }
  destruct (sat_reach_mut DT Sg (rk_sort (drk D r))) as [_ Hrr].
  destruct (Hrr R Hpf Hfld Hrsat) as [_ Hreach_r].
  assert (Holdr : forall q, In q (AtomSetImpl.elements (frv_row R)) -> old n q)
    by (intros q Hq; apply Hoq; apply in_elts; exact Hq).
  destruct (push_sort_r D (rk_sort (drk D r)) (AtomSetImpl.elements (frv_row R)) n)
    as [[sr D1] n1] eqn:Er.
  destruct (push_sort_r_facts _ _ _ _ _ _ _ Er Holdr) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  pose proof (push_sort_r_dok _ _ _ _ _ _ _ Er Hd) as Hd1.
  pose proof (push_sort_r_new _ _ _ _ _ _ _ Er Holdr) as Qn.
  destruct (push_sort_r_complete _ _ _ (rk_sort (drk D r)) Sg DT Hd HK
              (fun q Hq => Hreach_r q (proj1 (in_elts _ _) Hq)) Holdr sr D1 n1 Er)
    as (S2a & K1 & T1 & Rq).
  assert (Hnl : ~ In r (AtomSetImpl.elements (frv_row R))) by (intros H; apply Hnr; apply in_elts; exact H).
  assert (Hrsr : sR sr r = row_Var r) by exact (Q4 r Hnl).
  assert (Hvs : rren sr) by (split; [ exact Q1 | exact Q5 ]).
  assert (Hr1 : old n1 r) by (intros m Hm; apply Hr; lia).
  assert (HD1r : drk D1 r = drk D r) by exact (Q6 r Hr).
  assert (Hagt : forall x, sT Sg x = apT S2a (sT sr x)).
  { intros x. rewrite (proj1 Hvs x). change (apT S2a (typ_Var x)) with (sT S2a x). rewrite T1. reflexivity. }
  assert (Happ : apR S2a (apR sr R) = apR Sg R).
  { apply (proj2 (ap_agree Sg S2a sr)).
    - intros x _. apply Hagt.
    - intros q Hq. apply Rq. apply Hoq. exact Hq. }
  assert (Hnew1 : forall q q', old n q -> sR sr q = row_Var q' -> old n1 q').
  { intros q q' Hq E m Hm. destruct (Qn q q' Hq E) as [->|[m' [H1 [H2 ->]]]].
    - apply Hq. lia.
    - intros Heq. apply ea_inj in Heq. lia. }
  destruct (bind_row_core_complete D1 DT S2a r (apR sr R) n1 Hd1 K1 Hr1
              ltac:(intros x Hx; rewrite (proj2 (ftv_rren sr Hvs)) in Hx; intros m Hm; apply (Hot x Hx m); lia)
              ltac:(intros z Hz; destruct (frv_vren_in sr (rren_vren sr Hvs) R z Hz) as (q0 & Hq0 & E);
                    exact (Hnew1 q0 z (Hoq q0 Hq0) E))
              ltac:(apply (proj2 (pf_ap sr ltac:(intros x; rewrite (Q1 x); exact I) Q5)); exact Hpf)
              ltac:(unfold apR; rewrite (proj2 (lcb_ap_var (sT sr) (sR sr)
                      (fun x => ex_intro _ x (proj1 Hvs x)) Q5) R 0); exact Hlc)
              ltac:(intros Hin; destruct (frv_vren_in sr (rren_vren sr Hvs) R r Hin) as (q0 & Hq0 & E);
                    destruct (Qn q0 r (Hoq q0 Hq0) E) as [->|[m [H1 [H2 H3]]]];
                    [ exact (Hnr Hq0) | exact (Hr m H1 H3) ])
              ltac:(intros z Hz; destruct (frv_vren_in sr (rren_vren sr Hvs) R z Hz) as (q0 & Hq0 & E);
                    destruct (Q7 q0 (proj2 (in_elts _ _) Hq0)) as (q' & E' & Hf);
                    rewrite E in E'; injection E' as <-; rewrite HD1r; apply finer_b_iff; exact Hf)
              ltac:(rewrite HD1r; refine (proj2 (fld_pull DT Sg S2a _ sr ltac:(intros x; rewrite (Q1 x); exact I) _) R Hpf Hfld _ _);
                    [ intros q0; destruct (Q5 q0) as [q' ->]; exact I
                    | intros x _; apply Hagt
                    | intros q0 Hq0; apply Rq; apply Hoq; exact Hq0 ])
              ltac:(rewrite HD1r; rewrite (lacks_ok_vren _ sr (rren_vren sr Hvs)); exact Hlo)
              ltac:(rewrite Happ; replace (sR S2a r) with (sR Sg r); [ exact Hreq | ];
                    rewrite (Rq r Hr), Hrsr; reflexivity))
    as (s & D' & n' & S2 & E & K & Hn & Hd' & Ft & Fr).
  exists sr, D1, n1, s, D', n', S2. refine (conj eq_refl (conj E (conj K (conj _ (conj Hd' (conj _ _)))))).
  - lia.
  - intros x Hx. change (teq (sT Sg x) (apT S2 (apT s (sT sr x)))). rewrite (proj1 Hvs x).
    change (apT s (typ_Var x)) with (sT s x). rewrite <- T1.
    exact (Ft x (fun m Hm => Hx m ltac:(lia))).
  - intros q Hq. change (reqX bx DT (sR Sg q) (apR S2 (apR s (sR sr q)))).
    destruct (Q5 q) as [q' Eq']. rewrite Eq'. change (apR s (row_Var q')) with (sR s q').
    rewrite (Rq q Hq), Eq'. change (apR S2a (row_Var q')) with (sR S2a q').
    exact (Fr q' (Hnew1 q q' Hq Eq')).
Qed.

(* ---- [bind_row] ---- *)

Theorem bind_row_sorted_complete : forall (D DT : denv) Sg r R n,
  DOk D n -> KR D DT Sg -> old n r ->
  (forall x, x `in` ftv_row R -> old n x) -> (forall q, q `in` frv_row R -> old n q) ->
  prf R -> lcrb 0 R = true -> r `notin` frv_row R ->
  frld DT Sg (rk_sort (drk D r)) R -> reqX bx DT (sR Sg r) (apR Sg R) ->
  exists s D' n' S2, bind_row D r R n = Some (s, D', n') /\ KR D' DT S2 /\ n <= n' /\ DOk D' n' /\
    (forall x, old n x -> teq (sT Sg x) (apT S2 (sT s x))) /\
    (forall q, old n q -> reqX bx DT (sR Sg q) (apR S2 (sR s q))).
Proof.
  intros D DT Sg r R n Hd HK Hr Hot Hoq Hpf Hlc Hnr Hfld Hreq.
  assert (HLK : LK DT (drk D r) (apR Sg R)).
  { apply LK_rkok. exact (rkok_reqX bx DT _ _ _ Hreq (proj2 HK r)). }
  set (ps := abs_vars (drk D r) R).
  assert (Hps : forall p, In p ps -> sT Sg p = typ_Bool) by exact (abs_vars_bool DT _ Sg R HLK).
  assert (Hchk : forallb (fun p => sat_b D (D p) typ_Bool) ps = true).
  { apply forallb_forall. intros p Hp. apply sat_b_iff.
    pose proof (proj1 HK p) as H. rewrite (Hps p Hp) in H. exact H. }
  unfold bind_row. cbn zeta. fold ps. rewrite Hchk.
  set (R0 := apR (bool_sub ps) R).
  destruct (bool_sub_agree Sg ps Hps) as [A0t A0r].
  assert (Hu1 := bool_sub_T_cases ps). assert (Hu2 := bool_sub_R ps).
  assert (Hftv : forall x, x `in` ftv_row R0 -> x `in` ftv_row R) by exact (bs_ftv_in _ Hu1 Hu2 R).
  assert (Hfrv : forall q, q `in` frv_row R0 -> q `in` frv_row R) by exact (bs_frv_in _ Hu1 Hu2 R).
  assert (Hpfs : forall x, pf (sT (bool_sub ps) x))
    by (intros x; destruct (Hu1 x) as [E|E]; rewrite E; exact I).
  assert (Hlcs : forall x k, lcb k (sT (bool_sub ps) x) = true)
    by (intros x k; destruct (Hu1 x) as [E|E]; rewrite E; reflexivity).
  assert (Hpf0 : prf R0)
    by exact (proj2 (pf_ap (bool_sub ps) Hpfs (fun q => ex_intro _ q (Hu2 q))) R Hpf).
  assert (Hlc0 : lcrb 0 R0 = true)
    by exact (proj2 (lcb_ap_closed (bool_sub ps) Hlcs (fun q => ex_intro _ q (Hu2 q))) R 0 Hlc).
  assert (Hnr0 : r `notin` frv_row R0) by (intros H; exact (Hnr (Hfrv r H))).
  assert (Hocc : occR r R0 = false).
  { unfold occR. apply Bool.orb_false_iff. split.
    - apply AtomSetFacts.not_mem_iff. exact Hnr0.
    - rewrite Hlc0. reflexivity. }
  assert (Happ0 : apR Sg R0 = apR Sg R) by exact (proj2 (ap_agree Sg Sg (bool_sub ps)) R
                                                  (fun x _ => A0t x) (fun q _ => A0r q)).
  rewrite Hocc. cbn iota.
  destruct (bind_row_mid_complete D DT Sg r R0 n Hd HK Hr
              (fun x Hx => Hot x (Hftv x Hx)) (fun q Hq => Hoq q (Hfrv q Hq)) Hpf0 Hlc0 Hnr0
              ltac:(refine (proj2 (fld_pull DT Sg Sg _ (bool_sub ps) _ _) R Hpf Hfld _ _);
                    [ intros x; destruct (Hu1 x) as [E|E]; rewrite E; exact I
                    | intros q; rewrite Hu2; exact I
                    | intros x _; apply A0t
                    | intros q _; apply A0r ])
              (lacks_ok_bs DT _ Sg R ps HLK (fun p H => H))
              ltac:(rewrite Happ0; exact Hreq))
    as (sr & D1 & n1 & s & D' & n' & S2 & Er & Ec & K & Hn & Hd' & Ft & Fr).
  rewrite Er. cbn iota. rewrite Ec.
  exists (scomp s (scomp sr (bool_sub ps))), D', n', S2.
  refine (conj eq_refl (conj K (conj Hn (conj Hd' (conj _ _))))).
  - intros x Hx. change (teq (sT Sg x) (apT S2 (apT s (apT sr (sT (bool_sub ps) x))))).
    destruct (in_dec Atom.eq_dec x ps) as [Hin|Hin].
    + rewrite (bool_sub_in ps x Hin), (Hps x Hin). apply teq_refl.
    + rewrite (bool_sub_out ps x Hin). exact (Ft x Hx).
  - intros q Hq. change (reqX bx DT (sR Sg q) (apR S2 (apR s (apR sr (sR (bool_sub ps) q))))).
    rewrite Hu2. exact (Fr q Hq).
Qed.

End RowX.

(* END *)
