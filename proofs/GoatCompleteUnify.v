(* Completeness of algorithm W, stage 7.6, part L2: the plain unifier finds a
   most general unifier (docs/design/phase7-proof-plan.md).

   The fragment is the types with no recursion, no tag group and no row
   variable: base types, variables, arrows, and, when [b] is [true], records
   of closed rows ([crow]: a spine of fields, no tail variable, no presence
   entry), fields again in the fragment.  Substitution images are arbitrary:
   the variables stand for any type, and an image may hold a presence entry or
   a row variable the unifier never sees.  What is assumed of the substitution
   [S] is that it unifies the two types up to [teq] and respects the sorts
   ([kres D D1 (sT S)]).  The unifier then succeeds, from some fuel on
   ([Stable]), with a substitution [s] that is in the fragment and that [S]
   factors through ([Fac S s]: [S x] is [teq] to [S] applied to [s x]).  No
   variable is renamed or invented (a variable's sort is pushed only onto a
   record's variables, and only a record under a sorted variable needs it; with
   [b = true] every sort is [Any]), so the environment and the supply come back
   unchanged and the factoring substitution is [S] itself.

   The measure is the size of the image ([tsz], [GoatCompleteRows.v]), which
   [teq] and [req] preserve; the factoring lemma carries it from [S x] to [S]
   applied to [s x]. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteRows.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the fragment ---- *)

Fixpoint cp (b : bool) (T : typ) {struct T} : Prop :=
  match T with
  | typ_Int | typ_Float | typ_Bool | typ_Unit | typ_String | typ_Var _ => True
  | typ_Arrow A B => cp b A /\ cp b B
  | typ_Record R => b = true /\ crow b R
  | _ => False
  end
with crow (b : bool) (R : row) {struct R} : Prop :=
  match R with
  | row_Empty => True
  | row_Ext _ T R' => cp b T /\ crow b R'
  | _ => False
  end.

Lemma crow_cext : forall b R, crow b R -> cext R.
Proof. intros b R. induction R; simpl; try tauto. Qed.

Lemma crow_rm : forall b l R, crow b R -> crow b (rm_l l R).
Proof.
  intros b l R. induction R; simpl; try tauto.
  intros [HT HR]. destruct (Nat.eqb l l0); [ exact HR | simpl; auto ].
Qed.

Lemma crow_get : forall b l R T, crow b R -> get_l l R = Some T -> cp b T.
Proof.
  intros b l R T. induction R; simpl; try tauto; try (intros _ E; discriminate E).
  intros [HT HR] E. destruct (Nat.eqb l l0); [ inversion E; subst; exact HT | eauto ].
Qed.

Lemma cp_lcb : forall b,
  (forall T, cp b T -> forall k, lcb k T = true) /\ (forall R, crow b R -> forall k, lcrb k R = true).
Proof.
  intros b. apply typ_row_mutind; simpl; try (intros; reflexivity); try (intros; contradiction).
  - intros A IHA B IHB [HA HB] k. rewrite (IHA HA), (IHB HB). reflexivity.
  - intros R IH [_ HR] k. apply IH. exact HR.
  - intros l T IHT R IHR [HT HR] k. rewrite (IHT HT), (IHR HR). reflexivity.
Qed.

(* A substitution in the fragment: type variables go to fragment types, row
   variables stay. *)
Definition CpS (b : bool) (s : sub) : Prop :=
  (forall x, cp b (sT s x)) /\ (forall r, sR s r = row_Var r).

Lemma cp_ap : forall b s, CpS b s ->
  (forall T, cp b T -> cp b (apT s T)) /\ (forall R, crow b R -> crow b (apR s R)).
Proof.
  intros b s [Hs Hr]. unfold apT, apR. apply typ_row_mutind; simpl;
    try (intros; exact I); try (intros; contradiction).
  - intros A IHA B IHB [HA HB]. split; auto.
  - intros R IH [Hb HR]. split; auto.
  - intros a _. apply Hs.
  - intros l T IHT R IHR [HT HR']. split; auto.
Qed.

(* [S] factors through [s]: [S x] equals [S] applied to [s x]. *)
Definition Fac (S s : sub) : Prop := forall x, teq (sT S x) (apT S (sT s x)).

Lemma fac_ap : forall b S s, CpS b s -> Fac S s ->
  (forall T, cp b T -> teq (apT S T) (apT S (apT s T))) /\
  (forall R, crow b R -> req (apR S R) (apR S (apR s R))).
Proof.
  intros b S s Hc Hf. unfold Fac, apT in Hf. unfold apT, apR.
  apply typ_row_mutind; simpl; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try contradiction;
    first [ apply Hf | apply teq_arrow | apply teq_rec | apply req_head
          | apply teq_refl | apply req_refl ]; eauto.
Qed.

Definition Res (b : bool) (S s : sub) : Prop := CpS b s /\ Fac S s.

Lemma Res_sid : forall b S, Res b S sid.
Proof.
  intros b S. split; [ split | ].
  - intros x. exact I.
  - intros r. reflexivity.
  - intros x. apply teq_refl.
Qed.

Lemma Res_comp : forall b S s1 s2, Res b S s1 -> Res b S s2 -> Res b S (scomp s2 s1).
Proof.
  intros b S s1 s2 [[C1 R1] F1] [[C2 R2] F2]. split; [ split | ].
  - intros x. change (cp b (apT s2 (sT s1 x))).
    apply (proj1 (cp_ap b s2 (conj C2 R2))). apply C1.
  - intros r. change (ap_row (sT s2) (sR s2) (sR s1 r) = row_Var r).
    rewrite R1. simpl. apply R2.
  - intros x. change (teq (sT S x) (apT S (apT s2 (sT s1 x)))).
    eapply teq_trans; [ apply F1 | ].
    exact (proj1 (fac_ap b S s2 (conj C2 R2) F2) _ (C1 x)).
Qed.

Lemma Res_sbT : forall b S a T, cp b T -> teq (sT S a) (apT S T) -> Res b S (sbT a T).
Proof.
  intros b S a T HT Heq. split; [ split | ].
  - intros x. simpl. destruct (Atom.eq_dec x a); [ exact HT | exact I ].
  - intros r. reflexivity.
  - intros x. simpl. destruct (Atom.eq_dec x a) as [->|]; [ exact Heq | apply teq_refl ].
Qed.

Lemma Res_bind : forall b S a T, cp b T -> teq (sT S a) (apT S T) ->
  Res b S (scomp (sbT a T) (scomp sid sid)).
Proof.
  intros b S a T HT Heq.
  apply Res_comp; [ apply Res_comp; apply Res_sid | exact (Res_sbT b S a T HT Heq) ].
Qed.

(* ---- the occurs check never rejects ---- *)

Lemma tsz_occ : forall b S a,
  (forall T, cp b T -> a `in` ftv_typ T -> tsz (sT S a) <= tsz (apT S T)) /\
  (forall R, crow b R -> a `in` ftv_row R -> tsz (sT S a) <= rsz (apR S R)).
Proof.
  intros b S a. unfold apT, apR.
  apply typ_row_mutind; simpl; try (intros; exfalso; fsetdec); try (intros; contradiction).
  - intros A IHA B IHB [HA HB] Hin. apply AtomSetFacts.union_iff in Hin.
    destruct Hin as [H|H]; [ pose proof (IHA HA H) | pose proof (IHB HB H) ]; lia.
  - intros R IH [_ HR] Hin. pose proof (IH HR Hin). lia.
  - intros x _ Hin. apply AtomSetFacts.singleton_iff in Hin. subst. lia.
  - intros l T IHT R IHR [HT HR] Hin. apply AtomSetFacts.union_iff in Hin.
    destruct Hin as [H|H]; [ pose proof (IHT HT H) | pose proof (IHR HR H) ]; lia.
Qed.

Lemma not_occ : forall b S a T, cp b T -> (forall v, T <> typ_Var v) ->
  teq (sT S a) (apT S T) -> a `notin` ftv_typ T.
Proof.
  intros b S a T HT Hv Heq Hin.
  pose proof (teq_tsz _ _ Heq) as Hs.
  pose proof (tsz_occ b S a) as [Ht Hr].
  destruct T; simpl in HT, Hin; try contradiction; try fsetdec;
    try (exfalso; exact (Hv _ eq_refl)).
  - destruct HT as [HA HB]. apply AtomSetFacts.union_iff in Hin.
    unfold apT in Hs. simpl in Hs.
    destruct Hin as [H|H]; [ pose proof (Ht _ HA H) | pose proof (Ht _ HB H) ];
      unfold apT in *; lia.
  - destruct HT as [_ HR]. pose proof (Hr _ HR Hin). unfold apT, apR in *. simpl in Hs. lia.
Qed.

(* ---- binding a variable ---- *)

Lemma finer_b_any : forall k, finer_b k k_Any = true.
Proof. intros []; reflexivity. Qed.

Lemma push_sort_any : forall l D n, push_sort D k_Any l n = (sid, D, n).
Proof. induction l; intros; simpl; [ reflexivity | ]. rewrite finer_b_any. apply IHl. Qed.

Lemma push_sort_r_any : forall l D n, push_sort_r D k_Any l n = (sid, D, n).
Proof.
  induction l; intros; simpl; [ reflexivity | ]. rewrite finer_b_any. apply IHl.
Qed.

Lemma sat_b_any : forall D T, sat_b D k_Any T = true.
Proof. intros D T. destruct T; simpl; first [ reflexivity | apply finer_b_any ]. Qed.

Lemma bind_prop_any : forall (D : denv) a T (n : nat), D a = k_Any -> occT a T = false ->
  bind_prop D a T n = Some (scomp (sbT a T) (scomp sid sid), D, n).
Proof.
  intros D a T n Ha Ho. unfold bind_prop. rewrite Ho, Ha, push_sort_any.
  cbn match. rewrite Ha, push_sort_r_any. cbn match. rewrite !apT_id, Ho, Ha, sat_b_any.
  reflexivity.
Qed.

Lemma bind_prop_scalar : forall (D : denv) a c (n : nat),
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) ->
  sat_b D (D a) c = true ->
  bind_prop D a c n = Some (scomp (sbT a c) (scomp sid sid), D, n).
Proof.
  intros D a c n Hc Hs.
  assert (Hf : ftv_typ c = empty /\ frv_typ c = empty)
    by (destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; split; reflexivity).
  assert (Ho : occT a c = false).
  { unfold occT. rewrite (proj1 Hf). apply Bool.orb_false_iff. split.
    - apply AtomSetFacts.not_mem_iff. fsetdec.
    - destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; reflexivity. }
  unfold bind_prop. rewrite Ho, (proj1 Hf), (proj2 Hf), AtomSetProperties.elements_empty.
  cbn [push_sort push_sort_r]. cbn iota. rewrite !apT_id, Ho, Hs. reflexivity.
Qed.

Lemma sat_scalar : forall (D D1 : denv) a c,
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) ->
  sat D1 (D a) c -> sat_b D (D a) c = true.
Proof.
  intros D D1 a c Hc Hs.
  destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; simpl in Hs |- *; try reflexivity;
    destruct (D a); simpl in Hs |- *; try reflexivity; destruct Hs as [H|H]; discriminate H.
Qed.

Lemma bind_prop_complete : forall b S (D D1 : denv) a T (n : nat),
  (b = true -> forall c, D c = k_Any) -> kres D D1 (sT S) ->
  cp b T -> (forall v, T <> typ_Var v) -> teq (sT S a) (apT S T) ->
  bind_prop D a T n = Some (scomp (sbT a T) (scomp sid sid), D, n).
Proof.
  intros b S D D1 a T n Hs Hk HT Hv Heq.
  assert (Ho : occT a T = false).
  { unfold occT. apply Bool.orb_false_iff. split.
    - apply AtomSetFacts.not_mem_iff. exact (not_occ b S a T HT Hv Heq).
    - rewrite (proj1 (cp_lcb b) T HT 0). reflexivity. }
  assert (Hk' := Hk a). unfold kres in Hk.
  destruct T; try (exfalso; simpl in HT; contradiction); try (exfalso; exact (Hv _ eq_refl)).
  all: try (apply bind_prop_scalar; [ tauto | ];
            apply (sat_scalar D D1 a); [ tauto | ];
            apply teq_sym in Heq; cbn in Heq;
            first [ rewrite (teq_Int_inv _ Heq) in Hk' | rewrite (teq_Float_inv _ Heq) in Hk'
                  | rewrite (teq_Bool_inv _ Heq) in Hk' | rewrite (teq_Unit_inv _ Heq) in Hk'
                  | rewrite (teq_String_inv _ Heq) in Hk' ]; exact Hk').
  - (* Arrow *)
    apply bind_prop_any; [ | exact Ho ].
    apply teq_sym in Heq. destruct (teq_Arrow_inv _ _ _ Heq) as (A' & B' & E & _).
    rewrite E in Hk'. exact Hk'.
  - (* Record *)
    destruct HT as [Hb _]. apply bind_prop_any; [ exact (Hs Hb a) | exact Ho ].
Qed.

Lemma unify_var_nonvar : forall b S (D D1 : denv) a T (n : nat),
  (b = true -> forall c, D c = k_Any) -> kres D D1 (sT S) ->
  cp b T -> (forall v, T <> typ_Var v) -> teq (sT S a) (apT S T) ->
  exists s, Res b S s /\ Stable (fun f => unify_t f D (typ_Var a) T n = Some (s, D, n)).
Proof.
  intros b S D D1 a T n Hs Hk HT Hv Heq.
  pose proof (bind_prop_complete b S D D1 a T n Hs Hk HT Hv Heq) as E.
  exists (scomp (sbT a T) (scomp sid sid)). split; [ exact (Res_bind b S a T HT Heq) | ].
  exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  destruct T; try (exfalso; exact (Hv _ eq_refl)); exact E.
Qed.

Lemma unify_nonvar_var : forall b S (D D1 : denv) a T (n : nat),
  (b = true -> forall c, D c = k_Any) -> kres D D1 (sT S) ->
  cp b T -> (forall v, T <> typ_Var v) -> teq (apT S T) (sT S a) ->
  exists s, Res b S s /\ Stable (fun f => unify_t f D T (typ_Var a) n = Some (s, D, n)).
Proof.
  intros b S D D1 a T n Hs Hk HT Hv Heq.
  apply teq_sym in Heq.
  pose proof (bind_prop_complete b S D D1 a T n Hs Hk HT Hv Heq) as E.
  exists (scomp (sbT a T) (scomp sid sid)). split; [ exact (Res_bind b S a T HT Heq) | ].
  exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  destruct T; try (exfalso; exact (Hv _ eq_refl)); exact E.
Qed.

Lemma unify_var_var : forall b S (D : denv) a a' (n : nat), teq (sT S a) (sT S a') ->
  exists s, Res b S s /\ Stable (fun f => unify_t f D (typ_Var a) (typ_Var a') n = Some (s, D, n)).
Proof.
  intros b S D a a' n Heq. destruct (Atom.eq_dec a a') as [->|Hne].
  - exists sid. split; [ apply Res_sid | exists 1; intros f Hf; destruct f as [|f]; [ lia | ] ].
    cbn [unify_t]. destruct (Atom.eq_dec a' a'); [ reflexivity | congruence ].
  - destruct (finer_b (D a') (D a)) eqn:Ef.
    + exists (sbT a (typ_Var a')). split; [ exact (Res_sbT b S a (typ_Var a') I Heq) | ].
      exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
      cbn [unify_t]. destruct (Atom.eq_dec a a'); [ congruence | ]. rewrite Ef. reflexivity.
    + exists (sbT a' (typ_Var a)). split; [ exact (Res_sbT b S a' (typ_Var a) I (teq_sym _ _ Heq)) | ].
      exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
      cbn [unify_t]. destruct (Atom.eq_dec a a'); [ congruence | ]. rewrite Ef. reflexivity.
Qed.

Lemma apT_Arrow : forall S A B, apT S (typ_Arrow A B) = typ_Arrow (apT S A) (apT S B).
Proof. reflexivity. Qed.

Lemma apT_Record : forall S R, apT S (typ_Record R) = typ_Record (apR S R).
Proof. reflexivity. Qed.

Lemma unify_scalar_same : forall b S (D : denv) c (n : nat),
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) ->
  exists s, Res b S s /\ Stable (fun f => unify_t f D c c n = Some (s, D, n)).
Proof.
  intros b S D c n Hc. exists sid. split; [ apply Res_sid | exists 1; intros f Hf ].
  destruct f as [|f]; [ lia | ].
  destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; reflexivity.
Qed.

(* A closed row has no presence entry, so there is nothing to drop. *)
Lemma drop_abs_crow : forall b R, crow b R -> drop_abs R = R.
Proof.
  intros b R. induction R as [| r | l T R IH | l P T R IH]; simpl; intros C;
    try reflexivity; try contradiction.
  f_equal. apply IH. exact (proj2 C).
Qed.

(* ---- the theorem ---- *)

Ltac nv := intros ? E; discriminate E.

Theorem unify_complete_aux : forall b S (D D1 : denv),
  (b = true -> forall c, D c = k_Any) -> kres D D1 (sT S) -> forall m,
  (forall T1 T2 n, cp b T1 -> cp b T2 -> tsz (apT S T1) < m ->
     teq (apT S T1) (apT S T2) ->
     exists s, Res b S s /\ Stable (fun f => unify_t f D T1 T2 n = Some (s, D, n))) /\
  (forall R1 R2 n, crow b R1 -> crow b R2 -> rsz (apR S R1) < m ->
     req (apR S R1) (apR S R2) ->
     exists s, Res b S s /\ Stable (fun f => unify_r f D R1 R2 n = Some (s, D, n))).
Proof.
  intros b S D D1 Hs Hk. induction m as [|m IH]; [ split; intros; lia | ].
  destruct IH as [IHt IHr]. split.
  - (* types *)
    intros T1 T2 n C1 C2 Hlt Hteq.
    destruct T1 as [ | | | | | A B | R | a | i | B1 | w A1 ]; try (simpl in C1; contradiction);
    destruct T2 as [ | | | | | A' B' | R' | a' | i' | B1' | w' A1' ];
      try (simpl in C2; contradiction);
    try (exfalso; pose proof (teq_thead _ _ Hteq) as Ht; unfold apT in Ht;
         cbn [ap_typ thead_tag] in Ht; discriminate Ht).
    all: try (apply unify_scalar_same; tauto).
    all: try (apply unify_var_nonvar with (D1 := D1); [ exact Hs | exact Hk | exact C2 | nv | exact Hteq ]).
    all: try (apply unify_nonvar_var with (D1 := D1); [ exact Hs | exact Hk | exact C1 | nv | exact Hteq ]).
    + (* Arrow, Arrow *)
      destruct C1 as [CA CB], C2 as [CA' CB'].
      rewrite apT_Arrow in Hlt. simpl in Hlt.
      rewrite !apT_Arrow in Hteq.
      destruct (teq_Arrow_inv _ _ _ Hteq) as (X & Y & EX & H1 & H2).
      injection EX as <- <-.
      destruct (IHt A A' n CA CA' ltac:(lia) H1) as (s1 & Hr1 & E1).
      destruct Hr1 as [Hc1 Hf1]. pose proof (conj Hc1 Hf1 : Res b S s1) as Hr1.
      pose proof (fac_ap b S s1 Hc1 Hf1) as [FT _].
      pose proof (FT B CB) as FB. pose proof (FT B' CB') as FB'.
      destruct (IHt (apT s1 B) (apT s1 B') n
                  ((proj1 (cp_ap b s1 Hc1)) _ CB) ((proj1 (cp_ap b s1 Hc1)) _ CB')
                  ltac:(rewrite <- (teq_tsz _ _ FB); lia)
                  (teq_trans _ _ _ (teq_sym _ _ FB) (teq_trans _ _ _ H2 FB')))
        as (s2 & Hr2 & E2).
      exists (scomp s2 s1). split; [ exact (Res_comp b S s1 s2 Hr1 Hr2) | ].
      eapply Stable_mono; [ | exact (Stable_below _ (Stable_and _ _ E1 E2)) ].
      intros [|f] Hf; [ contradiction | ]. destruct Hf as [Ha Hb].
      cbn [unify_t]. rewrite Ha, Hb. reflexivity.
    + (* Record, Record *)
      destruct C1 as [Hb CR], C2 as [_ CR'].
      rewrite apT_Record in Hlt. simpl in Hlt.
      rewrite !apT_Record in Hteq.
      destruct (teq_Record_inv _ _ Hteq) as (X & EX & H1). injection EX as <-.
      destruct (IHr R R' n CR CR' ltac:(lia) H1) as (s & Hr & E).
      exists s. split; [ exact Hr | ].
      eapply Stable_mono; [ | exact (Stable_below _ E) ].
      intros [|f] Hf; [ contradiction | ]. cbn [unify_t].
      rewrite (drop_abs_crow b R CR), (drop_abs_crow b R' CR'). exact Hf.
    + (* Var, Var *)
      apply unify_var_var. exact Hteq.
  - (* rows *)
    intros R1 R2 n C1 C2 Hlt Hreq.
    destruct R1 as [ | r | l T R1' | l P T R1' ]; try (simpl in C1; contradiction);
    destruct R2 as [ | q | l2 T2 R2' | l2 P2 T2 R2' ]; try (simpl in C2; contradiction).
    + (* Empty, Empty *)
      exists sid. split; [ apply Res_sid | exists 1; intros f Hf; destruct f as [|f]; [ lia | reflexivity ] ].
    + (* Empty, Ext *)
      exfalso. pose proof (req_pi _ _ Hreq l2) as H. rewrite pi_apR_ext in H.
      change (apR S row_Empty) with (row_Empty) in H. simpl in H. inversion H.
    + (* Ext, Empty *)
      exfalso. pose proof (req_pi _ _ Hreq l) as H. rewrite pi_apR_ext in H.
      change (apR S row_Empty) with (row_Empty) in H. simpl in H. inversion H.
    + (* Ext, Ext *)
      destruct C1 as [CT CR1], C2 as [CT2 CR2].
      remember (row_Ext l2 T2 R2') as R2 eqn:ER2.
      assert (CR2f : crow b R2) by (subst R2; simpl; tauto).
      assert (Hx2 : cext R2) by exact (crow_cext b R2 CR2f).
      assert (HxY : cext (apR S R2)) by exact (cext_ap S R2 Hx2).
      assert (Hx1 : cext R1') by exact (crow_cext b R1' CR1).
      pose proof (req_pi _ _ Hreq l) as Hpl. rewrite pi_apR_ext in Hpl.
      destruct (pi l (apR S R2)) as [|B rest] eqn:Epi; [ inversion Hpl | ].
      inversion Hpl as [|? ? ? ? Hh Ht].
      destruct (get_l l (apR S R2)) as [B0|] eqn:Eg;
        [ | pose proof (pi_get_none _ _ HxY Eg) as Hn; rewrite Hn in Epi; discriminate Epi ].
      destruct (pi_get_some _ _ _ HxY Eg) as [Hp Hm]. rewrite Hp in Epi.
      injection Epi as EB Hrest. subst B0.
      rewrite (get_l_ap S l R2 Hx2) in Eg.
      destruct (get_l l R2) as [T'|] eqn:Eg2; [ | discriminate Eg ].
      simpl in Eg. injection Eg as <-.
      pose proof (crow_get b l R2 T' CR2f Eg2) as CT'.
      pose proof (crow_rm b l R2 CR2f) as CRm.
      assert (Hpi_aux : forall k, k <> l -> Forall2 teq (pi k (apR S R1')) (pi k (apR S R2))).
      { intros k Hne. pose proof (req_pi _ _ Hreq k) as Hq. rewrite apR_Ext in Hq. cbn [pi] in Hq.
        destruct (Nat.eqb k l) eqn:E; [ apply Nat.eqb_eq in E; congruence | exact Hq ]. }
      assert (Hrq : req (apR S R1') (apR S (rm_l l R2))).
      { apply req_of_pi; [ exact (cext_ap S _ Hx1) | exact (cext_ap S _ (cext_rm l R2 Hx2)) | ].
        rewrite <- (rm_l_ap S l R2 Hx2). intros k. destruct (Nat.eq_dec k l) as [->|Hne].
        - rewrite Hrest. exact Ht.
        - rewrite (Hm k Hne). exact (Hpi_aux k Hne). }
      rewrite apR_Ext in Hlt. simpl in Hlt.
      destruct (IHt T T' n CT CT' ltac:(lia) Hh) as (s1 & [Hc1 Hf1] & E1).
      pose proof (conj Hc1 Hf1 : Res b S s1) as Hr1.
      pose proof (fac_ap b S s1 Hc1 Hf1) as [_ FR].
      pose proof (FR R1' CR1) as FR1. pose proof (FR (rm_l l R2) CRm) as FR2.
      destruct (IHr (apR s1 R1') (apR s1 (rm_l l R2)) n
                  (proj2 (cp_ap b s1 Hc1) _ CR1) (proj2 (cp_ap b s1 Hc1) _ CRm)
                  ltac:(rewrite <- (req_rsz _ _ FR1); lia)
                  (req_trans _ _ _ (req_sym _ _ FR1) (req_trans _ _ _ Hrq FR2)))
        as (s2 & Hr2 & E3).
      exists (scomp s2 (scomp s1 (scomp sid sid))). split.
      { apply Res_comp; [ apply Res_comp; [ apply Res_comp; apply Res_sid | exact Hr1 ] | exact Hr2 ]. }
      assert (E0 : Stable (fun f => unify_t f D (apT sid typ_Unit) typ_Unit n = Some (sid, D, n))).
      { exists 1. intros [|f] Hf; [ lia | ]. rewrite apT_id. reflexivity. }
      assert (E1' : Stable (fun f => unify_t f D (apT sid (apT sid T)) (apT sid T') n = Some (s1, D, n))).
      { eapply Stable_mono; [ | exact E1 ]. intros f Hf. rewrite !apT_id. exact Hf. }
      assert (E3' : Stable (fun f => unify_r f D (drop_abs (apR s1 (apR sid (apR sid R1'))))
                                       (drop_abs (apR s1 (apR sid (rm_l l R2)))) n = Some (s2, D, n))).
      { eapply Stable_mono; [ | exact E3 ]. intros f Hf. rewrite !apR_id.
        rewrite (drop_abs_crow b _ (proj2 (cp_ap b s1 Hc1) _ CR1)),
                (drop_abs_crow b _ (proj2 (cp_ap b s1 Hc1) _ CRm)). exact Hf. }
      eapply Stable_mono; [ | exact (Stable_below _ (Stable_and _ _ E0 (Stable_and _ _ E1' E3'))) ].
      intros [|f] Hf; [ contradiction | ]. destruct Hf as (Hu0 & Hu1 & Hu3).
      pose proof (rewrite_row_found l (frv_row (row_Ext l T R1')) D R2 n T' Hx2 Eg2) as Erw.
      subst R2. cbn [unify_r row_head]. rewrite Erw. cbn iota beta. rewrite Hu0. cbn iota beta.
      rewrite Hu1. cbn iota beta. rewrite Hu3. reflexivity.
Qed.

(* ---- statements ---- *)

Theorem unify_t_complete : forall b S (D D1 : denv) T1 T2 n,
  (b = true -> forall c, D c = k_Any) -> kres D D1 (sT S) ->
  cp b T1 -> cp b T2 -> teq (apT S T1) (apT S T2) ->
  exists s, Res b S s /\ Stable (fun f => unify_t f D T1 T2 n = Some (s, D, n)).
Proof.
  intros b S D D1 T1 T2 n Hs Hk C1 C2 Hteq.
  exact (proj1 (unify_complete_aux b S D D1 Hs Hk (Datatypes.S (tsz (apT S T1)))) T1 T2 n C1 C2
           (Nat.lt_succ_diag_r _) Hteq).
Qed.

Theorem unify_r_complete : forall b S (D D1 : denv) R1 R2 n,
  (b = true -> forall c, D c = k_Any) -> kres D D1 (sT S) ->
  crow b R1 -> crow b R2 -> req (apR S R1) (apR S R2) ->
  exists s, Res b S s /\ Stable (fun f => unify_r f D R1 R2 n = Some (s, D, n)).
Proof.
  intros b S D D1 R1 R2 n Hs Hk C1 C2 Hreq.
  exact (proj2 (unify_complete_aux b S D D1 Hs Hk (Datatypes.S (rsz (apR S R1)))) R1 R2 n C1 C2
           (Nat.lt_succ_diag_r _) Hreq).
Qed.

(* The coercion-aware unifier, through which W calls the plain one, returns the
   same unifier and no coercion. *)
Theorem unify_co_complete : forall b S (D D1 : denv) T1 T2 n,
  (b = true -> forall c, D c = k_Any) -> kres D D1 (sT S) ->
  cp b T1 -> cp b T2 -> teq (apT S T1) (apT S T2) ->
  exists s, Res b S s /\ Stable (fun f => unify_co f D T1 T2 n = Some (s, D, nil, n)).
Proof.
  intros b S D D1 T1 T2 n Hs Hk C1 C2 Hteq.
  destruct (unify_t_complete b S D D1 T1 T2 n Hs Hk C1 C2 Hteq) as (s & Hr & [f0 Hf]).
  exists s. split; [ exact Hr | ].
  exact (unify_co_stable f0 D T1 T2 n s D n (Hf f0 (le_n _))).
Qed.

(* ---- what the fragment leaves out ----

   Rows with a tail variable.  The unifier rewrites a row variable that lacks
   the label (to an absent entry) and one whose sort is finer than [Any] (the
   field variable takes the sort), so the fresh variables [rewrite_row] and
   [bind_row] invent are all that stands between the statements above and such
   rows: the invention of the factoring substitution for them is not proved. *)

Example rewrite_row_lacking : forall l m B r av (D : denv) n,
  l <> m -> AtomSetImpl.mem r av = false -> rk_lacks (drk D r) l = true ->
  rewrite_row l av D (row_Ext m B (row_Var r)) n <> None.
Proof.
  intros l m B r av D n Hne Hm Hl. simpl.
  destruct (Nat.eqb l m) eqn:E; [ apply Nat.eqb_eq in E; congruence | ].
  cbn iota. rewrite Hm, Hl. discriminate.
Qed.
