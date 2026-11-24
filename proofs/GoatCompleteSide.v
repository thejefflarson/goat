(* Completeness of algorithm W, stage 7.6f, part (2): Leijen's side condition
   on [rewrite_row] (docs/design/phase7-proof-plan.md).

   [unify_rD] rewrites the second row so that it presents the first row's front
   label, and [rewrite_row] refuses to bind the row variable at the tail of the
   second row when it is in [av], the row variables of the first row.  The
   condition is sound where Leijen states it: when the two rows end in the
   same row variable, the second has no entry of the label, and the first has a
   present entry of it, no substitution makes them [req] ([leijen_tail]): the
   first has one more present entry of the label than the second, and a
   substitution adds the same entries to both through their common tail.

   [rewrite_row]'s [av] is the tail of the first row ([side_av]).  The
   checker's earlier [av], every row variable of the first row, refused a
   unifiable pair whose second row ends in a variable that occurs only inside a
   field of the first:
       {l0: Int, l1: {...r}}  against  {l1: c, ...r}
   is unified by [r := {l0: Int}] and [c := {l0: Int}] ([nested_sub_unifies]),
   the variable is in a field type and not in the first row's tail, and the
   checker accepts the program that unifies them, so [side_av] reads the tail
   alone ([side_passes_nested]).  [side_guard_passes] is the completeness of
   that guard: a unifier of two rows whose first entry it makes present never
   meets it.

   What stays is the first entry whose presence is a variable the unifier makes
   absent ([side_blocks_absent]):
       {l0^p: Int, ...r}  against  {l1^q: Int, ...r}
   is unified by [p := Bool], [q := Bool], [r := {}]: both rows are the empty
   row once their entries are absent.  The occurs checks of [bind_row] and
   [bind_prop] read a variable behind an absent entry as an occurrence, and
   refuse unifiable pairs the same way ([bind_row_blocks_absent_tail],
   [bind_prop_blocks_absent]).  The checker has no guard to compare with there
   (it ties a recursive type, or refuses), and the triage found no goat
   program that reaches either pair, so the plan states the induction with a
   hypothesis that excludes them (option (b) of the stage 7.6f decision). *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatRowNf.
Require Import Goat.GoatDefs.
Require Import Goat.GoatInfer.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the number of present entries of a label ---- *)

Fixpoint cnt (es : list (typ * typ)) : nat :=
  match es with
  | nil => 0
  | e :: es' => (if is_unit (fst e) then 1 else 0) + cnt es'
  end.

Lemma is_abs_not_unit : forall T, is_abs T = true -> is_unit T = false.
Proof. intros T. destruct T; simpl; intros; try reflexivity; discriminate. Qed.

Lemma cnt_dropT : forall es, cnt (dropT es) = cnt es.
Proof.
  induction es as [ | e es IH ]; [ reflexivity | ].
  simpl dropT. unfold cons_d. destruct (dropT es) eqn:E.
  - simpl in IH. destruct (is_abs (fst e)) eqn:Ha.
    + simpl. rewrite (is_abs_not_unit _ Ha). simpl. lia.
    + simpl. rewrite <- IH. reflexivity.
  - simpl. rewrite <- IH. simpl. reflexivity.
Qed.

Lemma cnt_ents_t : forall t es, cnt (ents_t t es) = cnt es.
Proof. intros t es. destruct t; [ apply cnt_dropT | reflexivity | reflexivity | reflexivity ]. Qed.

Lemma cnt_Forall2 : forall a b, Forall2 ent_eq a b -> cnt a = cnt b.
Proof.
  induction 1 as [ | e e' a b [Hp _] _ IH ]; [ reflexivity | ].
  simpl. rewrite IH. rewrite (teq_is_unit _ _ Hp). reflexivity.
Qed.

Lemma req_cnt : forall R1 R2, req R1 R2 -> forall l, cnt (raw l R1) = cnt (raw l R2).
Proof.
  intros R1 R2 H l. apply req_nf in H as [_ H]. specialize (H l).
  apply cnt_Forall2 in H. unfold ents in H. rewrite !cnt_ents_t in H. exact H.
Qed.

(* ---- a substitution adds the entries of the tail's image ---- *)

Lemma cnt_app : forall a b, cnt (a ++ b) = cnt a + cnt b.
Proof. intros a b. induction a as [ | e a IH ]; [ reflexivity | ]. simpl. rewrite IH. lia. Qed.

Lemma raw_ap : forall st sr l R,
  raw l (ap_row st sr R) =
    map (fun e => (ap_typ st sr (fst e), ap_typ st sr (snd e))) (raw l R) ++
    match row_tail R with Some q => raw l (sr q) | None => nil end.
Proof.
  intros st sr l R. induction R as [ | r | l' T R IH | l' P T R IH ]; simpl; try reflexivity.
  - destruct (Nat.eqb l l'); simpl; rewrite IH; reflexivity.
  - destruct (Nat.eqb l l'); simpl; rewrite IH; reflexivity.
Qed.

(* Two rows with the same tail variable, the second without an entry of [l]
   and the first with a present one, are not [req] under any substitution. *)
Theorem leijen_tail : forall s R1 R2 r l P T es,
  row_tail R1 = Some r -> row_tail R2 = Some r ->
  raw l R1 = (P, T) :: es -> raw l R2 = nil ->
  teq (apT s P) typ_Unit -> ~ req (apR s R1) (apR s R2).
Proof.
  intros s R1 R2 r l P T es H1 H2 Hr1 Hr2 HP Hreq.
  pose proof (req_cnt _ _ Hreq l) as Hc. unfold apR in Hc.
  rewrite !raw_ap, H1, H2, Hr1, Hr2 in Hc. simpl in Hc.
  rewrite !cnt_app in Hc. simpl in Hc.
  assert (Hu : is_unit (ap_typ (sT s) (sR s) P) = true)
    by (change (is_unit (apT s P) = true); rewrite (teq_is_unit _ _ HP); reflexivity).
  rewrite Hu in Hc. lia.
Qed.

(* ---- the condition blocks unifiable pairs ---- *)

(* [r := {l0: Int}] and [c := {l0: Int}]. *)
Definition nested_sub (r c : atom) : sub :=
  Sub (fun b => if Atom.eq_dec b c then typ_Record (row_Ext 0 typ_Int row_Empty) else typ_Var b)
      (fun q => if Atom.eq_dec q r then row_Ext 0 typ_Int row_Empty else row_Var q).

Definition nested_R1 (r : atom) : row :=
  row_Ext 0 typ_Int (row_Ext 1 (typ_Record (row_Var r)) row_Empty).

Definition nested_R2 (r c : atom) : row := row_Ext 1 (typ_Var c) (row_Var r).

Lemma nested_sub_unifies : forall (r c : atom),
  req (apR (nested_sub r c) (nested_R1 r)) (apR (nested_sub r c) (nested_R2 r c)).
Proof.
  intros r c.
  unfold nested_R1, nested_R2, nested_sub, apR. simpl.
  destruct (Atom.eq_dec r r) as [_ | N]; [ | congruence ].
  destruct (Atom.eq_dec c c) as [_ | N]; [ | congruence ].
  apply req_sym. apply req_swap. discriminate.
Qed.

(* The guard [side_av] reads only the tail of the first row, so it lets the
   rewrite of the second row bind [r]. *)
Theorem side_passes_nested : forall (r c : atom) D n,
  rewrite_row 0 (side_av (nested_R1 r)) D (nested_R2 r c) n <> None.
Proof.
  intros r c D n. unfold nested_R1, nested_R2, side_av.
  cbn [rewrite_row row_tail Nat.eqb].
  destruct (AtomSetImpl.mem r {}) eqn:Hm;
    [ exfalso; apply AtomSetImpl.mem_2 in Hm; fsetdec | ].
  destruct (rk_lacks (drk D r) 0); discriminate.
Qed.

(* [p := Bool], [q := Bool] and [r := {}]. *)
Definition absent_sub (p q r : atom) : sub :=
  Sub (fun b => if Atom.eq_dec b p then typ_Bool else if Atom.eq_dec b q then typ_Bool else typ_Var b)
      (fun s => if Atom.eq_dec s r then row_Empty else row_Var s).

Theorem side_blocks_absent : forall (p q r : atom) D n f, p <> q ->
  req (apR (absent_sub p q r) (row_Maybe 0 (typ_Var p) typ_Int (row_Var r)))
      (apR (absent_sub p q r) (row_Maybe 1 (typ_Var q) typ_Int (row_Var r))) /\
  unify_rD f D (row_Maybe 0 (typ_Var p) typ_Int (row_Var r))
               (row_Maybe 1 (typ_Var q) typ_Int (row_Var r)) n = None.
Proof.
  intros p q r D n f Hpq. split.
  - unfold apR, absent_sub. simpl.
    destruct (Atom.eq_dec p p) as [_ | N]; [ | congruence ].
    destruct (Atom.eq_dec q p) as [E | _]; [ congruence | ].
    destruct (Atom.eq_dec q q) as [_ | N]; [ | congruence ].
    destruct (Atom.eq_dec r r) as [_ | N]; [ | congruence ].
    eapply req_trans; [ apply req_abs; reflexivity | ].
    apply req_sym. apply req_abs. reflexivity.
  - destruct f as [ | f ]; [ reflexivity | ].
    simpl. cbn [row_head rewrite_row]. unfold side_av. simpl.
    match goal with |- context [AtomSetImpl.mem r ?S] =>
      assert (Hm : AtomSetImpl.mem r S = true) by (apply AtomSetImpl.mem_1; fsetdec); rewrite Hm
    end. reflexivity.
Qed.

(* Two entries of one label that a unifier makes absent, with different field
   types: [l0^p: Int] against [l0^q: String] is unified by [p := Bool] and
   [q := Bool] (both rows are the empty row), and W refuses it, because it
   pairs the two entries and compares their field types.  An absent entry's
   field type carries no information ([row_cancel]), so statement A's
   hypothesis on the unifier covers this pair too. *)
Theorem field_blocks_absent : forall (p q : atom) D n f, p <> q ->
  req (apR (absent_sub p q p) (row_Maybe 0 (typ_Var p) typ_Int row_Empty))
      (apR (absent_sub p q p) (row_Maybe 0 (typ_Var q) typ_String row_Empty)) /\
  unify_rD f D (row_Maybe 0 (typ_Var p) typ_Int row_Empty)
               (row_Maybe 0 (typ_Var q) typ_String row_Empty) n = None.
Proof.
  intros p q D n f Hpq. split.
  - unfold apR, absent_sub. simpl.
    destruct (Atom.eq_dec p p) as [_ | N]; [ | congruence ].
    destruct (Atom.eq_dec q p) as [E | _]; [ congruence | ].
    destruct (Atom.eq_dec q q) as [_ | N]; [ | congruence ].
    eapply req_trans; [ apply req_abs; reflexivity | ].
    apply req_sym. apply req_abs. reflexivity.
  - destruct f as [ | f ]; [ reflexivity | ].
    cbn [unify_rD row_head rewrite_row Nat.eqb]. cbn iota beta.
    destruct f as [ | f ]; [ reflexivity | ].
    cbn [unify_tD apT ap_typ sT sid idt]. destruct (Atom.eq_dec p q); [ congruence | ].
    destruct (finer_b (D q) (D p)); cbn iota beta; try (destruct (finer_b (D p) (D q)); cbn iota beta);
      destruct f as [ | f ]; reflexivity.
Qed.

(* ---- the occurs checks block unifiable pairs the same way ---- *)

(* A variable against a row it ends, behind an absent entry:
   [r] against [{l0^p: Int, ...r}] is unified by [p := Bool], [r := {}]. *)
Theorem bind_row_blocks_absent_tail : forall (p r : atom) n f,
  req (apR (absent_sub p p r) (row_Var r))
      (apR (absent_sub p p r) (row_Maybe 0 (typ_Var p) typ_Int (row_Var r))) /\
  unify_rD f d_any (row_Var r) (row_Maybe 0 (typ_Var p) typ_Int (row_Var r)) n = None.
Proof.
  intros p r n f. split.
  - unfold apR, absent_sub. simpl.
    destruct (Atom.eq_dec p p) as [_ | N]; [ | congruence ].
    destruct (Atom.eq_dec r r) as [_ | N]; [ | congruence ].
    apply req_sym. eapply req_trans; [ apply req_abs; reflexivity | apply req_empty ].
  - destruct f as [ | f ]; [ reflexivity | ].
    cbn [unify_rD]. unfold bind_row, bind_row0. simpl.
    match goal with |- context [occR r ?R] =>
      assert (Ho : occR r R = true)
        by (unfold occR; apply Bool.orb_true_iff; left; apply AtomSetImpl.mem_1; simpl; fsetdec);
      rewrite Ho
    end. reflexivity.
Qed.

(* A variable against a record it occurs in behind an absent entry:
   [a] against [{l0^Bool: a}] is unified by [a := {}]. *)
Theorem bind_prop_blocks_absent : forall (a : atom) D n,
  teq (apT (sbT a (typ_Record row_Empty)) (typ_Var a))
      (apT (sbT a (typ_Record row_Empty)) (typ_Record (row_Maybe 0 typ_Bool (typ_Var a) row_Empty))) /\
  bind_prop D a (typ_Record (row_Maybe 0 typ_Bool (typ_Var a) row_Empty)) n = None.
Proof.
  intros a D n. split.
  - unfold apT, sbT. simpl. destruct (Atom.eq_dec a a) as [_ | N]; [ | congruence ].
    apply teq_rec. apply req_sym. apply req_abs. reflexivity.
  - unfold bind_prop, bind_prop0, occT.
    match goal with |- context [AtomSetImpl.mem a ?S] =>
      assert (Hm : AtomSetImpl.mem a S = true) by (apply AtomSetImpl.mem_1; simpl; fsetdec); rewrite Hm
    end. reflexivity.
Qed.

(* ---- the guard never blocks a unifiable pair whose front is present ---- *)

(* [rewrite_row] fails only at the guard: at the tail variable of a row that
   has no entry of the label. *)
Lemma rewrite_row_total : forall l av D R n,
  (raw l R = nil -> forall r, row_tail R = Some r -> AtomSetImpl.mem r av = false) ->
  rewrite_row l av D R n <> None.
Proof.
  intros l av D R. induction R as [ | r | l' T R IH | l' P T R IH ]; intros n H; cbn [rewrite_row].
  - discriminate.
  - destruct (AtomSetImpl.mem r av) eqn:Hm.
    + exfalso. rewrite (H eq_refl r eq_refl) in Hm. discriminate.
    + destruct (rk_lacks (drk D r) l); discriminate.
  - destruct (Nat.eqb l l') eqn:E; [ discriminate | ].
    destruct (rewrite_row l av D R n) as [[[[[[P0 T0] R3] s] D1] n1]|] eqn:E2; [ discriminate | ].
    exfalso. refine (IH n _ E2). intros Hn r' Hr'. apply H; [ simpl; rewrite E; exact Hn | exact Hr' ].
  - destruct (Nat.eqb l l') eqn:E; [ discriminate | ].
    destruct (rewrite_row l av D R n) as [[[[[[P0 T0] R3] s] D1] n1]|] eqn:E2; [ discriminate | ].
    exfalso. refine (IH n _ E2). intros Hn r' Hr'. apply H; [ simpl; rewrite E; exact Hn | exact Hr' ].
Qed.

(* A substitution that unifies two rows, the first of which starts with an
   entry it makes present, never meets the guard [side_av]: the second row has
   the label, or its tail is not the tail of the first (a common tail is
   [leijen_tail]).  A front entry with a presence variable that the
   substitution makes absent is the case this leaves out
   ([side_blocks_absent]). *)
Theorem side_guard_passes : forall S R1 R2 l P T R1' D n,
  row_head R1 = Some (l, P, T, R1') -> teq (apT S P) typ_Unit ->
  req (apR S R1) (apR S R2) -> rewrite_row l (side_av R1) D R2 n <> None.
Proof.
  intros S R1 R2 l P T R1' D n Hh HP Hreq. apply rewrite_row_total.
  intros Hnil r Hr. unfold side_av.
  destruct (row_tail R1) as [q|] eqn:Hq.
  - destruct (Atom.eq_dec q r) as [->|Hne].
    + exfalso.
      assert (Hraw : exists es, raw l R1 = (P, T) :: es).
      { destruct R1 as [ | | l0 T0 R0 | l0 P0 T0 R0 ]; simpl in Hh; try discriminate;
          inversion Hh; subst; simpl; rewrite Nat.eqb_refl; eexists; reflexivity. }
      destruct Hraw as [es Hraw].
      exact (leijen_tail S R1 R2 r l P T es Hq Hr Hraw Hnil HP Hreq).
    + apply AtomSetFacts.not_mem_iff. intros Hin. apply Hne. fsetdec.
  - apply AtomSetFacts.not_mem_iff. intros Hin. fsetdec.
Qed.
