(* Completeness of algorithm W, stage 7.7: every declared group spells its
   parameters, so [spn] holds (docs/design/phase7-proof-plan.md).

   The unifier's completeness on a tag group ([GoatCompleteBind.v]) asks that
   the payload [spine Ts] of [typ_Grp w] have arrows ending in [Unit] and that
   every slot [6 + j] be used by some tag of [w] ([spn]).  goat has no syntax
   for an unused parameter: a group's parameters are the [_] slots written in
   its tags' payloads, numbered in order from zero across the whole
   declaration ([type_slots], GoatDen.v).  So the slots a declaration uses are
   [6 .. 6 + m - 1] for the [m] parameters it declares, and [nparams w] is [m].
   This file proves that of every group [decl_entries] reads out of a
   declaration, which is the table the denotation and the printer use. *)

From Stdlib Require Import List.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatInfer.
Require Import Goat.GoatCompleteBind.
From Stdlib Require Import Lia.

(* A group whose declaration uses every parameter it counts. *)
Definition gwf (w : gdecl) : Prop :=
  forall i, i < nparams w -> exists cs, In cs (gtags w) /\ In (6 + i) cs.

Lemma spn_spine : forall w Ts j,
  (forall i, i < length Ts -> exists cs, In cs (gtags w) /\ In (6 + j + i) cs) ->
  spn w j (spine Ts).
Proof.
  intros w Ts. induction Ts as [|T Ts IH]; intros j H; cbn [spine spn]; [ exact I | ].
  split.
  - destruct (H 0 (Nat.lt_0_succ _)) as (cs & Hc & Hi). exists cs. split; [ exact Hc | ].
    replace (6 + j) with (6 + j + 0) by lia. exact Hi.
  - apply IH. intros i Hi. destruct (H (Datatypes.S i) ltac:(simpl; lia)) as (cs & Hc & Hin).
    exists cs. split; [ exact Hc | ]. replace (6 + Datatypes.S j + i) with (6 + j + Datatypes.S i) by lia. exact Hin.
Qed.

(* A well-formed group's parameter spine spells its parameters. *)
Theorem spn_gwf : forall w Ts, gwf w -> length Ts = nparams w -> spn w 0 (spine Ts).
Proof.
  intros w Ts Hw Hl. apply spn_spine. intros i Hi. rewrite Hl in Hi. exact (Hw i Hi).
Qed.

(* ---- the slots a declaration numbers ---- *)

Lemma slot_of_lt6 : forall g n, slot_of g n < 6.
Proof.
  intros g n. unfold slot_of.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Ltac slot_default H := inversion H; subst; left; split; [ lia | reflexivity ].

Lemma type_slot_cases : forall g j t c j1, type_slot g j t = (c, j1) ->
  (c < 6 /\ j1 = j) \/ (c = 6 + j /\ j1 = Datatypes.S j).
Proof.
  intros g j t c j1 H. unfold type_slot in H.
  destruct t as [k | r cs]; [ slot_default H | ].
  destruct r; try (slot_default H).
  - destruct cs as [|t1 [|t2 cs2]]; try (slot_default H);
      destruct t1 as [k1 | r1 cs1]; try (slot_default H);
      destruct k1 as [n | ? | ? | | ?]; try (slot_default H);
      inversion H; subst; left; split; [ apply slot_of_lt6 | reflexivity ].
  - inversion H; subst. right. split; reflexivity.
Qed.

(* What a run of [type_slots] from [j] to [j'] produces: the slots it makes are
   the old codes below 6 and the parameters [j .. j' - 1], each once at least. *)
Lemma type_slots_facts : forall g ts j cs j', type_slots g j ts = (cs, j') ->
  j <= j' /\ (forall c, In c cs -> c < 6 \/ (6 <= c /\ j <= c - 6 /\ c - 6 < j')) /\
  (forall i, j <= i -> i < j' -> In (6 + i) cs).
Proof.
  intros g ts. induction ts as [|t ts IH]; intros j cs j' H; cbn [type_slots] in H.
  - inversion H; subst. refine (conj (le_n _) (conj _ _)); [ intros c [] | intros i H1 H2; lia ].
  - destruct (type_slot g j t) as [c j1] eqn:Et.
    destruct (type_slots g j1 ts) as [cs1 j2] eqn:Ets. inversion H; subst; clear H.
    destruct (IH _ _ _ Ets) as (Hl & Hc & Hu).
    destruct (type_slot_cases _ _ _ _ _ Et) as [[Hlt ->] | [-> ->]].
    + refine (conj Hl (conj _ _)).
      * intros c' [<-|Hin]; [ left; exact Hlt | exact (Hc c' Hin) ].
      * intros i H1 H2. right. exact (Hu i H1 H2).
    + refine (conj (Nat.le_trans _ _ _ (Nat.le_succ_diag_r j) Hl) (conj _ _)).
      * intros c' [<-|Hin].
        -- right. refine (conj _ (conj _ _)); lia.
        -- destruct (Hc c' Hin) as [H1|(H1 & H2 & H3)]; [ left; exact H1 | right; refine (conj H1 (conj _ H3)); lia ].
      * intros i H1 H2. destruct (Nat.eq_dec i j) as [->|Hne].
        -- left. reflexivity.
        -- right. apply Hu; lia.
Qed.

Lemma cases_slots_facts : forall g cases j,
  exists j', j <= j' /\
    (forall cs, In cs (List.map snd (cases_slots g j cases)) -> forall c, In c cs ->
       c < 6 \/ (6 <= c /\ j <= c - 6 /\ c - 6 < j')) /\
    (forall i, j <= i -> i < j' -> exists cs, In cs (List.map snd (cases_slots g j cases)) /\ In (6 + i) cs).
Proof.
  intros g cases. induction cases as [|c rest IH]; intros j; cbn [cases_slots List.map].
  - exists j. refine (conj (le_n _) (conj _ _)); [ intros cs [] | intros i H1 H2; lia ].
  - destruct (type_slots g j (List.filter is_type_node c)) as [cs j1] eqn:Ets.
    destruct (type_slots_facts _ _ _ _ _ Ets) as (Hl & Hc & Hu).
    destruct (IH j1) as (j' & Hl' & Hc' & Hu').
    exists j'. refine (conj (Nat.le_trans _ _ _ Hl Hl') (conj _ _)).
    + intros cs0 [<-|Hin] c0 Hc0.
      * destruct (Hc c0 Hc0) as [H1|(H1 & H2 & H3)]; [ left; exact H1 | right ].
        refine (conj H1 (conj H2 _)); lia.
      * destruct (Hc' cs0 Hin c0 Hc0) as [H1|(H1 & H2 & H3)]; [ left; exact H1 | right ].
        refine (conj H1 (conj _ H3)); lia.
    + intros i H1 H2. destruct (Nat.lt_ge_cases i j1) as [Hlt|Hge].
      * exists cs. split; [ left; reflexivity | exact (Hu i H1 Hlt) ].
      * destruct (Hu' i Hge H2) as (cs0 & Hin & Hi). exists cs0. split; [ right; exact Hin | exact Hi ].
Qed.

Lemma nparams_le : forall w m,
  (forall cs, In cs (gtags w) -> forall c, In c cs -> c - 5 <= m) -> nparams w <= m.
Proof.
  intros w m H. unfold nparams. generalize dependent (gtags w). intros L. induction L as [|cs L IH]; intros H.
  - simpl. lia.
  - cbn [fold_right]. assert (Hr : fold_right (fun cs a => fold_right (fun c b => Nat.max (c - 5) b) a cs) 0 L <= m)
      by (apply IH; intros cs' Hin; apply H; right; exact Hin).
    revert Hr. generalize (fold_right (fun cs a => fold_right (fun c b => Nat.max (c - 5) b) a cs) 0 L) as a. intros a Ha.
    assert (Hcs : forall c, In c cs -> c - 5 <= m) by (intros c Hc; exact (H cs (or_introl eq_refl) c Hc)).
    clear H IH. induction cs as [|c cs IH]; [ exact Ha | ]. cbn [fold_right].
    assert (Hc : c - 5 <= m) by (apply Hcs; left; reflexivity).
    assert (Hr : fold_right (fun c b => Nat.max (c - 5) b) a cs <= m)
      by (apply IH; intros c' Hc'; apply Hcs; right; exact Hc').
    lia.
Qed.

(* Every group a declaration reads out spells its parameters. *)
Theorem declared_gwf : forall d x w tg, In (x, (w, tg)) (decl_entries d) -> gwf w.
Proof.
  intros d x w tg H. unfold decl_entries in H. destruct d as [k | r cs]; [ destruct H | ].
  destruct r; try (destruct H; fail).
  cbn [decl_entries] in H.
  set (cases := cases_slots (decl_group cs) 0 (decl_cases cs)) in *.
  apply List.in_map_iff in H. destruct H as [ic [Heq _]]. injection Heq as _ <- _.
  destruct (cases_slots_facts (decl_group cs) (decl_cases cs) 0) as (j' & _ & Hc & Hu).
  fold cases in Hc, Hu.
  intros i Hi. cbn [gtags snd] in *.
  assert (Hle : nparams (decl_name cs cases, List.map snd cases) <= j').
  { apply nparams_le. intros cs0 Hin c Hc0. cbn [gtags snd] in Hin.
    destruct (Hc cs0 Hin c Hc0) as [H1|(H1 & H2 & H3)]; lia. }
  destruct (Hu i (Nat.le_0_l i) ltac:(lia)) as (cs0 & Hin & Hci).
  exists cs0. split; [ exact Hin | exact Hci ].
Qed.

(* So a group's parameter spine, as the algorithm builds it, spells them. *)
Theorem spn_declared : forall d x w tg Ts,
  In (x, (w, tg)) (decl_entries d) -> length Ts = nparams w -> spn w 0 (spine Ts).
Proof. intros d x w tg Ts H Hl. exact (spn_gwf w Ts (declared_gwf d x w tg H) Hl). Qed.
