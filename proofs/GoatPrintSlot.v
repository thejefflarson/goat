(* The slots of a match arm. The denotation of an arm [Tag(x0, ..., xm) then
   body] binds the payload to a fresh variable, reads each slot into a name, and
   closes the names and the payload again. The arm's term has the same shape as
   bindings of the slots of its payload index, over the body. *)

From Stdlib Require Import String List Arith Lia.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatDen.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintArm.
Require Import Goat.GoatPrintInst.
Open Scope string_scope.
Open Scope list_scope.

Local Hint Extern 1 (_ `notin` _) => fsetdec : core.

Local Ltac cl_simp :=
  cbn [close_exp_rec close_fields_rec close_arms_rec fv_exp fv_fields fv_arms] in *.

Local Ltac split_ifs :=
  repeat match goal with
  | |- context [if ?c then _ else _] => destruct c
  end.

(* Closing a variable that does not occur changes nothing. *)
Lemma close_notin :
  (forall e k x, x `notin` fv_exp e -> close_exp_rec k x e = e) /\
  (forall fs k x, x `notin` fv_fields fs -> close_fields_rec k x fs = fs) /\
  (forall ars k x, x `notin` fv_arms ars -> close_arms_rec k x ars = ars).
Proof.
  apply exp_fields_mutind; intros; cl_simp; try reflexivity; try (f_equal; eauto; fail).
  split_ifs; [ exfalso; fsetdec | reflexivity ].
Qed.

(* Closing two different variables, each at its own level, in either order. *)
Lemma close_comm :
  (forall e k k' x y, x <> y ->
     close_exp_rec k x (close_exp_rec k' y e) = close_exp_rec k' y (close_exp_rec k x e)) /\
  (forall fs k k' x y, x <> y ->
     close_fields_rec k x (close_fields_rec k' y fs)
     = close_fields_rec k' y (close_fields_rec k x fs)) /\
  (forall ars k k' x y, x <> y ->
     close_arms_rec k x (close_arms_rec k' y ars)
     = close_arms_rec k' y (close_arms_rec k x ars)).
Proof.
  apply exp_fields_mutind; intros; cl_simp; try reflexivity; try (f_equal; eauto; fail).
  split_ifs; cl_simp; split_ifs; subst; try reflexivity; try congruence.
Qed.

(* ---- the arm's term ---- *)

(* The names an arm gives its slots, from depth [q]. *)
Fixpoint arm_vars (q m : nat) {struct m} : list string :=
  match m with
  | 0 => []
  | S m' => nm q :: arm_vars (S q) m'
  end.

(* [m] bindings of the slots of the payload, from slot [j], over [Z]. *)
Fixpoint wrap_slots (m j : nat) (Z : exp) {struct m} : exp :=
  match m with
  | 0 => Z
  | S m' => e_let (e_proj (e_fvar_b j) j) (wrap_slots m' (S j) Z)
  end.

(* Closing the names of the slots in [B]: the last slot's name at level 0, each
   earlier one at the level its binding adds. *)
Fixpoint clo (var_of : string -> termvar) (q m : nat) (B : exp) {struct m} : exp :=
  match m with
  | 0 => B
  | S m' => close_exp_rec m' (var_of (nm q)) (clo var_of (S q) m' B)
  end.

Lemma close_wrap : forall m j k x Z,
  close_exp_rec k x (wrap_slots m j Z) = wrap_slots m j (close_exp_rec (k + m) x Z).
Proof.
  induction m as [| m IH]; intros j k x Z.
  - cbn [wrap_slots]. rewrite Nat.add_0_r. reflexivity.
  - cbn [wrap_slots close_exp_rec]. rewrite IH. replace (S k + m) with (k + S m) by lia.
    reflexivity.
Qed.

Lemma slot_close : forall var_of m q j B s,
  s `notin` fv_exp B ->
  (forall t, t < m -> s <> var_of (nm (q + t))) ->
  close_exp_rec j s (slot_lets var_of s j (arm_vars q m) B)
  = wrap_slots m j (clo var_of q m B).
Proof.
  intros var_of. induction m as [| m IH]; intros q j B s HB Hs.
  - cbn [slot_lets arm_vars wrap_slots clo]. exact (proj1 close_notin B j s HB).
  - cbn [slot_lets arm_vars wrap_slots clo]. unfold close_exp.
    cbn [close_exp_rec].
    f_equal.
    + split_ifs; try reflexivity; congruence.
    + rewrite (proj1 close_comm _ (S j) 0 s (var_of (nm q))).
      * rewrite (IH (S q) (S j) B s HB).
        -- rewrite close_wrap. cbn [Nat.add]. reflexivity.
        -- intros t Ht. replace (S q + t) with (q + S t) by lia. apply Hs. lia.
      * intros Heq. specialize (Hs 0 (Nat.lt_0_succ m)). rewrite Nat.add_0_r in Hs. exact (Hs Heq).
Qed.

Lemma inst_wrap : forall var_of m j b G P,
  arm_chain m j b ->
  inst_rec var_of G (S j) P b
  = wrap_slots m j (inst_rec var_of G (S j + m) P (arm_inner m b)).
Proof.
  intros var_of. induction m as [| m IH]; intros j b G P Hc.
  - cbn [wrap_slots arm_inner]. rewrite Nat.add_0_r. reflexivity.
  - destruct b; try (cbn in Hc; contradiction).
    destruct b1; try (cbn in Hc; contradiction).
    destruct b1; try (cbn in Hc; contradiction).
    cbn in Hc. destruct Hc as (-> & -> & Hc).
    cbn [inst_rec wrap_slots arm_inner].
    assert (Hlt : Nat.ltb j (S j) = true) by (apply Nat.ltb_lt; lia).
    rewrite Hlt. rewrite (IH (S j) b2 G P Hc). replace (S j + S m) with (S (S j) + m) by lia.
    reflexivity.
Qed.

(* A bound index that does not occur is not read as a name either way. *)
Lemma inst_unused : forall var_of,
  (forall e G k D, unused k e -> inst_rec var_of G k (S D) e = inst_rec var_of G (S k) D e) /\
  (forall fs G k D, unused_fields k fs ->
     inst_fields var_of G k (S D) fs = inst_fields var_of G (S k) D fs) /\
  (forall ars G k D, unused_arms k ars ->
     inst_arms var_of G k (S D) ars = inst_arms var_of G (S k) D ars).
Proof.
  intros var_of. apply exp_fields_mutind.
  12: { intros a IH l G k D H.
        destruct (bvar_or_not a) as [[i ->] | Hnb].
        - cbn [unused] in H. cbn [inst_rec].
          destruct (Nat.ltb i k) eqn:E1; destruct (Nat.ltb i (S k)) eqn:E2; try reflexivity.
          + apply Nat.ltb_lt in E1. apply Nat.ltb_ge in E2. lia.
          + apply Nat.ltb_ge in E1. apply Nat.ltb_lt in E2. exfalso. apply H. lia.
          + replace (S k + D - 1 - i) with (k + S D - 1 - i) by lia. reflexivity.
        - rewrite (inst_proj_other var_of G k (S D) a l Hnb),
            (inst_proj_other var_of G (S k) D a l Hnb).
          cbn [unused] in H. rewrite (IH G k D H). reflexivity. }
  1: { intros i G k D H. cbn [unused] in H. cbn [inst_rec].
       destruct (Nat.ltb i k) eqn:E1; destruct (Nat.ltb i (S k)) eqn:E2; try reflexivity.
       - apply Nat.ltb_lt in E1. apply Nat.ltb_ge in E2. lia.
       - apply Nat.ltb_ge in E1. apply Nat.ltb_lt in E2. exfalso. apply H. lia.
       - replace (S k + D - 1 - i) with (k + S D - 1 - i) by lia. reflexivity. }
  all: intros; cbn [unused unused_fields unused_arms] in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    cbn [inst_rec inst_fields inst_arms]; try reflexivity.
  all: try (f_equal; eauto; fail).
  (* a group enters the scope at the depth its binder reads as a name *)
  all: replace (k + S D) with (S k + D) by lia; f_equal; eauto.
Qed.

(* Reading the names of the slots back into bindings. *)
Lemma clo_inst : forall var_of, names_distinct var_of ->
  forall m q G X,
  (forall D, q <= D -> grp_size G D = None) ->
  scoped G (q + m) X ->
  clo var_of q m (inst_rec var_of G 0 (q + m) X) = inst_rec var_of G m q X.
Proof.
  intros var_of Hd. induction m as [| m IH]; intros q G X HG Hs.
  - cbn [clo]. rewrite Nat.add_0_r. reflexivity.
  - cbn [clo]. replace (q + S m) with (S q + m) by lia.
    rewrite (IH (S q) G X) by (try lia; first [ intros D HD; apply HG; lia | replace (S q + m) with (q + S m) by lia; exact Hs ]).
    exact (proj1 (close_inst var_of Hd q) X G m (HG q (le_n q))
             (eq_ind_r (fun n => scoped G n X) (eq_ind _ (fun n => scoped G n X) Hs _ (ltac:(lia) : q + S m = m + S q)) eq_refl)).
Qed.

Lemma in_arm_vars : forall m q t, t < m -> List.In (nm (q + t)) (arm_vars q m).
Proof.
  induction m as [| m IH]; intros q t Ht; [ lia | ].
  cbn [arm_vars]. destruct t as [| t].
  - left. rewrite Nat.add_0_r. reflexivity.
  - right. replace (q + S t) with (S q + t) by lia. apply IH. lia.
Qed.

(* The arm the denotation builds, from the arm's slots and its body read at the
   depth they reach, is the arm's term with the enclosing binders read as names. *)
Lemma arm_close : forall var_of, names_distinct var_of ->
  forall m G P b s,
  (forall D, P <= D -> grp_size G D = None) ->
  arm_chain m 0 b -> scoped G (S P) b -> unused m (arm_inner m b) ->
  s `notin` fv_exp (inst_rec var_of G 0 (S P + m) (arm_inner m b)) ->
  (forall t, t < m -> s <> var_of (nm (S P + t))) ->
  close_exp s (slot_lets var_of s 0 (arm_vars (S P) m)
                 (inst_rec var_of G 0 (S P + m) (arm_inner m b)))
  = inst_rec var_of G 1 P b.
Proof.
  intros var_of Hd m G P b s HG Hch Hs Hun Hnot Hs'.
  unfold close_exp. rewrite (slot_close var_of m (S P) 0 _ s Hnot Hs').
  rewrite (clo_inst var_of Hd m (S P) G (arm_inner m b));
    [ | intros D HD; apply HG; lia | exact (scoped_inner m 0 b G (S P) Hch Hs) ].
  rewrite (proj1 (inst_unused var_of) (arm_inner m b) G m P Hun).
  rewrite (inst_wrap var_of m 0 b G P Hch). reflexivity.
Qed.
