(* Every recursive type the algorithm builds is guarded (phase 5, stage 4,
   part 4).

   A recursive type [mu B] is guarded when every mention of its own index in
   [B] sits under a record field and a function type ([guarded], GoatDefs.v),
   so unfolding it always exposes a constructor and two such types have a
   regular unfolding to compare.  [mg T] says that every [mu] inside [T] is
   guarded.  [mgb] decides it; the unifier's [bind_k] checks it of every type
   it binds, so a substitution it returns has [mg] images ([gsub]) whatever the
   types it was asked to equate.  The bound type's own mus are guarded because
   the type was [mg] when it came in, and the mu [bind_k] adds is guarded
   because [gdb_abs_guarded] says so. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Goat.GoatSubst.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatKnot.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

(* ---- the guard of a recursive type, decided ---- *)

(* [gdk] is [gd] as a boolean. *)
Fixpoint gdk (r f : bool) (k : nat) (T : typ) {struct T} : bool :=
  match T with
  | typ_Int | typ_Float | typ_Bool | typ_Unit | typ_String | typ_Var _ => true
  | typ_Arrow A B => gdk r true k A && gdk r true k B
  | typ_Record R => gdkr true f k R
  | typ_Bvar n => if Nat.eqb n k then r && f else true
  | typ_Mu B => gdk r f (S k) B
  | typ_Grp _ A => gdk true true k A
  end
with gdkr (r f : bool) (k : nat) (R : row) {struct R} : bool :=
  match R with
  | row_Empty | row_Var _ => true
  | row_Ext _ T R' => gdk r f k T && gdkr r f k R'
  | row_Maybe _ P T R' => gdk r f k P && (is_abs P || gdk r f k T) && gdkr r f k R'
  end.

Lemma gdk_gd_mut :
  (forall T r f k, gdk r f k T = true -> gd r f k T) /\
  (forall R r f k, gdkr r f k R = true -> gdr r f k R).
Proof.
  apply typ_row_mutind; cbn [gdk gdkr gd gdr]; intros;
    repeat match goal with
           | H : (_ && _) = true |- _ => apply Bool.andb_true_iff in H as [? ?]
           end;
    try exact I; try (split; eauto; fail); eauto.
  - subst. rewrite Nat.eqb_refl in H. apply Bool.andb_true_iff in H as [-> ->]. split; reflexivity.
  - split; [ eauto | split; [ | eauto ] ].
    match goal with Ho : (_ || _) = true |- _ =>
      apply Bool.orb_true_iff in Ho as [Hp | Hp]; [ left; exact Hp | right; eauto ] end.
Qed.

Lemma gdk_guarded : forall B, gdk false false 0 B = true -> guarded B.
Proof. intros. apply (proj1 gdk_gd_mut); assumption. Qed.

(* ---- every recursive type inside is guarded ---- *)

Fixpoint mg (T : typ) : Prop :=
  match T with
  | typ_Mu B => guarded B /\ mg B
  | typ_Arrow A B => mg A /\ mg B
  | typ_Record R => mgr R
  | typ_Grp _ A => mg A
  | _ => True
  end
with mgr (R : row) : Prop :=
  match R with
  | row_Ext _ T R' => mg T /\ mgr R'
  | row_Maybe _ P T R' => mg P /\ mg T /\ mgr R'
  | _ => True
  end.

Fixpoint mgb (T : typ) : bool :=
  match T with
  | typ_Mu B => gdk false false 0 B && mgb B
  | typ_Arrow A B => mgb A && mgb B
  | typ_Record R => mgbr R
  | typ_Grp _ A => mgb A
  | _ => true
  end
with mgbr (R : row) : bool :=
  match R with
  | row_Ext _ T R' => mgb T && mgbr R'
  | row_Maybe _ P T R' => mgb P && mgb T && mgbr R'
  | _ => true
  end.

Lemma mgb_mg_mut :
  (forall T, mgb T = true -> mg T) /\ (forall R, mgbr R = true -> mgr R).
Proof.
  apply typ_row_mutind; cbn [mgb mgbr mg mgr]; intros;
    repeat match goal with
           | H : (_ && _) = true |- _ => apply Bool.andb_true_iff in H as [? ?]
           end;
    try exact I; eauto.
  - split; [ apply gdk_guarded; assumption | eauto ].
  - repeat split; eauto.
Qed.

Lemma mgb_mg : forall T, mgb T = true -> mg T.
Proof. intros. apply (proj1 mgb_mg_mut); assumption. Qed.

Lemma mgbr_mgr : forall R, mgbr R = true -> mgr R.
Proof. intros. apply (proj2 mgb_mg_mut); assumption. Qed.

(* ---- substitution keeps it ---- *)

Lemma mg_ap_mut : forall st sr, lc_sub st sr ->
  (forall a, mg (st a)) -> (forall r, mgr (sr r)) ->
  (forall T, mg T -> mg (ap_typ st sr T)) /\
  (forall R, mgr R -> mgr (ap_row st sr R)).
Proof.
  intros st sr Hlc Ht Hr.
  apply typ_row_mutind; cbn [mg mgr ap_typ ap_row]; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try exact I; try (split; auto; fail); auto.
  all: try (split; [ apply guarded_ap; assumption | auto ]).
  all: try (repeat split; auto).
Qed.

(* ---- abstracting an atom keeps it ---- *)

Lemma gd_abs_mut : forall x,
  (forall T r f j k, j <> k -> gd r f j T -> gd r f j (abs_typ x k T)) /\
  (forall R r f j k, j <> k -> gdr r f j R -> gdr r f j (abs_row x k R)).
Proof.
  intros x. apply typ_row_mutind; cbn [gd gdr abs_typ abs_row]; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try exact I; try (split; eauto; fail); eauto.
  all: try (destruct (Atom.eq_dec a x); cbn [gd]; [ | exact I ];
            intros E; exfalso; match goal with H : _ <> _ |- _ => apply H; symmetry; exact E end).
  all: try (repeat split; eauto; rewrite abs_is_abs;
            match goal with H : _ \/ _ |- _ => destruct H as [Ha | Hb] end;
            [ left; exact Ha | right; eauto ]).
Qed.

Lemma mg_abs_mut : forall x,
  (forall T k, mg T -> mg (abs_typ x k T)) /\
  (forall R k, mgr R -> mgr (abs_row x k R)).
Proof.
  intros x. apply typ_row_mutind; cbn [mg mgr abs_typ abs_row]; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try exact I; try (split; eauto; fail); eauto.
  all: try (destruct (Atom.eq_dec a x); exact I).
  all: try (split; [ | eauto ];
            unfold guarded; apply (proj1 (gd_abs_mut x)); [ lia | assumption ]).
  all: try (repeat split; eauto).
Qed.

Lemma mg_knot : forall x T, lct 0 T -> mg T -> gdb false false x T = true -> mg (knot x T).
Proof.
  intros x T Hlc Hmg Hg. unfold knot. cbn [mg]. split.
  - apply gdb_abs_guarded; assumption.
  - apply (proj1 (mg_abs_mut x)); assumption.
Qed.

(* ---- substitutions whose images keep it ---- *)

Definition gsub (s : sub) : Prop :=
  lc_sub (sT s) (sR s) /\ (forall a, mg (sT s a)) /\ (forall r, mgr (sR s r)).

Lemma mg_apT : forall s T, gsub s -> mg T -> mg (apT s T).
Proof. intros s T (Hl & Ht & Hr) H. exact (proj1 (mg_ap_mut _ _ Hl Ht Hr) T H). Qed.

Lemma mg_apR : forall s R, gsub s -> mgr R -> mgr (apR s R).
Proof. intros s R (Hl & Ht & Hr) H. exact (proj2 (mg_ap_mut _ _ Hl Ht Hr) R H). Qed.

Lemma gs_id : gsub sid.
Proof.
  split; [ split; [ intros a; exact I | intros r; exact I ] | split; intros; exact I ].
Qed.

Lemma gs_comp : forall s2 s1, gsub s2 -> gsub s1 -> gsub (scomp s2 s1).
Proof.
  intros s2 s1 H2 H1. pose proof H2 as (Hl2 & _ & _). pose proof H1 as (Hl1 & _ & _).
  split; [ | split ]; cbn [scomp sT sR tcomp rcomp].
  - split; intros x.
    + apply ap_lc; [ exact Hl2 | exact (proj1 Hl1 x) ].
    + apply ap_lcr; [ exact Hl2 | exact (proj2 Hl1 x) ].
  - intros a. apply mg_apT; [ exact H2 | exact (proj1 (proj2 H1) a) ].
  - intros r. apply mg_apR; [ exact H2 | exact (proj2 (proj2 H1) r) ].
Qed.

Lemma gs_sbT : forall a T, lct 0 T -> mg T -> gsub (sbT a T).
Proof.
  intros a T Hl Hm. split; [ | split ]; cbn [sbT sT sR].
  - split; [ intros b; destruct (Atom.eq_dec b a); [ exact Hl | exact I ] | intros r; exact I ].
  - intros b. destruct (Atom.eq_dec b a); [ exact Hm | exact I ].
  - intros r. exact I.
Qed.

Lemma gs_sbR : forall r R, lcr 0 R -> mgr R -> gsub (sbR r R).
Proof.
  intros r R Hl Hm. split; [ | split ]; cbn [sbR sT sR].
  - split; [ intros b; exact I | intros q; destruct (Atom.eq_dec q r); [ exact Hl | exact I ] ].
  - intros b. exact I.
  - intros q. destruct (Atom.eq_dec q r); [ exact Hm | exact I ].
Qed.
