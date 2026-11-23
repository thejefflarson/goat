(* A decision procedure for the bounded-unrolling equality (phase 5, stage 4,
   part 2; docs/design/phase5-proof-plan.md, Q2).

   [unroll_eqb n T T'] searches for a derivation of [unroll_eq n T T']:
   types are compared by shape, and a mu that meets a different head on the
   other side is unrolled, spending one unit of the budget.  The budget falls
   at every unrolling, so the search ends without the checker's assumed-pairs
   set.  That set makes a revisited pair succeed, which equates two regular
   trees by a derivation of unbounded depth; [unroll_eq] has only finite
   derivations, so it cannot be what the relation states.

   The procedure is sound ([unroll_eqb_sound]).  It is not complete:
   [unroll_eq] may route an equality through a middle type ([UE_trans]) that
   the search never builds, and it compares rows by syntax where [req] also
   reorders them. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatMu.
Require Import Goat.GoatElab.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

(* ---- syntactic equality ---- *)

Definition gdecl_eqb (w w' : gdecl) : bool :=
  if list_eq_dec (list_eq_dec Nat.eq_dec) w w' then true else false.

Fixpoint typ_eqb (T T' : typ) {struct T} : bool :=
  match T, T' with
  | typ_Int, typ_Int | typ_Float, typ_Float | typ_Bool, typ_Bool
  | typ_Unit, typ_Unit | typ_String, typ_String => true
  | typ_Arrow A B, typ_Arrow A' B' => typ_eqb A A' && typ_eqb B B'
  | typ_Record R, typ_Record R' => row_eqb R R'
  | typ_Var a, typ_Var a' => if Atom.eq_dec a a' then true else false
  | typ_Bvar i, typ_Bvar j => Nat.eqb i j
  | typ_Mu B, typ_Mu B' => typ_eqb B B'
  | typ_Grp w A, typ_Grp w' A' => gdecl_eqb w w' && typ_eqb A A'
  | _, _ => false
  end
with row_eqb (R R' : row) {struct R} : bool :=
  match R, R' with
  | row_Empty, row_Empty => true
  | row_Var r, row_Var r' => if Atom.eq_dec r r' then true else false
  | row_Ext l T R1, row_Ext l' T' R1' => Nat.eqb l l' && typ_eqb T T' && row_eqb R1 R1'
  | row_Maybe l P T R1, row_Maybe l' P' T' R1' =>
      Nat.eqb l l' && typ_eqb P P' && typ_eqb T T' && row_eqb R1 R1'
  | _, _ => false
  end.

Lemma gdecl_eqb_eq : forall w w', gdecl_eqb w w' = true -> w = w'.
Proof.
  unfold gdecl_eqb. intros w w'. destruct (list_eq_dec _ w w'); [ auto | discriminate ].
Qed.

Lemma typ_eqb_eq_mut :
  (forall T T', typ_eqb T T' = true -> T = T') /\
  (forall R R', row_eqb R R' = true -> R = R').
Proof.
  apply typ_row_mutind.
  - intros T'; destruct T'; cbn; intros; try discriminate; reflexivity.
  - intros T'; destruct T'; cbn; intros; try discriminate; reflexivity.
  - intros T'; destruct T'; cbn; intros; try discriminate; reflexivity.
  - intros T'; destruct T'; cbn; intros; try discriminate; reflexivity.
  - intros T'; destruct T'; cbn; intros; try discriminate; reflexivity.
  - intros A IHA B IHB T'; destruct T'; cbn; intros H; try discriminate.
    apply andb_true_iff in H as [H1 H2]. rewrite (IHA _ H1), (IHB _ H2). reflexivity.
  - intros R IHR T'; destruct T'; cbn; intros H; try discriminate. rewrite (IHR _ H). reflexivity.
  - intros a T'; destruct T'; cbn; intros H; try discriminate.
    destruct (Atom.eq_dec a a0); [ subst; reflexivity | discriminate ].
  - intros i T'; destruct T'; cbn; intros H; try discriminate.
    apply Nat.eqb_eq in H. subst. reflexivity.
  - intros B IHB T'; destruct T'; cbn; intros H; try discriminate. rewrite (IHB _ H). reflexivity.
  - intros w A IHA T'; destruct T'; cbn; intros H; try discriminate.
    apply andb_true_iff in H as [H1 H2].
    rewrite (gdecl_eqb_eq _ _ H1), (IHA _ H2). reflexivity.
  - intros R'; destruct R'; cbn; intros; try discriminate; reflexivity.
  - intros r R'; destruct R'; cbn; intros H; try discriminate.
    destruct (Atom.eq_dec r r0); [ subst; reflexivity | discriminate ].
  - intros l T IHT R1 IHR R'; destruct R'; cbn; intros H; try discriminate.
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Nat.eqb_eq in H1. subst. rewrite (IHT _ H2), (IHR _ H3). reflexivity.
  - intros l P IHP T IHT R1 IHR R'; destruct R'; cbn; intros H; try discriminate.
    apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3].
    apply andb_true_iff in H as [H1 H2].
    apply Nat.eqb_eq in H1. subst. rewrite (IHP _ H2), (IHT _ H3), (IHR _ H4). reflexivity.
Qed.

Lemma typ_eqb_teq : forall T T', typ_eqb T T' = true -> teq T T'.
Proof. intros T T' H. rewrite <- (proj1 typ_eqb_eq_mut _ _ H). apply teq_refl. Qed.

Lemma row_eqb_req : forall R R', row_eqb R R' = true -> req R R'.
Proof. intros R R' H. rewrite <- (proj2 typ_eqb_eq_mut _ _ H). apply req_refl. Qed.

(* ---- the search ---- *)

(* [rec] decides what is left after one unrolling; it is [unroll_eqb] at the
   next smaller budget, and answers [false] when none is left. *)
Fixpoint unroll_go (rec : typ -> typ -> bool) (T T' : typ) {struct T} : bool :=
  typ_eqb T T'
  || match T, T' with
     | typ_Arrow A B, typ_Arrow A' B' => unroll_go rec A A' && unroll_go rec B B'
     | typ_Record R, typ_Record R' => unroll_go_row rec R R'
     | typ_Grp w A, typ_Grp w' A' => gdecl_eqb w w' && unroll_go rec A A'
     | _, _ => false
     end
  || match T with typ_Mu B => rec (open_typ 0 T B) T' | _ => false end
  || match T' with typ_Mu B' => rec T (open_typ 0 T' B') | _ => false end
with unroll_go_row (rec : typ -> typ -> bool) (R R' : row) {struct R} : bool :=
  row_eqb R R'
  || match R, R' with
     | row_Ext l T R1, row_Ext l' T' R1' =>
         Nat.eqb l l' && unroll_go rec T T' && unroll_go_row rec R1 R1'
     | row_Maybe l P T R1, row_Maybe l' P' T' R1' =>
         Nat.eqb l l' && unroll_go rec P P' && unroll_go rec T T' && unroll_go_row rec R1 R1'
     | _, _ => false
     end.

Fixpoint unroll_eqb (n : nat) (T T' : typ) {struct n} : bool :=
  match n with
  | O => unroll_go (fun _ _ => false) T T'
  | S m => unroll_go (unroll_eqb m) T T'
  end.

(* What [rec] may claim: equality at a budget that leaves room for the
   unrolling spent to reach it. *)
Definition rec_sound (n : nat) (rec : typ -> typ -> bool) : Prop :=
  forall T T', rec T T' = true -> exists m, S m <= n /\ unroll_eq m T T'.

Lemma unroll_go_sound : forall n rec, rec_sound n rec ->
  (forall T T', unroll_go rec T T' = true -> unroll_eq n T T') /\
  (forall R R', unroll_go_row rec R R' = true -> unroll_row n R R').
Proof.
  intros n rec Hrec.
  assert (Hmu_l : forall B T', rec (open_typ 0 (typ_Mu B) B) T' = true ->
            unroll_eq n (typ_Mu B) T').
  { intros B T' H. destruct (Hrec _ _ H) as [m [Hle Hm]].
    destruct n as [ | n']; [ lia | ].
    apply (unroll_mono (S m) (S n')); [ lia | ].
    apply (UE_trans 1 m _ (open_typ 0 (typ_Mu B) B)); [ apply (UE_unfold 0) | exact Hm ]. }
  assert (Hmu_r : forall B T, rec T (open_typ 0 (typ_Mu B) B) = true ->
            unroll_eq n T (typ_Mu B)).
  { intros B T H. destruct (Hrec _ _ H) as [m [Hle Hm]].
    destruct n as [ | n']; [ lia | ].
    apply (unroll_mono (m + 1) (S n')); [ lia | ].
    apply (UE_trans m 1 _ (open_typ 0 (typ_Mu B) B)); [ exact Hm | apply (UE_fold 0) ]. }
  assert (orb4 : forall a b c d : bool, a || b || c || d = true ->
            a = true \/ b = true \/ c = true \/ d = true).
  { intros a b c d H. rewrite !orb_true_iff in H. tauto. }
  assert (orb2 : forall a b : bool, a || b = true -> a = true \/ b = true).
  { intros a b H. apply orb_true_iff. exact H. }
  apply typ_row_mutind.
  - intros T' H. cbn [unroll_go] in H. apply orb4 in H as [H | [H | [H | H]]].
    + apply UE_teq, typ_eqb_teq. exact H.
    + destruct T'; cbn in H; discriminate.
    + cbn in H. discriminate.
    + destruct T'; cbn in H; try discriminate. apply Hmu_r. exact H.
  - intros T' H. cbn [unroll_go] in H. apply orb4 in H as [H | [H | [H | H]]].
    + apply UE_teq, typ_eqb_teq. exact H.
    + destruct T'; cbn in H; discriminate.
    + cbn in H. discriminate.
    + destruct T'; cbn in H; try discriminate. apply Hmu_r. exact H.
  - intros T' H. cbn [unroll_go] in H. apply orb4 in H as [H | [H | [H | H]]].
    + apply UE_teq, typ_eqb_teq. exact H.
    + destruct T'; cbn in H; discriminate.
    + cbn in H. discriminate.
    + destruct T'; cbn in H; try discriminate. apply Hmu_r. exact H.
  - intros T' H. cbn [unroll_go] in H. apply orb4 in H as [H | [H | [H | H]]].
    + apply UE_teq, typ_eqb_teq. exact H.
    + destruct T'; cbn in H; discriminate.
    + cbn in H. discriminate.
    + destruct T'; cbn in H; try discriminate. apply Hmu_r. exact H.
  - intros T' H. cbn [unroll_go] in H. apply orb4 in H as [H | [H | [H | H]]].
    + apply UE_teq, typ_eqb_teq. exact H.
    + destruct T'; cbn in H; discriminate.
    + cbn in H. discriminate.
    + destruct T'; cbn in H; try discriminate. apply Hmu_r. exact H.
  - intros A IHA B IHB T' H. cbn [unroll_go] in H. apply orb4 in H as [H | [H | [H | H]]].
    + apply UE_teq, typ_eqb_teq. exact H.
    + destruct T'; cbn in H; try discriminate.
      apply andb_true_iff in H as [H1 H2]. apply UE_arrow; [ apply IHA | apply IHB ]; assumption.
    + cbn in H. discriminate.
    + destruct T'; cbn in H; try discriminate. apply Hmu_r. exact H.
  - intros R IHR T' H. cbn [unroll_go] in H. apply orb4 in H as [H | [H | [H | H]]].
    + apply UE_teq, typ_eqb_teq. exact H.
    + destruct T'; cbn in H; try discriminate. apply UE_record, IHR. exact H.
    + cbn in H. discriminate.
    + destruct T'; cbn in H; try discriminate. apply Hmu_r. exact H.
  - intros a T' H. cbn [unroll_go] in H. apply orb4 in H as [H | [H | [H | H]]].
    + apply UE_teq, typ_eqb_teq. exact H.
    + destruct T'; cbn in H; discriminate.
    + cbn in H. discriminate.
    + destruct T'; cbn in H; try discriminate. apply Hmu_r. exact H.
  - intros i T' H. cbn [unroll_go] in H. apply orb4 in H as [H | [H | [H | H]]].
    + apply UE_teq, typ_eqb_teq. exact H.
    + destruct T'; cbn in H; discriminate.
    + cbn in H. discriminate.
    + destruct T'; cbn in H; try discriminate. apply Hmu_r. exact H.
  - intros B IHB T' H. cbn [unroll_go] in H. apply orb4 in H as [H | [H | [H | H]]].
    + apply UE_teq, typ_eqb_teq. exact H.
    + destruct T'; cbn in H; discriminate.
    + cbn in H. apply Hmu_l. exact H.
    + destruct T'; cbn in H; try discriminate. apply Hmu_r. exact H.
  - intros w A IHA T' H. cbn [unroll_go] in H. apply orb4 in H as [H | [H | [H | H]]].
    + apply UE_teq, typ_eqb_teq. exact H.
    + destruct T'; cbn in H; try discriminate.
      apply andb_true_iff in H as [H1 H2]. rewrite (gdecl_eqb_eq _ _ H1).
      apply UE_grp, IHA. exact H2.
    + cbn in H. discriminate.
    + destruct T'; cbn in H; try discriminate. apply Hmu_r. exact H.
  - intros R' H. cbn [unroll_go_row] in H. apply orb2 in H as [H | H].
    + apply UR_req, row_eqb_req. exact H.
    + destruct R'; cbn in H; discriminate.
  - intros r R' H. cbn [unroll_go_row] in H. apply orb2 in H as [H | H].
    + apply UR_req, row_eqb_req. exact H.
    + destruct R'; cbn in H; discriminate.
  - intros l T IHT R1 IHR R' H. cbn [unroll_go_row] in H. apply orb2 in H as [H | H].
    + apply UR_req, row_eqb_req. exact H.
    + destruct R'; cbn in H; try discriminate.
      apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
      apply Nat.eqb_eq in H1. subst. apply UR_ext; [ apply IHT | apply IHR ]; assumption.
  - intros l P IHP T IHT R1 IHR R' H. cbn [unroll_go_row] in H. apply orb2 in H as [H | H].
    + apply UR_req, row_eqb_req. exact H.
    + destruct R'; cbn in H; try discriminate.
      apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3].
      apply andb_true_iff in H as [H1 H2].
      apply Nat.eqb_eq in H1. subst.
      apply UR_maybe; [ apply IHP | apply IHT | apply IHR ]; assumption.
Qed.

(* A [true] answer is a derivation of the bounded equality. *)
Theorem unroll_eqb_sound : forall n T T', unroll_eqb n T T' = true -> unroll_eq n T T'.
Proof.
  induction n as [ | m IH]; intros T T' H; cbn [unroll_eqb] in H.
  - refine (proj1 (unroll_go_sound 0 _ _) _ _ H).
    intros T0 T0' H0. discriminate.
  - refine (proj1 (unroll_go_sound (S m) _ _) _ _ H).
    intros T0 T0' H0. exists m. split; [ lia | apply IH; exact H0 ].
Qed.

(* ---- the procedure at work ---- *)

(* The integer lists: mu a. { head : Int, tail : a }. *)
Definition list_body : typ :=
  typ_Record (row_Ext 0 typ_Int (row_Ext 1 (typ_Bvar 0) row_Empty)).

Definition list_ty : typ := typ_Mu list_body.

Example unroll_eqb_unfold :
  unroll_eqb 1 list_ty (open_typ 0 list_ty list_body) = true.
Proof. reflexivity. Qed.

Example unroll_eqb_fold :
  unroll_eqb 1 (open_typ 0 list_ty list_body) list_ty = true.
Proof. reflexivity. Qed.

(* No budget, no unrolling. *)
Example unroll_eqb_no_budget :
  unroll_eqb 0 list_ty (open_typ 0 list_ty list_body) = false.
Proof. reflexivity. Qed.

(* Two unrollings, one inside the other: the tail of the unrolling is a list
   too. *)
Definition list_unrolled_twice : typ :=
  typ_Record (row_Ext 0 typ_Int (row_Ext 1 (open_typ 0 list_ty list_body) row_Empty)).

Example unroll_eqb_twice :
  unroll_eqb 2 list_ty list_unrolled_twice = true.
Proof. reflexivity. Qed.

Example unroll_eqb_twice_needs_two :
  unroll_eqb 1 list_ty list_unrolled_twice = false.
Proof. reflexivity. Qed.

(* A mu under a field. *)
Example unroll_eqb_below_field :
  unroll_eqb 1 (typ_Arrow typ_Int list_ty)
               (typ_Arrow typ_Int (open_typ 0 list_ty list_body)) = true.
Proof. reflexivity. Qed.

Example unroll_eqb_distinct :
  unroll_eqb 5 list_ty typ_Int = false.
Proof. reflexivity. Qed.
