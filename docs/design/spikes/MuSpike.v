(* Spike for docs/design/recursive-types-plan.md.  Not part of proofs/.

   A stripped calculus with goat's shape: types with a row-carrying record, free
   type and row variables that are atoms substituted by total maps (as in
   GoatDefs.v), and the one new thing, a `mu` binder written with de Bruijn
   indices (tBvar n, tMu T).  Terms are locally nameless with fold and unfold.

   Proved here, 0 admits:
     ap_open_mut      substitution commutes with unrolling (the hardest lemma)
     teq_ap_mut       type equality survives substitution, with no finite-support
                      hypothesis on the substitution
     teq_open         type equality survives unrolling, in body and argument
     teq_Mu_inv       a type equal to a mu is a mu, with equal bodies
     typing_tsubst    the type-substitution lemma through fold and unfold
     canon_mu         a closed value of a type equal to a mu is a fold
     preservation     for the unfold-of-fold redex and the fold/unfold congruences
     progress_unfold  unfold of a value or a stepping term steps

   Atoms are nat here (the real files use metalib atoms); nothing below depends
   on that. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Arith.Compare_dec.
Require Import Stdlib.micromega.Lia.
Import ListNotations.

Definition atom := nat.

Inductive typ : Set :=
  | tUnit : typ
  | tInt : typ
  | tArrow (A B : typ)
  | tRecord (R : row)
  | tVar (a : atom)
  | tBvar (n : nat)
  | tMu (T : typ)
with row : Set :=
  | rEmpty : row
  | rVar (r : atom)
  | rExt (l : nat) (T : typ) (R : row).

Scheme typ_mutind := Induction for typ Sort Prop
with row_mutind := Induction for row Sort Prop.
Combined Scheme typ_row_mutind from typ_mutind, row_mutind.

(* Unrolling: replace the index k by U, as Ott's open_typ_wrt_typ_rec does. *)
Fixpoint open_typ (k : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | tUnit => tUnit
  | tInt => tInt
  | tArrow A B => tArrow (open_typ k U A) (open_typ k U B)
  | tRecord R => tRecord (open_row k U R)
  | tVar a => tVar a
  | tBvar n =>
      match lt_eq_lt_dec n k with
      | inleft (left _) => tBvar n
      | inleft (right _) => U
      | inright _ => tBvar (n - 1)
      end
  | tMu T => tMu (open_typ (S k) U T)
  end
with open_row (k : nat) (U : typ) (R : row) {struct R} : row :=
  match R with
  | rEmpty => rEmpty
  | rVar r => rVar r
  | rExt l T R' => rExt l (open_typ k U T) (open_row k U R')
  end.

(* Substitution for free type and row variables: total maps, as GoatDefs.v. *)
Definition tsub := atom -> typ.
Definition rsub := atom -> row.

Fixpoint ap_typ (st : tsub) (sr : rsub) (T : typ) {struct T} : typ :=
  match T with
  | tUnit => tUnit
  | tInt => tInt
  | tArrow A B => tArrow (ap_typ st sr A) (ap_typ st sr B)
  | tRecord R => tRecord (ap_row st sr R)
  | tVar a => st a
  | tBvar n => tBvar n
  | tMu T => tMu (ap_typ st sr T)
  end
with ap_row (st : tsub) (sr : rsub) (R : row) {struct R} : row :=
  match R with
  | rEmpty => rEmpty
  | rVar r => sr r
  | rExt l T R' => rExt l (ap_typ st sr T) (ap_row st sr R')
  end.

(* Local closure: every index is bound by one of the k enclosing mus. *)
Fixpoint lct (k : nat) (T : typ) {struct T} : Prop :=
  match T with
  | tUnit | tInt | tVar _ => True
  | tArrow A B => lct k A /\ lct k B
  | tRecord R => lcr k R
  | tBvar n => n < k
  | tMu T => lct (S k) T
  end
with lcr (k : nat) (R : row) {struct R} : Prop :=
  match R with
  | rEmpty | rVar _ => True
  | rExt _ T R' => lct k T /\ lcr k R'
  end.

Lemma lc_mono :
  (forall T k m, lct k T -> k <= m -> lct m T) /\
  (forall R k m, lcr k R -> k <= m -> lcr m R).
Proof.
  apply typ_row_mutind; simpl; intros; try tauto.
  - destruct H1; split; eauto.
  - eauto.
  - lia.
  - eapply H; eauto. lia.
  - destruct H1; split; eauto.
Qed.

Lemma open_closed :
  (forall T k U, lct k T -> open_typ k U T = T) /\
  (forall R k U, lcr k R -> open_row k U R = R).
Proof.
  apply typ_row_mutind; simpl; intros; try reflexivity.
  - destruct H1. rewrite H, H0; auto.
  - rewrite H; auto.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; auto; lia.
  - rewrite H; auto.
  - destruct H1. rewrite H, H0; auto.
Qed.

(* A substitution is locally closed when it sends every variable to a type
   with no free index. *)
Definition lc_sub (st : tsub) (sr : rsub) : Prop :=
  (forall a, lct 0 (st a)) /\ (forall r, lcr 0 (sr r)).

(* The hardest lemma: substitution commutes with unrolling.  It needs the
   substitution to be locally closed, so that an index never leaks into the
   binder the substituted type is placed under. *)
Lemma ap_open_mut : forall st sr, lc_sub st sr ->
  (forall T k U, ap_typ st sr (open_typ k U T) = open_typ k (ap_typ st sr U) (ap_typ st sr T)) /\
  (forall R k U, ap_row st sr (open_row k U R) = open_row k (ap_typ st sr U) (ap_row st sr R)).
Proof.
  intros st sr [Hs Hr].
  apply typ_row_mutind; simpl; intros; try reflexivity.
  - rewrite H, H0; reflexivity.
  - rewrite H; reflexivity.
  - symmetry. apply (proj1 open_closed). eapply (proj1 lc_mono); [apply Hs | lia].
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
  - rewrite H; reflexivity.
  - symmetry. apply (proj2 open_closed). eapply (proj2 lc_mono); [apply Hr | lia].
  - rewrite H, H0; reflexivity.
Qed.

Lemma ap_lc_mut : forall st sr, lc_sub st sr ->
  (forall T k, lct k T -> lct k (ap_typ st sr T)) /\
  (forall R k, lcr k R -> lcr k (ap_row st sr R)).
Proof.
  intros st sr [Hs Hr].
  apply typ_row_mutind; simpl; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try split; auto;
    first [ eapply (proj1 lc_mono); [apply Hs | lia]
          | eapply (proj2 lc_mono); [apply Hr | lia] ].
Qed.

(* ---------------------------------------------------------------- *)
(* Type equality: congruence only.  There is no unrolling equation,    *)
(* which is what makes the recursion iso.  The mu rule compares bodies *)
(* directly, so no fresh name and no finite-support hypothesis appear.  *)
(* ---------------------------------------------------------------- *)

Inductive teq : typ -> typ -> Prop :=
  | teq_unit : teq tUnit tUnit
  | teq_int : teq tInt tInt
  | teq_var : forall a, teq (tVar a) (tVar a)
  | teq_bvar : forall n, teq (tBvar n) (tBvar n)
  | teq_arrow : forall A A' B B', teq A A' -> teq B B' -> teq (tArrow A B) (tArrow A' B')
  | teq_rec : forall R R', req R R' -> teq (tRecord R) (tRecord R')
  | teq_mu : forall T T', teq T T' -> teq (tMu T) (tMu T')
  | teq_trans : forall A B C, teq A B -> teq B C -> teq A C
  | teq_sym : forall A B, teq A B -> teq B A
with req : row -> row -> Prop :=
  | req_empty : req rEmpty rEmpty
  | req_var : forall r, req (rVar r) (rVar r)
  | req_head : forall l T T' R R', teq T T' -> req R R' -> req (rExt l T R) (rExt l T' R')
  | req_swap : forall l l' T T' R, l <> l' ->
      req (rExt l T (rExt l' T' R)) (rExt l' T' (rExt l T R))
  | req_trans : forall A B C, req A B -> req B C -> req A C
  | req_sym : forall A B, req A B -> req B A.

Scheme teq_mutind := Induction for teq Sort Prop
with req_mutind := Induction for req Sort Prop.
Combined Scheme teq_req_mutind from teq_mutind, req_mutind.

Lemma teq_req_refl :
  (forall T, teq T T) /\ (forall R, req R R).
Proof. apply typ_row_mutind; intros; try constructor; auto. Qed.

Lemma teq_refl : forall T, teq T T. Proof. apply teq_req_refl. Qed.
Lemma req_refl : forall R, req R R. Proof. apply teq_req_refl. Qed.

#[local] Hint Resolve teq_refl req_refl : core.
#[local] Hint Constructors teq req : core.

(* No finite-support or freshness hypothesis on the substitution: the index of
   a mu is untouched by it, so the case is the same congruence as an arrow. *)
Lemma teq_ap_mut : forall st sr,
  (forall T T', teq T T' -> teq (ap_typ st sr T) (ap_typ st sr T')) /\
  (forall R R', req R R' -> req (ap_row st sr R) (ap_row st sr R')).
Proof.
  intros st sr.
  apply teq_req_mutind; simpl; intros; eauto.
Qed.

(* Unrolling respects type equality: in the body ... *)
Lemma teq_open_body_mut : forall U,
  (forall T T', teq T T' -> forall k, teq (open_typ k U T) (open_typ k U T')) /\
  (forall R R', req R R' -> forall k, req (open_row k U R) (open_row k U R')).
Proof.
  intros U.
  apply teq_req_mutind; simpl; intros; eauto.
Qed.

(* ... and in the argument. *)
Lemma teq_open_arg_mut :
  (forall T k U U', teq U U' -> teq (open_typ k U T) (open_typ k U' T)) /\
  (forall R k U U', teq U U' -> req (open_row k U R) (open_row k U' R)).
Proof.
  apply typ_row_mutind; simpl; intros; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; auto.
Qed.

Lemma teq_open : forall T T' U U' k,
  teq T T' -> teq U U' -> teq (open_typ k U T) (open_typ k U' T').
Proof.
  intros. eapply teq_trans.
  - apply (proj1 (teq_open_body_mut U)); eauto.
  - apply (proj1 teq_open_arg_mut); auto.
Qed.

Definition thead (T : typ) : nat :=
  match T with
  | tUnit => 0 | tInt => 1 | tArrow _ _ => 2 | tRecord _ => 3
  | tVar _ => 4 | tBvar _ => 5 | tMu _ => 6
  end.

Lemma teq_thead : forall T T', teq T T' -> thead T = thead T'.
Proof. induction 1; simpl in *; congruence. Qed.

Lemma teq_mu_shape : forall T1 T2, teq T1 T2 ->
  (forall T, T1 = tMu T -> exists T', T2 = tMu T' /\ teq T T') /\
  (forall T, T2 = tMu T -> exists T', T1 = tMu T' /\ teq T T').
Proof.
  induction 1; try (split; intros; discriminate).
  - split; intros ? X; inversion X; subst.
    + eexists; split; [reflexivity | assumption].
    + eexists; split; [reflexivity | apply teq_sym; assumption].
  - destruct IHteq1 as [A1 A2], IHteq2 as [B1 B2]. split; intros.
    + destruct (A1 _ H1) as [? [? ?]]. destruct (B1 _ H2) as [? [? ?]].
      eexists; split; eauto.
    + destruct (B2 _ H1) as [? [? ?]]. destruct (A2 _ H2) as [? [? ?]].
      eexists; split; eauto.
  - destruct IHteq as [A1 A2]. split; eauto.
Qed.

Lemma teq_Mu_inv : forall T T', teq (tMu T) T' -> exists T'', T' = tMu T'' /\ teq T T''.
Proof. intros. apply (proj1 (teq_mu_shape _ _ H)); reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* Terms (locally nameless) and typing, with monotype contexts.        *)
(* ---------------------------------------------------------------- *)

Inductive exp : Set :=
  | eBvar (n : nat)
  | eFvar (x : atom)
  | eUnit
  | eAbs (e : exp)
  | eApp (e1 e2 : exp)
  | eFold (e : exp)
  | eUnfold (e : exp).

Fixpoint open_exp (k : nat) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | eBvar n =>
      match lt_eq_lt_dec n k with
      | inleft (left _) => eBvar n
      | inleft (right _) => u
      | inright _ => eBvar (n - 1)
      end
  | eFvar x => eFvar x
  | eUnit => eUnit
  | eAbs e => eAbs (open_exp (S k) u e)
  | eApp a b => eApp (open_exp k u a) (open_exp k u b)
  | eFold e => eFold (open_exp k u e)
  | eUnfold e => eUnfold (open_exp k u e)
  end.

Inductive value : exp -> Prop :=
  | v_unit : value eUnit
  | v_abs : forall e, value (eAbs e)
  | v_fold : forall v, value v -> value (eFold v).

Definition ctx := list (atom * typ).

Inductive typing : ctx -> exp -> typ -> Prop :=
  | T_Unit : forall G, typing G eUnit tUnit
  | T_Var : forall G x T, In (x, T) G -> typing G (eFvar x) T
  | T_Abs : forall (L : list atom) G A B e,
      (forall x, ~ In x L -> typing ((x, A) :: G) (open_exp 0 (eFvar x) e) B) ->
      typing G (eAbs e) (tArrow A B)
  | T_App : forall G A B e1 e2,
      typing G e1 (tArrow A B) -> typing G e2 A -> typing G (eApp e1 e2) B
  | T_Fold : forall G T e,
      lct 0 (tMu T) ->
      typing G e (open_typ 0 (tMu T) T) -> typing G (eFold e) (tMu T)
  | T_Unfold : forall G T e,
      typing G e (tMu T) -> typing G (eUnfold e) (open_typ 0 (tMu T) T)
  | T_Conv : forall G e T T', typing G e T -> teq T T' -> typing G e T'.

#[local] Hint Constructors typing value : core.

Definition ap_ctx (st : tsub) (sr : rsub) (G : ctx) : ctx :=
  map (fun p => (fst p, ap_typ st sr (snd p))) G.

(* The type-substitution lemma through fold and unfold. *)
Lemma typing_tsubst : forall G e T, typing G e T ->
  forall st sr, lc_sub st sr ->
    typing (ap_ctx st sr G) e (ap_typ st sr T).
Proof.
  induction 1; intros st sr Hlc; simpl.
  - constructor.
  - constructor. unfold ap_ctx. apply in_map_iff.
    exists (x, T). simpl. auto.
  - eapply T_Abs. intros x Hx. exact (H0 x Hx st sr Hlc).
  - eauto.
  - constructor.
    + simpl. apply (proj1 (ap_lc_mut st sr Hlc)). exact H.
    + specialize (IHtyping st sr Hlc).
      rewrite (proj1 (ap_open_mut st sr Hlc)) in IHtyping. exact IHtyping.
  - specialize (IHtyping st sr Hlc). simpl in IHtyping.
    rewrite (proj1 (ap_open_mut st sr Hlc)). simpl. constructor. exact IHtyping.
  - eapply T_Conv; [eauto|]. apply (proj1 (teq_ap_mut st sr)). auto.
Qed.

(* ---------------------------------------------------------------- *)
(* Inversions, canonical forms, preservation.                          *)
(* ---------------------------------------------------------------- *)

Lemma typing_fold_inv : forall G e0 T, typing G e0 T ->
  forall e, e0 = eFold e ->
  exists T0, teq T (tMu T0) /\ lct 0 (tMu T0) /\ typing G e (open_typ 0 (tMu T0) T0).
Proof.
  induction 1; intros e' E; try discriminate.
  - inversion E; subst. exists T. repeat split; auto.
  - destruct (IHtyping _ E) as [T0 [? [? ?]]].
    exists T0. repeat split; auto. eauto.
Qed.

Lemma typing_unfold_inv : forall G e0 T, typing G e0 T ->
  forall e, e0 = eUnfold e ->
  exists T0, typing G e (tMu T0) /\ teq T (open_typ 0 (tMu T0) T0).
Proof.
  induction 1; intros e' E; try discriminate.
  - inversion E; subst. exists T. auto.
  - destruct (IHtyping _ E) as [T0 [? ?]]. exists T0. eauto.
Qed.

(* Folding at a type equal to the one it was typed at. *)
Lemma retype_unrolling : forall T0 T1, teq (tMu T0) (tMu T1) ->
  teq (open_typ 0 (tMu T1) T1) (open_typ 0 (tMu T0) T0).
Proof.
  intros T0 T1 H. destruct (teq_Mu_inv _ _ H) as [T' [E Hb]]. inversion E; subst.
  apply teq_open; auto.
Qed.

Lemma canon_mu : forall G v T, typing G v T -> G = nil -> value v ->
  forall T0, teq T (tMu T0) ->
  exists v', v = eFold v' /\ value v' /\ typing nil v' (open_typ 0 (tMu T0) T0).
Proof.
  induction 1; intros HG Hv T0 Heq; subst.
  - apply teq_thead in Heq. discriminate.
  - destruct H.
  - apply teq_thead in Heq. discriminate.
  - inversion Hv.
  - inversion Hv; subst.
    exists e. repeat split; auto.
    eapply T_Conv; [exact H0|]. apply retype_unrolling. apply teq_sym. exact Heq.
  - inversion Hv.
  - apply IHtyping; auto. eauto.
Qed.

Inductive step : exp -> exp -> Prop :=
  | S_UnfoldFold : forall v, value v -> step (eUnfold (eFold v)) v
  | S_Unfold : forall e e', step e e' -> step (eUnfold e) (eUnfold e')
  | S_Fold : forall e e', step e e' -> step (eFold e) (eFold e').

Theorem preservation : forall G e T, typing G e T -> forall e', step e e' -> typing G e' T.
Proof.
  induction 1; intros e' Hs; try (inversion Hs; fail).
  - inversion Hs; subst. constructor; auto.
  - inversion Hs; subst.
    + destruct (typing_fold_inv _ _ _ H _ eq_refl) as [T1 [Heq [Hlc Hv]]].
      eapply T_Conv; [exact Hv|]. apply retype_unrolling. exact Heq.
    + constructor. auto.
  - eauto.
Qed.

Theorem progress_unfold : forall e T, typing nil (eUnfold e) T ->
  (value e \/ exists e', step e e') -> exists e', step (eUnfold e) e'.
Proof.
  intros e T Ht [Hv | [e' Hs]].
  - destruct (typing_unfold_inv _ _ _ Ht _ eq_refl) as [T0 [He _]].
    destruct (canon_mu _ _ _ He eq_refl Hv T0 (teq_refl _)) as [v' [E [Hv' _]]].
    subst. exists v'. constructor; auto.
  - eexists. constructor. exact Hs.
Qed.

Print Assumptions typing_tsubst.
Print Assumptions preservation.
Print Assumptions progress_unfold.
