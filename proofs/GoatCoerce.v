(* The coercion pass: where a unifier's equation needs a [fold] or [unfold]
   (phase 5, stage 4, part 3b).

   [unify_k] equates two types up to unrolling ([unify_k_sound]): a mu may meet
   its own unfolding anywhere.  A term of the first type has the second only
   after the coercions of GoatElab.v, and those repair a difference at the HEAD
   of a type, a [fold] or [unfold] of the whole.  A difference below a function
   type or a record field would need an eta-expansion, which [erase] does not
   undo, so the pass refuses it (a deep coercion, counted by the differential
   test).

   [coerce_dec] decides this "head-coercible" relation: it answers with the
   coercions [cs] and [coerce_dec_sound] says [chain cs T T'].  The
   non-recursive part of the comparison is [teq_dec], which finds [teq] by
   syntax or by asking [unify_t], the unifier whose answer is already proved
   to be [teq], to equate the two types without changing either.  [unify_co]
   is the unifier the elaborating W calls: [unify_t] first, and [unify_k]
   followed by [coerce_dec] when that fails, and [unify_co_sound] is the join
   lemma W's soundness proof uses where [unify_sound] gave a [teq]. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Goat.GoatSubst.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatElab.
Require Import Goat.GoatUnrollEqb.
Require Import Goat.GoatKnot.
Require Import Goat.GoatGuard.
Require Import Goat.GoatInferKnot.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* A recursive type a coercion may fold into or unfold: closed, with a guarded
   body. *)
Definition mu_ok (T : typ) : bool :=
  match T with
  | typ_Mu B => lcb 0 T && gdk false false 0 B
  | _ => false
  end.

Lemma mu_ok_sound : forall B, mu_ok (typ_Mu B) = true -> lct 0 (typ_Mu B) /\ guarded B.
Proof.
  intros B H. cbn [mu_ok] in H. apply Bool.andb_true_iff in H as [H1 H2].
  split; [ apply lcb_lct; exact H1 | apply gdk_guarded; exact H2 ].
Qed.

(* ---- type equality, decided ---- *)

(* [teq] by syntax, or by a unifier run that leaves both types as they are. *)
Definition teq_dec (f : nat) (D : denv) (T T' : typ) : bool :=
  typ_eqb T T'
  || match unify_t f D T T' 0 with
     | Some (s, _) => typ_eqb (apT s T) T && typ_eqb (apT s T') T'
     | None => false
     end.

Lemma teq_dec_sound : forall f D T T', rtriv D ->
  EvT T -> EvT T' -> teq_dec f D T T' = true -> teq T T'.
Proof.
  intros f D T T' Hrt H1 H2 H. unfold teq_dec in H. apply Bool.orb_true_iff in H as [H | H].
  - apply typ_eqb_teq; exact H.
  - destruct (unify_t f D T T' 0) as [[s n']|] eqn:E; [ | discriminate ].
    apply Bool.andb_true_iff in H as [Ha Hb].
    destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ Hrt E H1 H2) as (_ & Ht & _).
    rewrite (proj1 typ_eqb_eq_mut _ _ Ha), (proj1 typ_eqb_eq_mut _ _ Hb) in Ht. exact Ht.
Qed.

(* ---- the head coercions between two types ---- *)

(* Unfold the first type's mu, or fold into the second's, and ask [rec] for the
   rest. *)
Definition co_unfold (rec : typ -> typ -> option (list dir)) (T T' : typ) : option (list dir) :=
  match T with
  | typ_Mu B => if mu_ok T then option_map (cons d_unfold) (rec (open_typ 0 T B) T') else None
  | _ => None
  end.

Definition co_fold (rec : typ -> typ -> option (list dir)) (T T' : typ) : option (list dir) :=
  match T' with
  | typ_Mu B' =>
      if mu_ok T' then option_map (fun cs => cs ++ [d_fold]) (rec T (open_typ 0 T' B')) else None
  | _ => None
  end.

(* The search spends a unit of fuel at every unrolling, so it ends. *)
Fixpoint coerce_dec (f : nat) (D : denv) (T T' : typ) {struct f} : option (list dir) :=
  if teq_dec f D T T' then Some nil
  else
    match f with
    | O => None
    | S f' =>
        match co_unfold (coerce_dec f' D) T T' with
        | Some cs => Some cs
        | None => co_fold (coerce_dec f' D) T T'
        end
    end.

Definition rec_chain (rec : typ -> typ -> option (list dir)) : Prop :=
  forall T T' cs, EvT T -> EvT T' -> rec T T' = Some cs -> chain cs T T'.

Lemma co_unfold_sound : forall rec T T' cs,
  rec_chain rec -> EvT T -> EvT T' -> co_unfold rec T T' = Some cs -> chain cs T T'.
Proof.
  intros rec T T' cs Hrec H1 H2 H. unfold co_unfold in H.
  destruct T as [| | | | | | | | | B | ]; try discriminate H.
  destruct (mu_ok (typ_Mu B)) eqn:Em; [ | discriminate ].
  destruct (rec (open_typ 0 (typ_Mu B) B) T') as [cs0|] eqn:Er; cbn [option_map] in H; [ | discriminate ].
  inversion H; subst. destruct (mu_ok_sound _ Em) as [Hl Hg].
  apply ch_unfold; [ exact Hl | exact Hg | ].
  apply (Hrec _ _ _ (EvT_open B 0 _ H1 H1) H2 Er).
Qed.

Lemma co_fold_sound : forall rec T T' cs,
  rec_chain rec -> EvT T -> EvT T' -> co_fold rec T T' = Some cs -> chain cs T T'.
Proof.
  intros rec T T' cs Hrec H1 H2 H. unfold co_fold in H.
  destruct T' as [| | | | | | | | | B | ]; try discriminate H.
  destruct (mu_ok (typ_Mu B)) eqn:Em; [ | discriminate ].
  destruct (rec T (open_typ 0 (typ_Mu B) B)) as [cs0|] eqn:Er; cbn [option_map] in H; [ | discriminate ].
  inversion H; subst. destruct (mu_ok_sound _ Em) as [Hl Hg].
  apply (chain_app cs0 [d_fold] T (open_typ 0 (typ_Mu B) B)).
  - apply (Hrec _ _ _ H1 (EvT_open B 0 _ H2 H2) Er).
  - apply ch_fold; [ exact Hl | exact Hg | constructor ].
Qed.

Theorem coerce_dec_sound : forall f D, rtriv D -> rec_chain (coerce_dec f D).
Proof.
  induction f as [|f IH]; intros D Hrt T T' cs H1 H2 H; cbn [coerce_dec] in H.
  all: destruct (teq_dec _ D T T') eqn:E.
  - inversion H; subst. eapply ch_conv; [ eapply teq_dec_sound; eassumption | constructor ].
  - discriminate.
  - inversion H; subst. eapply ch_conv; [ eapply teq_dec_sound; eassumption | constructor ].
  - destruct (co_unfold (coerce_dec f D) T T') as [cs0|] eqn:Eu.
    + inversion H; subst. eapply co_unfold_sound; [ apply (IH D Hrt) | exact H1 | exact H2 | exact Eu ].
    + eapply co_fold_sound; [ apply (IH D Hrt) | exact H1 | exact H2 | exact H ].
Qed.

(* ---- the unifier W calls ---- *)

(* The plain unifier first: when it succeeds the two types are [teq] and no
   coercion is needed, which is every program the algorithm accepted before it
   tied knots.  Only when it fails does [unify_k] equate them up to unrolling,
   and then the head coercions that take a term of the first type to the second
   under the substitution it found.  Failing to find them is a deep coercion. *)
Definition unify_co (f : nat) (D : denv) (T1 T2 : typ) (n : nat)
  : option (sub * list dir * nat) :=
  match unify_t f D T1 T2 n with
  | Some (s, n') => Some (s, nil, n')
  | None =>
      match unify_k f D T1 T2 n with
      | None => None
      | Some (s, n') =>
          match coerce_dec f D (apT s T1) (apT s T2) with
          | None => None
          | Some cs => Some (s, cs, n')
          end
      end
  end.

Theorem unify_co_sound : forall f D T1 T2 n s cs n', rtriv D ->
  unify_co f D T1 T2 n = Some (s, cs, n') -> EvT T1 -> EvT T2 ->
  OkS s /\ chain cs (apT s T1) (apT s T2) /\ kres D D (sT s) /\ n <= n'.
Proof.
  intros f D T1 T2 n s cs n' Hrt H H1 H2. unfold unify_co in H.
  destruct (unify_t f D T1 T2 n) as [[s0 n0]|] eqn:Et.
  - inversion H; subst; clear H.
    destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ Hrt Et H1 H2) as (Hs & Ht & Hk & Hl).
    refine (conj Hs (conj _ (conj Hk Hl))).
    eapply ch_conv; [ exact Ht | constructor ].
  - destruct (unify_k f D T1 T2 n) as [[s0 n0]|] eqn:E; [ | discriminate ].
    destruct (coerce_dec f D (apT s0 T1) (apT s0 T2)) as [cs0|] eqn:Ec; [ | discriminate ].
    inversion H; subst; clear H.
    destruct ((proj1 (unify_k_sound f)) D T1 T2 n Hrt s n' E H1 H2) as (Hs & _ & Hk & Hl).
    refine (conj Hs (conj _ (conj Hk Hl))).
    exact (coerce_dec_sound f D Hrt _ _ _ (EvT_ap s T1 Hs H1) (EvT_ap s T2 Hs H2) Ec).
Qed.

(* A chain survives a substitution whose images are closed: the coercions stay,
   the types move. *)
Lemma chain_ap : forall st sr cs T T', lc_sub st sr ->
  chain cs T T' -> chain cs (ap_typ st sr T) (ap_typ st sr T').
Proof.
  intros st sr cs T T' Hlc H. induction H.
  - constructor.
  - cbn [ap_typ]. apply ch_unfold.
    + apply (ap_lc st sr _ 0 Hlc) in H. exact H.
    + apply guarded_ap; assumption.
    + pose proof (ap_open st sr B 0 (typ_Mu B) Hlc) as Ho. cbn [ap_typ] in Ho.
      rewrite <- Ho. exact IHchain.
  - rewrite (ap_open st sr B 0 (typ_Mu B) Hlc). cbn [ap_typ] in IHchain |- *.
    apply (ch_fold (ap_typ st sr B) cs (ap_typ st sr T')).
    + apply (ap_lc st sr _ 0 Hlc) in H. exact H.
    + apply guarded_ap; assumption.
    + exact IHchain.
  - eapply ch_conv; [ | exact IHchain ].
    exact (teq_ap _ _ st sr H).
Qed.

Lemma chain_apT : forall s cs T T', OkS s ->
  chain cs T T' -> chain cs (apT s T) (apT s T').
Proof. intros s cs T T' Hs H. exact (chain_ap _ _ _ _ _ (OkS_lc s Hs) H). Qed.

(* ---- examples ---- *)

Definition swapped_a : typ :=
  typ_Record (row_Ext 0 typ_Int (row_Ext 1 typ_Bool row_Empty)).
Definition swapped_b : typ :=
  typ_Record (row_Ext 1 typ_Bool (row_Ext 0 typ_Int row_Empty)).

Example unfold_is_one_coercion :
  coerce_dec 10 d_any ball_ty ball_unrolled = Some [d_unfold].
Proof. vm_compute. reflexivity. Qed.

Example fold_is_one_coercion :
  coerce_dec 10 d_any ball_unrolled ball_ty = Some [d_fold].
Proof. vm_compute. reflexivity. Qed.

Example equal_types_need_none : coerce_dec 10 d_any ball_ty ball_ty = Some nil.
Proof. vm_compute. reflexivity. Qed.

Example reordered_rows_need_none : coerce_dec 10 d_any swapped_a swapped_b = Some nil.
Proof. vm_compute. reflexivity. Qed.

Example below_a_function_is_deep :
  coerce_dec 10 d_any (typ_Arrow ball_ty typ_Int) (typ_Arrow ball_unrolled typ_Int) = None.
Proof. vm_compute. reflexivity. Qed.

Example below_a_field_is_deep :
  coerce_dec 10 d_any (typ_Record (row_Ext 0 ball_ty row_Empty))
    (typ_Record (row_Ext 0 ball_unrolled row_Empty)) = None.
Proof. vm_compute. reflexivity. Qed.

Example a_mu_is_not_an_int : coerce_dec 10 d_any ball_ty typ_Int = None.
Proof. vm_compute. reflexivity. Qed.

Example the_unifier_finds_the_unfold :
  unify_co 10 d_any ball_ty ball_unrolled 0 = Some (sid, [d_unfold], 0).
Proof. vm_compute. reflexivity. Qed.

Example the_unifier_refuses_a_deep_difference :
  unify_co 10 d_any (typ_Arrow ball_ty typ_Int) (typ_Arrow ball_unrolled typ_Int) 0 = None.
Proof. vm_compute. reflexivity. Qed.
