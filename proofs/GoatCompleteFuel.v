(* Completeness of algorithm W, stage 7.5, part L0: fuel (docs/design/phase7-proof-plan.md).

   W's recursion is indexed by fuel, and a run that exhausts it returns [None],
   so a completeness proof that composes the runs of several sub-calls needs
   one fuel that works for all of them.  [unify_t] and [unify_r] are monotone
   in it: a [Some] answer at fuel [f] is the same answer at every larger fuel,
   because nothing they do depends on the fuel but whether it runs out.

   W itself is not monotone, and neither are [coerce_dec], [unify_co],
   [unify_k] (whose two-mu case tries the bodies and falls back to unrolling)
   or [unify_mem]: each falls back to a second search when the first returns
   [None], and [None] also means "out of fuel", so a larger fuel can take the
   first search to a [Some] that replaces the fallback's.  What a completeness
   proof needs is the weaker, composable statement that a run is [Stable]: it
   gives the same [Some] at every fuel from some point on.  [Stable] is closed
   under conjunction and under a shift of the fuel, and [unify_co_stable] says
   that a plain unifier success is a stable coercion-free [unify_co] success,
   which is the only way the plain fragment (no [fold], [unfold], or method)
   ever calls it. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferW.
Require Import Goat.GoatElab.
Require Import Goat.GoatCoerce.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ---- the plain unifier ---- *)

(* A scrutinee's value at fuel [f] is its value at fuel [S f], one level at a
   time; [mono_run] walks the two unfoldings together. *)
Ltac mono_run IHt IHr :=
  repeat (
    match goal with
    | H : context [match ?x with _ => _ end] |- _ =>
        let E := fresh "E" in
        destruct x eqn:E;
        cbv iota beta in H |- *;
        try discriminate H;
        try rewrite E;
        try rewrite (IHt _ _ _ _ _ E);
        try rewrite (IHr _ _ _ _ _ E);
        cbv iota beta in H |- *
    end).

Lemma unify_mono_pair : forall f g, f <= g ->
  (forall D T1 T2 n r, unify_t f D T1 T2 n = Some r -> unify_t g D T1 T2 n = Some r) /\
  (forall D R1 R2 n r, unify_r f D R1 R2 n = Some r -> unify_r g D R1 R2 n = Some r).
Proof.
  induction f as [|f IH]; intros g Hle; [ split; intros; discriminate | ].
  destruct g as [|g]; [ lia | ]. apply le_S_n in Hle.
  destruct (IH g Hle) as [IHt IHr]. split.
  - intros D T1 T2 n r H.
    destruct T1, T2; cbn [unify_t] in H |- *; try discriminate H; try exact H;
      mono_run IHt IHr;
      first [ exact H | exact (IHt _ _ _ _ _ H) | exact (IHr _ _ _ _ _ H) ].
  - intros D R1 R2 n r H.
    destruct R1, R2; cbn [unify_r] in H |- *; try discriminate H; try exact H;
      mono_run IHt IHr;
      first [ exact H | exact (IHt _ _ _ _ _ H) | exact (IHr _ _ _ _ _ H) ].
Qed.

Lemma unify_t_mono : forall f g D T1 T2 n r, f <= g ->
  unify_t f D T1 T2 n = Some r -> unify_t g D T1 T2 n = Some r.
Proof. intros f g D T1 T2 n r Hle H. exact (proj1 (unify_mono_pair f g Hle) _ _ _ _ _ H). Qed.

Lemma unify_r_mono : forall f g D R1 R2 n r, f <= g ->
  unify_r f D R1 R2 n = Some r -> unify_r g D R1 R2 n = Some r.
Proof. intros f g D R1 R2 n r Hle H. exact (proj2 (unify_mono_pair f g Hle) _ _ _ _ _ H). Qed.

(* ---- what stays true of the rest ---- *)

Lemma teq_dec_mono : forall f g D T T', f <= g ->
  teq_dec f D T T' = true -> teq_dec g D T T' = true.
Proof.
  intros f g D T T' Hle H. unfold teq_dec in H |- *.
  apply Bool.orb_true_iff in H as [H | H]; [ rewrite H; reflexivity | ].
  destruct (unify_t f D T T' 0) as [[[s D'] n']|] eqn:E; [ | discriminate ].
  rewrite (unify_t_mono f g _ _ _ _ _ Hle E). rewrite H. apply Bool.orb_true_r.
Qed.

(* [P] holds at every fuel from some point on. *)
Definition Stable (P : nat -> Prop) : Prop := exists f0, forall f, f0 <= f -> P f.

Lemma Stable_mono : forall (P Q : nat -> Prop),
  (forall f, P f -> Q f) -> Stable P -> Stable Q.
Proof. intros P Q HPQ [f0 H]. exists f0. intros f Hf. apply HPQ, H, Hf. Qed.

Lemma Stable_and : forall (P Q : nat -> Prop), Stable P -> Stable Q -> Stable (fun f => P f /\ Q f).
Proof.
  intros P Q [f1 H1] [f2 H2]. exists (Nat.max f1 f2). intros f Hf. split.
  - apply H1. eapply Nat.le_trans; [ apply Nat.le_max_l | exact Hf ].
  - apply H2. eapply Nat.le_trans; [ apply Nat.le_max_r | exact Hf ].
Qed.

(* A caller at fuel [S f] runs its sub-calls at [f]. *)
Definition Below (P : nat -> Prop) (f : nat) : Prop :=
  match f with O => False | S f' => P f' end.

Lemma Stable_below : forall (P : nat -> Prop), Stable P -> Stable (Below P).
Proof.
  intros P [f0 H]. exists (S f0). intros f Hf. destruct f as [|f]; [ lia | ].
  apply H. lia.
Qed.

Lemma Stable_const : forall P : Prop, P -> Stable (fun _ => P).
Proof. intros P H. exists 0. intros; exact H. Qed.

(* A fuel at which the plain unifier succeeds is a fuel from which it, and
   [unify_co] through it, succeeds in the same way and without a coercion. *)
Lemma unify_t_stable : forall f D T1 T2 n r,
  unify_t f D T1 T2 n = Some r -> Stable (fun g => unify_t g D T1 T2 n = Some r).
Proof. intros f D T1 T2 n r H. exists f. intros g Hg. exact (unify_t_mono f g _ _ _ _ _ Hg H). Qed.

Lemma unify_r_stable : forall f D R1 R2 n r,
  unify_r f D R1 R2 n = Some r -> Stable (fun g => unify_r g D R1 R2 n = Some r).
Proof. intros f D R1 R2 n r H. exists f. intros g Hg. exact (unify_r_mono f g _ _ _ _ _ Hg H). Qed.

Lemma unify_co_stable : forall f D T1 T2 n s D' n',
  unify_t f D T1 T2 n = Some (s, D', n') ->
  Stable (fun g => unify_co g D T1 T2 n = Some (s, D', nil, n')).
Proof.
  intros f D T1 T2 n s D' n' H. exists f. intros g Hg.
  unfold unify_co. rewrite (unify_t_mono f g _ _ _ _ _ Hg H). reflexivity.
Qed.

(* One construct, to show the pieces compose: an application whose two
   operands and whose unification each succeed from some fuel on succeeds from
   some fuel on. *)
Lemma infer_app_stable : forall D G e1 e2 n s1 D1 T1 n1 e1' s2 D2 T2 n2 e2' s3 D3 cs n3,
  Stable (fun f => infer f D G e1 n = Some (s1, D1, T1, n1, e1')) ->
  Stable (fun f => infer f D1 (apC s1 G) e2 n1 = Some (s2, D2, T2, n2, e2')) ->
  Stable (fun f => unify_coD f D2 (apT s2 T1) (typ_Arrow T2 (typ_Var (ea n2))) (S n2)
                     = Some (s3, D3, cs, n3)) ->
  Stable (fun f => infer f D G (e_app e1 e2) n =
    Some (scomp s3 (scomp s2 s1), D3, apT s3 (typ_Var (ea n2)), n3, e_app (coerce cs e1') e2')).
Proof.
  intros D G e1 e2 n s1 D1 T1 n1 e1' s2 D2 T2 n2 e2' s3 D3 cs n3 H1 H2 H3.
  pose proof (Stable_below _ (Stable_and _ _ H1 (Stable_and _ _ H2 H3))) as H.
  eapply Stable_mono; [ | exact H ].
  intros [|f] Hf; [ contradiction | ]. destruct Hf as (E1 & E2 & E3).
  cbn [infer]. rewrite E1, E2, E3. reflexivity.
Qed.
