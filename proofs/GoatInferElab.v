(* Algorithm W returns the elaborated term (ADR 0037, decision 3; phase 5,
   stage 4, part 1).

   [infer_elab fuel e = Some (D, e', T)] says [e'] has type [T] in the empty
   context and erases to [e]: the checker's program, with the [fold] and
   [unfold] its equi-recursive types leave implicit written in.  W never
   builds a recursive type ([infer_mu_free]), so on the fragment it covers
   today no coercion is ever needed and [e'] is [e] itself.  The statement is
   the one the knot-tying unifier keeps: a later part changes what [e'] is,
   not what is proved of it.

   [fold_free] is the syntactic fact that makes this so: W has no case for
   [e_fold] or [e_unfold], so a program it accepts contains neither. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatDefs.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSound.
Require Import Goat.GoatElab.
Require Import Stdlib.Lists.List.
Import ListNotations.

Fixpoint fold_free (e : exp) {struct e} : Prop :=
  match e with
  | e_fvar_b _ | e_fvar_f _ | e_num _ | e_dec _ | e_true | e_false
  | e_unit | e_str _ => True
  | e_abs e1 | e_proj e1 _ | e_tofloat e1 | e_con _ _ e1 | e_restrict e1 _ => fold_free e1
  | e_app e1 e2 | e_let e1 e2 | e_bin e1 _ e2 | e_spread e1 _ e2 => fold_free e1 /\ fold_free e2
  | e_letrec fs e2 => fold_free_fields fs /\ fold_free e2
  | e_rec fs => fold_free_fields fs
  | e_ite e1 e2 e3 => fold_free e1 /\ fold_free e2 /\ fold_free e3
  | e_match _ e1 ars => fold_free e1 /\ fold_free_arms ars
  | e_fold _ | e_unfold _ => False
  end
with fold_free_fields (fs : fields) {struct fs} : Prop :=
  match fs with
  | fs_nil => True
  | fs_cons _ e fs' => fold_free e /\ fold_free_fields fs'
  end
with fold_free_arms (ars : arms) {struct ars} : Prop :=
  match ars with
  | arms_nil => True
  | arms_else e => fold_free e
  | arms_cons _ e ars' => fold_free e /\ fold_free_arms ars'
  end.

Lemma erase_fold_free_mut :
  (forall e, fold_free e -> erase e = e) /\
  (forall fs, fold_free_fields fs -> erase_fields fs = fs) /\
  (forall ars, fold_free_arms ars -> erase_arms ars = ars).
Proof.
  apply exp_fields_mutind; intros; cbn [fold_free fold_free_fields fold_free_arms
    erase erase_fields erase_arms] in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try contradiction; try reflexivity;
    repeat match goal with H : ?P -> _ = _, H' : ?P |- _ => rewrite (H H'); clear H end;
    reflexivity.
Qed.

Lemma erase_fold_free : forall e, fold_free e -> erase e = e.
Proof. exact (proj1 erase_fold_free_mut). Qed.

Lemma fold_free_open_mut :
  (forall e k x, fold_free (open_exp_wrt_exp_rec k (e_fvar_f x) e) -> fold_free e) /\
  (forall fs k x, fold_free_fields (open_fields_wrt_exp_rec k (e_fvar_f x) fs) -> fold_free_fields fs) /\
  (forall ars k x, fold_free_arms (open_arms_wrt_exp_rec k (e_fvar_f x) ars) -> fold_free_arms ars).
Proof.
  apply exp_fields_mutind; intros;
    cbn [open_exp_wrt_exp_rec open_fields_wrt_exp_rec open_arms_wrt_exp_rec
         fold_free fold_free_fields fold_free_arms] in *;
    try exact I;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try (repeat split; eauto; fail); eauto.
Qed.

Lemma fold_free_open : forall e x,
  fold_free (open_exp_wrt_exp e (e_fvar_f x)) -> fold_free e.
Proof. intros e x. exact (proj1 fold_free_open_mut e 0 x). Qed.

Lemma fold_free_open_fields : forall fs x,
  fold_free_fields (open_fields_wrt_exp fs (e_fvar_f x)) -> fold_free_fields fs.
Proof. intros fs x. exact (proj1 (proj2 fold_free_open_mut) fs 0 x). Qed.

Lemma infer_fold_free : forall f,
  (forall lz ora D G e n s D' T n', infer f lz ora D G e n = Some (s, D', T, n') -> fold_free e) /\
  (forall lz ora D G fs n s D' R n', infer_fields f lz ora D G fs n = Some (s, D', R, n') ->
     fold_free_fields fs) /\
  (forall lz ora D G w Ts x res ars n s D' T n',
     infer_arms f lz ora D G w Ts x res ars n = Some (s, D', T, n') -> fold_free_arms ars).
Proof.
  induction f as [|f IH]; [ refine (conj _ (conj _ _)); intros; discriminate | ].
  destruct IH as [IHi [IHf IHa]].
  refine (conj _ (conj _ _)).
  - intros lz ora D G e n s D' T n' H.
    destruct e; cbn [infer] in H; try discriminate;
      cbn [fold_free]; try exact I;
      repeat match type of H with
        | context [match infer f ?lz ?o ?D ?G ?e ?n with _ => _ end] =>
            let E := fresh "E" in
            destruct (infer f lz o D G e n) as [[[[? ?] ?] ?]|] eqn:E; [ | discriminate ];
            apply IHi in E
        | context [match infer_fields f ?lz ?o ?D ?G ?e ?n with _ => _ end] =>
            let E := fresh "E" in
            destruct (infer_fields f lz o D G e n) as [[[[? ?] ?] ?]|] eqn:E; [ | discriminate ];
            apply IHf in E
        | context [match infer_arms f ?lz ?o ?D ?G ?w ?Ts ?x ?res ?e ?n with _ => _ end] =>
            let E := fresh "E" in
            destruct (infer_arms f lz o D G w Ts x res e n) as [[[[? ?] ?] ?]|] eqn:E; [ | discriminate ];
            apply IHa in E
        | context [unify_t ?f' ?D ?A ?B ?n] =>
            destruct (unify_t f' D A B n) as [[? ?]|]; [ | discriminate ]
        | context [match unify_pw ?f' ?D ?A ?B ?n with _ => _ end] =>
            destruct (unify_pw f' D A B n) as [[? ?]|]; [ | discriminate ]
        | context [bin_arg ?a ?b ?c ?d ?e ?g] =>
            destruct (bin_arg a b c d e g); [ | discriminate ]
        | context [bin_res ?a ?b ?c] => destruct (bin_res a b c); try discriminate
        | context [if ?c then _ else _] => destruct c; try discriminate
        end;
      repeat match goal with
        | E : fold_free (open_exp_wrt_exp _ _) |- _ => apply fold_free_open in E
        | E : fold_free_fields (open_fields_wrt_exp _ _) |- _ => apply fold_free_open_fields in E
        end;
      try (repeat split; assumption).
  - intros lz ora D G fs n s D' R n' H.
    destruct fs as [|l e rest]; cbn [infer_fields] in H; [ exact I | ].
    destruct (infer f lz ora D G e n) as [[[[s1 D1] T1] n1]|] eqn:E1; [ | discriminate ].
    apply IHi in E1.
    destruct (infer_fields f lz ora D1 (apC s1 G) rest n1) as [[[[s2 D2] R2] n2]|] eqn:E2; [ | discriminate ].
    apply IHf in E2. exact (conj E1 E2).
  - intros lz ora D G w Ts x res ars n s D' T n' H.
    destruct ars as [|e|tg e rest]; cbn [infer_arms] in H; [ exact I | | ].
    + destruct (infer f lz ora D G e n) as [[[[s1 D1] T1] n1]|] eqn:E1; [ | discriminate ].
      exact (IHi _ _ _ _ _ _ _ _ _ _ E1).
    + destruct (infer f lz ora D ((x ~ sch_mono (tag_payload w Ts tg)) ++ G)
                  (open_exp_wrt_exp e (e_fvar_f x)) n) as [[[[s1 D1] T1] n1]|] eqn:E1; [ | discriminate ].
      apply IHi in E1. apply fold_free_open in E1.
      destruct (unify_t f D1 (apT s1 res) T1 n1) as [[s2 n2]|]; [ | discriminate ].
      destruct (infer_arms f lz ora D1 (apC (scomp s2 s1) G) w (map (apT (scomp s2 s1)) Ts) x
                  (apT s2 T1) rest n2) as [[[[s3 D3] T3] n3]|] eqn:E2; [ | discriminate ].
      apply IHa in E2. exact (conj E1 E2).
Qed.

Definition infer_elab (fuel : nat) (e : exp) : option (denv * exp * typ) :=
  match infer_closed_env fuel e with
  | Some (D, T) => Some (D, e, T)
  | None => None
  end.

Lemma infer_closed_fold_free : forall fuel e D T,
  infer_closed_env fuel e = Some (D, T) -> fold_free e.
Proof.
  intros fuel e D T H. unfold infer_closed_env in H.
  destruct (infer fuel true (fun _ => typ_Int) d_any nil e 0) as [[[[s0 D00] T00] n0]|]; [ | discriminate ].
  destruct (infer fuel false (resolved s0) d_any nil e 0) as [[[[s D0] T0] n]|] eqn:E; [ | discriminate ].
  exact (proj1 (infer_fold_free fuel) _ _ _ _ _ _ _ _ _ _ E).
Qed.

Theorem infer_elab_sound : forall fuel e D e' T,
  infer_elab fuel e = Some (D, e', T) -> typing D nil e' T /\ erase e' = e.
Proof.
  intros fuel e D e' T H. unfold infer_elab in H.
  destruct (infer_closed_env fuel e) as [[D0 T0]|] eqn:E; [ | discriminate ].
  injection H as <- <- <-. split.
  - exact (infer_closed_sound _ _ _ _ E).
  - exact (erase_fold_free _ (infer_closed_fold_free _ _ _ _ E)).
Qed.
