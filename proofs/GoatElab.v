(* Elaboration (docs/design/phase5-proof-plan.md, stage 3; ADR 0037 decision 3).

   The checker's types are equi-recursive; the calculus's are iso-recursive.  An
   elaborated term writes the [fold] and [unfold] the checker leaves implicit.
   This file says what "the same program" means ([erase]), proves that erasure
   preserves behaviour in the direction that reads an iso program as the source
   program ([erase_step], [erase_traps]), gives the bounded-unrolling equality
   the unifier decides ([unroll_eq], written T ~~[n] T'), and the head
   coercions that repair a mismatch between a mu type and its unrolling
   ([coerce_typing], [erase_coerce]).

   A mismatch below a function type or a record field would need an
   eta-expansion, which [erase] does not undo; the plan counts those programs
   and skips them (DeepCoercion). *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatMu.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

(* ---- erasure ---- *)

Fixpoint erase (e : exp) {struct e} : exp :=
  match e with
  | e_fvar_b _ | e_fvar_f _ | e_num _ | e_dec _ | e_true | e_false
  | e_unit | e_str _ => e
  | e_abs e1 => e_abs (erase e1)
  | e_app e1 e2 => e_app (erase e1) (erase e2)
  | e_let e1 e2 => e_let (erase e1) (erase e2)
  | e_letrec fs e2 => e_letrec (erase_fields fs) (erase e2)
  | e_rec fs => e_rec (erase_fields fs)
  | e_proj e1 l => e_proj (erase e1) l
  | e_ite e1 e2 e3 => e_ite (erase e1) (erase e2) (erase e3)
  | e_bin e1 o e2 => e_bin (erase e1) o (erase e2)
  | e_tofloat e1 => e_tofloat (erase e1)
  | e_con w tg e1 => e_con w tg (erase e1)
  | e_match w e1 ars => e_match w (erase e1) (erase_arms ars)
  | e_spread e1 l e2 => e_spread (erase e1) l (erase e2)
  | e_restrict e1 l => e_restrict (erase e1) l
  | e_fold e1 => erase e1
  | e_unfold e1 => erase e1
  end
with erase_fields (fs : fields) {struct fs} : fields :=
  match fs with
  | fs_nil => fs_nil
  | fs_cons l e fs' => fs_cons l (erase e) (erase_fields fs')
  | fs_meth l e fs' => fs_meth l (erase e) (erase_fields fs')
  end
with erase_arms (ars : arms) {struct ars} : arms :=
  match ars with
  | arms_nil => arms_nil
  | arms_else e => arms_else (erase e)
  | arms_cons tg e ars' => arms_cons tg (erase e) (erase_arms ars')
  end.

Lemma erase_open_mut :
  (forall e k u, erase (open_exp_wrt_exp_rec k u e) = open_exp_wrt_exp_rec k (erase u) (erase e)) /\
  (forall fs k u, erase_fields (open_fields_wrt_exp_rec k u fs) =
                  open_fields_wrt_exp_rec k (erase u) (erase_fields fs)) /\
  (forall ars k u, erase_arms (open_arms_wrt_exp_rec k u ars) =
                   open_arms_wrt_exp_rec k (erase u) (erase_arms ars)).
Proof.
  apply exp_fields_mutind; intros;
    cbn [open_exp_wrt_exp_rec open_fields_wrt_exp_rec open_arms_wrt_exp_rec
         erase erase_fields erase_arms];
    repeat match goal with
           | H : forall (k : nat) (u : exp), _ = _ |- _ => rewrite H; clear H
           end;
    try reflexivity.
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma erase_open : forall e u,
  erase (open_exp_wrt_exp e u) = open_exp_wrt_exp (erase e) (erase u).
Proof. intros. apply (proj1 erase_open_mut). Qed.

Lemma erase_open_fields : forall fs u,
  erase_fields (open_fields_wrt_exp fs u) = open_fields_wrt_exp (erase_fields fs) (erase u).
Proof. intros. apply (proj1 (proj2 erase_open_mut)). Qed.

Lemma erase_value_mut :
  (forall v, value v -> value (erase v)) /\
  (forall fs, rec_value fs -> rec_value (erase_fields fs)).
Proof.
  apply value_rec_value_mutind; intros; cbn [erase erase_fields]; auto.
Qed.

Lemma erase_value : forall v, value v -> value (erase v).
Proof. apply erase_value_mut. Qed.

Lemma erase_rec_value : forall fs, rec_value fs -> rec_value (erase_fields fs).
Proof. apply erase_value_mut. Qed.

#[export] Hint Resolve erase_value erase_rec_value : core.

Lemma erase_lookup_first : forall l fs,
  lookup_first l (erase_fields fs) = option_map erase (lookup_first l fs).
Proof.
  induction fs as [|l0 e fs IH|l0 e fs IH]; cbn [erase_fields lookup_first]; try reflexivity;
    destruct (Nat.eqb l l0); first [ reflexivity | exact IH ].
Qed.

Lemma erase_fs_replace : forall l v fs,
  erase_fields (fs_replace l v fs) = fs_replace l (erase v) (erase_fields fs).
Proof.
  induction fs as [|l0 e fs IH|l0 e fs IH]; cbn [erase_fields fs_replace]; try reflexivity;
    destruct (Nat.eqb l l0); cbn [erase_fields]; try reflexivity; rewrite IH; reflexivity.
Qed.

Lemma erase_fs_drop : forall l fs,
  erase_fields (fs_drop l fs) = fs_drop l (erase_fields fs).
Proof.
  induction fs as [|l0 e fs IH|l0 e fs IH]; cbn [erase_fields fs_drop]; try reflexivity;
    destruct (Nat.eqb l l0); cbn [erase_fields]; try reflexivity; rewrite IH; reflexivity.
Qed.

Lemma erase_fs_set : forall l v fs,
  erase_fields (fs_set l v fs) = fs_set l (erase v) (erase_fields fs).
Proof.
  intros. unfold fs_set. rewrite erase_lookup_first.
  destruct (lookup_first l fs); cbn [option_map].
  - apply erase_fs_replace.
  - reflexivity.
Qed.

Lemma erase_fs_plain : forall fs,
  erase_fields (fs_plain fs) = fs_plain (erase_fields fs).
Proof.
  induction fs as [|l e fs IH|l e fs IH]; cbn [erase_fields fs_plain]; try reflexivity;
    rewrite IH; reflexivity.
Qed.

Lemma erase_arms_find : forall tg ars,
  arms_find tg (erase_arms ars) = option_map erase (arms_find tg ars).
Proof.
  induction ars; cbn [erase_arms arms_find]; try reflexivity.
  destruct (Nat.eqb tg tg0); [ reflexivity | exact IHars ].
Qed.

Lemma erase_arms_default : forall ars,
  arms_default (erase_arms ars) = option_map erase (arms_default ars).
Proof. induction ars; cbn [erase_arms arms_default]; try reflexivity. exact IHars. Qed.

Lemma erase_fn_group : forall fs, fn_group fs -> fn_group (erase_fields fs).
Proof. intros fs H. induction H; cbn [erase_fields erase]; constructor; auto. Qed.

Lemma erase_rec_zip : forall o fs1 fs2 fs,
  rec_zip o fs1 fs2 fs ->
  rec_zip o (erase_fields fs1) (erase_fields fs2) (erase_fields fs).
Proof.
  intros o fs1 fs2 fs H. induction H; cbn [erase_fields erase].
  - constructor.
  - econstructor.
    + rewrite erase_lookup_first, H. reflexivity.
    + rewrite <- erase_fs_drop. exact IHrec_zip.
Qed.

(* The operands and results of a primitive operation are base values, which
   carry no fold. *)
Lemma erase_val_bool : forall x b, val_bool x = Some b -> erase x = x.
Proof. intros x b H. destruct x; try discriminate H; reflexivity. Qed.

Lemma erase_of_bool : forall b, erase (of_bool b) = of_bool b.
Proof. destruct b; reflexivity. Qed.

Lemma erase_fl_pair : forall x y, fl_pair x y -> erase x = x /\ erase y = y.
Proof. intros x y H. inversion H; subst; split; reflexivity. Qed.

Lemma erase_fs_labels : forall fs, fs_labels (erase_fields fs) = fs_labels fs.
Proof. induction fs as [|l e fs IH|l e fs IH]; cbn [erase_fields fs_labels]; try rewrite IH; reflexivity. Qed.

Lemma erase_rec_labels : forall fs, rec_labels (erase_fields fs) = rec_labels fs.
Proof. intros fs. unfold rec_labels. rewrite erase_fs_labels. reflexivity. Qed.

Scheme cmp_rel_mind := Induction for cmp_rel Sort Prop
with cr_fields_mind := Induction for cr_fields Sort Prop.
Combined Scheme cmp_mutind from cmp_rel_mind, cr_fields_mind.

(* Erasing both operands keeps the comparison's result: [fold] is invisible,
   and a record's first field of a label erases to the first field of it. *)
Lemma erase_cmp_rel_mut :
  (forall a b c, cmp_rel a b c -> cmp_rel (erase a) (erase b) c) /\
  (forall labs fs1 fs2 c, cr_fields labs fs1 fs2 c ->
     cr_fields labs (erase_fields fs1) (erase_fields fs2) c).
Proof.
  apply cmp_mutind; intros; cbn [erase].
  - apply cr_int.
  - destruct (erase_fl_pair _ _ f) as [E1 E2]. rewrite E1, E2. apply cr_float. exact f.
  - apply cr_str.
  - rewrite (erase_val_bool _ _ e), (erase_val_bool _ _ e0). eapply cr_bool; eassumption.
  - apply cr_unit.
  - apply cr_rec. rewrite erase_rec_labels. assumption.
  - apply cf_nil.
  - eapply cf_eq; [ rewrite erase_lookup_first, e; reflexivity | rewrite erase_lookup_first, e0; reflexivity | | ]; assumption.
  - eapply cf_ne; [ rewrite erase_lookup_first, e; reflexivity | rewrite erase_lookup_first, e0; reflexivity | | ]; assumption.
Qed.

Lemma erase_cmp_rel : forall a b c, cmp_rel a b c -> cmp_rel (erase a) (erase b) c.
Proof. exact (proj1 erase_cmp_rel_mut). Qed.

Lemma erase_bin_step : forall o a b v,
  bin_step o a b v -> bin_step o (erase a) (erase b) (erase v).
Proof.
  intros o a b v H. inversion H; subst;
    try (match goal with Hc : cmp_rel _ _ _ |- _ =>
           rewrite erase_of_bool; apply bs_cmp; [ assumption | apply erase_cmp_rel; exact Hc ] end);
    repeat match goal with
           | Hp : fl_pair ?x ?y |- _ =>
               destruct (erase_fl_pair _ _ Hp) as [E1 E2]; clear Hp;
               try rewrite E1; try rewrite E2; clear E1 E2
           | Hv : val_bool ?x = Some _ |- _ =>
               rewrite (erase_val_bool _ _ Hv); clear Hv
           end;
    try rewrite erase_of_bool; exact H.
Qed.

Lemma erase_bin_trap : forall o a b k,
  bin_trap o a b k -> erase a = a /\ erase b = b.
Proof. intros o a b k H. inversion H; subst; split; reflexivity. Qed.

(* ---- erasure preserves behaviour ---- *)

(* A step of the elaborated term is either an [unfold(fold v) --> v], which
   erasure cannot see, or a step of the erased term. *)
Lemma erase_step_mut :
  (forall e e', step e e' -> erase e' = erase e \/ step (erase e) (erase e')) /\
  (forall fs fs', step_fields fs fs' ->
     erase_fields fs' = erase_fields fs \/ step_fields (erase_fields fs) (erase_fields fs')).
Proof.
  apply step_step_fields_mutind; intros; cbn [erase erase_fields].
  - (* beta *) right. rewrite erase_open. apply st_beta. auto.
  - (* app1 *) destruct H as [E | S]; [ left; rewrite E; reflexivity | right; apply st_app1; exact S ].
  - (* app2 *) destruct H as [E | S];
      [ left; rewrite E; reflexivity | right; apply st_app2; [ auto | exact S ] ].
  - (* letv *) right. rewrite erase_open. apply st_letv. auto.
  - (* let1 *) destruct H as [E | S]; [ left; rewrite E; reflexivity | right; apply st_let1; exact S ].
  - (* letrec *) right. rewrite erase_open. cbn [erase erase_fields].
    rewrite erase_open_fields. cbn [erase erase_fields]. apply st_letrec.
    apply erase_fn_group. auto.
  - (* proj *) destruct H as [E | S]; [ left; rewrite E; reflexivity | right; apply st_proj; exact S ].
  - (* projrec *) right. cbn [erase]. apply st_projrec with (v := erase v).
    + auto.
    + rewrite erase_lookup_first, e. reflexivity.
  - (* rec *) destruct H as [E | S]; [ left; rewrite E; reflexivity | right; apply st_rec; exact S ].
  - (* ite1 *) destruct H as [E | S]; [ left; rewrite E; reflexivity | right; apply st_ite1; exact S ].
  - (* ite true *) right. apply st_ite_true.
  - (* ite false *) right. apply st_ite_false.
  - (* bin1 *) destruct H as [E | S]; [ left; rewrite E; reflexivity | right; apply st_bin1; exact S ].
  - (* bin2 *) destruct H as [E | S];
      [ left; rewrite E; reflexivity | right; apply st_bin2; [ auto | exact S ] ].
  - (* bin *) right. apply st_bin; [ auto | auto | apply erase_bin_step; exact b ].
  - (* binrec *) right. apply st_binrec; auto.
    rewrite <- !erase_fs_plain. apply erase_rec_zip. exact r1.
  - (* tofloat1 *) destruct H as [E | S]; [ left; rewrite E; reflexivity | right; apply st_tofloat1; exact S ].
  - (* tofloat *) right. apply st_tofloat.
  - (* tofloat dec *) right. apply st_tofloat_dec.
  - (* spread1 *) destruct H as [E | S]; [ left; rewrite E; reflexivity | right; apply st_spread1; exact S ].
  - (* spread2 *) destruct H as [E | S];
      [ left; rewrite E; reflexivity | right; apply st_spread2; [ auto | exact S ] ].
  - (* spread *) right. rewrite erase_fs_plain, erase_fs_set. apply st_spread; auto.
  - (* restrict1 *) destruct H as [E | S]; [ left; rewrite E; reflexivity | right; apply st_restrict1; exact S ].
  - (* restrict *) right. rewrite erase_fs_plain, erase_fs_drop. apply st_restrict; auto.
  - (* fold1 *) exact H.
  - (* unfold1 *) exact H.
  - (* unfold_fold *) left. reflexivity.
  - (* con1 *) destruct H as [E | S]; [ left; rewrite E; reflexivity | right; apply st_con1; exact S ].
  - (* match1 *) destruct H as [E | S]; [ left; rewrite E; reflexivity | right; apply st_match1; exact S ].
  - (* match arm *) right. rewrite erase_open. apply st_match_arm; auto.
    rewrite erase_arms_find; match goal with Hf : arms_find _ _ = _ |- _ => rewrite Hf end; reflexivity.
  - (* match else *) right. apply st_match_else; auto.
    + rewrite erase_arms_find; match goal with Hf : arms_find _ _ = _ |- _ => rewrite Hf end; reflexivity.
    + rewrite erase_arms_default; match goal with Hf : arms_default _ = _ |- _ => rewrite Hf end; reflexivity.
  - (* stf_here *) destruct H as [E | S]; [ left; rewrite E; reflexivity | right; apply stf_here; exact S ].
  - (* stf_cons *) destruct H as [E | S];
      [ left; rewrite E; reflexivity | right; apply stf_cons; [ auto | exact S ] ].
  - (* stf_meth_here *) destruct H as [E | S]; [ left; rewrite E; reflexivity | right; apply stf_meth_here; exact S ].
  - (* stf_meth_cons *) destruct H as [E | S];
      [ left; rewrite E; reflexivity | right; apply stf_meth_cons; [ auto | exact S ] ].
Qed.

Theorem erase_step : forall e e', step e e' ->
  erase e' = erase e \/ step (erase e) (erase e').
Proof. apply erase_step_mut. Qed.

Theorem erase_multistep : forall e e', multistep e e' -> multistep (erase e) (erase e').
Proof.
  intros e e' H. induction H.
  - apply ms_refl.
  - destruct (erase_step _ _ H) as [E | S].
    + rewrite <- E. exact IHmultistep.
    + eapply ms_step; eassumption.
Qed.

Scheme traps_ind' := Induction for traps Sort Prop
  with traps_fields_ind' := Induction for traps_fields Sort Prop.
Combined Scheme traps_mutind from traps_ind', traps_fields_ind'.

Lemma erase_traps_mut :
  (forall e k, traps e k -> traps (erase e) k) /\
  (forall fs k, traps_fields fs k -> traps_fields (erase_fields fs) k).
Proof.
  apply traps_mutind; intros; cbn [erase erase_fields]; try (assumption; fail); try (constructor; auto; fail).
  - destruct (erase_bin_trap _ _ _ _ b) as [E1 E2]. rewrite E1, E2.
    apply tr_bin; auto.
Qed.

Theorem erase_traps : forall e k, traps e k -> traps (erase e) k.
Proof. apply erase_traps_mut. Qed.

(* A step erasure sees steps the erased term; the converse needs types and is
   [erase_converse] in GoatElabConverse.v. *)

(* ---- the bounded-unrolling equality, T ~~[n] T' ---- *)

(* [unroll_eq] is defined in GoatDefs.v, where T_Obj states the shared receiver with it. *)

Lemma unroll_refl : forall n T, unroll_eq n T T.
Proof. intros. apply UE_teq, teq_refl. Qed.

Lemma unroll_sym_mut :
  (forall n T T', unroll_eq n T T' -> unroll_eq n T' T) /\
  (forall n R R', unroll_row n R R' -> unroll_row n R' R).
Proof.
  apply unroll_mutind; intros;
    try (apply UE_teq; apply teq_sym; auto; fail);
    try (apply UR_req; apply req_sym; auto; fail);
    try (rewrite Nat.add_comm; eapply UE_trans; eauto; fail);
    try (rewrite Nat.add_comm; eapply UR_trans; eauto; fail);
    eauto.
Qed.

Theorem unroll_sym : forall n T T', unroll_eq n T T' -> unroll_eq n T' T.
Proof. exact (proj1 unroll_sym_mut). Qed.

(* A larger budget allows everything a smaller one does. *)
Lemma unroll_mono_mut :
  (forall n T T', unroll_eq n T T' -> unroll_eq (S n) T T') /\
  (forall n R R', unroll_row n R R' -> unroll_row (S n) R R').
Proof.
  apply unroll_mutind; intros;
    try (replace (S (m + n)) with (m + S n) by lia; eapply UE_trans; eauto; fail);
    try (replace (S (m + n)) with (m + S n) by lia; eapply UR_trans; eauto; fail);
    eauto.
Qed.

Theorem unroll_mono : forall m n T T', m <= n -> unroll_eq m T T' -> unroll_eq n T T'.
Proof.
  intros m n T T' Hle H. induction Hle; [ exact H | apply (proj1 unroll_mono_mut); exact IHHle ].
Qed.

(* T ~~ T' is the same for some budget. *)
Definition unroll_eq_some (T T' : typ) : Prop := exists n, unroll_eq n T T'.

Lemma teq_unroll_eq : forall T T', teq T T' -> unroll_eq 0 T T'.
Proof. intros. apply UE_teq. auto. Qed.

(* A mu and its unrolling are one unrolling apart, in both directions. *)
Lemma unroll_eq_unfold : forall B, unroll_eq 1 (typ_Mu B) (open_typ 0 (typ_Mu B) B).
Proof. intros. apply (UE_unfold 0). Qed.

Lemma unroll_eq_fold : forall B, unroll_eq 1 (open_typ 0 (typ_Mu B) B) (typ_Mu B).
Proof. intros. apply (UE_fold 0). Qed.

(* ... and one unrolling at a depth: the mu inside a function type and a
   record field. *)
Example unroll_eq_below_arrow : forall B C,
  unroll_eq 1 (typ_Arrow (typ_Mu B) C) (typ_Arrow (open_typ 0 (typ_Mu B) B) C).
Proof. intros. apply UE_arrow; [ apply unroll_eq_unfold | apply unroll_refl ]. Qed.

Example unroll_eq_below_field : forall B l C,
  unroll_eq 1 (typ_Record (row_Ext l (typ_Mu B) C))
              (typ_Record (row_Ext l (open_typ 0 (typ_Mu B) B) C)).
Proof.
  intros. apply UE_record. apply UR_ext;
    [ apply unroll_eq_unfold | apply UR_req, req_refl ].
Qed.

(* [unroll_ap] (substitution commutes with the relation) is in GoatSubst.v. *)

(* ---- head coercions ---- *)

Inductive dir : Set := d_fold | d_unfold.

Definition coerce1 (d : dir) (e : exp) : exp :=
  match d with d_fold => e_fold e | d_unfold => e_unfold e end.

(* The first coercion of the list is applied first, so it is innermost. *)
Fixpoint coerce (cs : list dir) (e : exp) : exp :=
  match cs with
  | nil => e
  | d :: cs' => coerce cs' (coerce1 d e)
  end.

(* [chain cs T T'] says the coercions [cs] take a term of type T to one of
   type T': each is one [unfold] of a mu, or one [fold] into it. *)
Inductive chain : list dir -> typ -> typ -> Prop :=
 | ch_nil : forall T, chain nil T T
 | ch_unfold : forall B cs T',
     lct 0 (typ_Mu B) -> guarded B ->
     chain cs (open_typ 0 (typ_Mu B) B) T' -> chain (d_unfold :: cs) (typ_Mu B) T'
 | ch_fold : forall B cs T',
     lct 0 (typ_Mu B) -> guarded B ->
     chain cs (typ_Mu B) T' -> chain (d_fold :: cs) (open_typ 0 (typ_Mu B) B) T'
 | ch_conv : forall cs T T1 T',
     teq T T1 -> chain cs T1 T' -> chain cs T T'.

#[export] Hint Constructors chain : core.

Theorem coerce_typing : forall D G cs T T' e,
  chain cs T T' -> typing D G e T -> typing D G (coerce cs e) T'.
Proof.
  intros D G cs T T' e H. revert e. induction H; intros e He; cbn [coerce coerce1].
  - exact He.
  - apply IHchain. apply T_Unfold; auto.
  - apply IHchain. apply T_Fold; auto.
  - apply IHchain. eapply T_Conv; eassumption.
Qed.

Theorem erase_coerce : forall cs e, erase (coerce cs e) = erase e.
Proof.
  induction cs as [ | d cs IH]; intros e; cbn [coerce]; [ reflexivity | ].
  rewrite IH. destruct d; reflexivity.
Qed.

(* A chain is a bounded unrolling: each coercion spends one unrolling. *)
Theorem chain_unroll_eq : forall cs T T', chain cs T T' -> unroll_eq (length cs) T T'.
Proof.
  intros cs T T' H. induction H; cbn [length].
  - apply unroll_refl.
  - apply (UE_trans 1 _ _ (open_typ 0 (typ_Mu B) B)); [ apply (UE_unfold 0) | exact IHchain ].
  - apply (UE_trans 1 _ _ (typ_Mu B)); [ apply (UE_fold 0) | exact IHchain ].
  - apply (UE_trans 0 _ _ T1); [ apply UE_teq; eassumption | exact IHchain ].
Qed.

Lemma chain_app : forall cs1 cs2 T1 T2 T3,
  chain cs1 T1 T2 -> chain cs2 T2 T3 -> chain (cs1 ++ cs2) T1 T3.
Proof.
  intros cs1 cs2 T1 T2 T3 H. induction H; intros H2; cbn [app]; eauto.
Qed.

Lemma coerce_app : forall cs1 cs2 e, coerce (cs1 ++ cs2) e = coerce cs2 (coerce cs1 e).
Proof. induction cs1; intros; cbn [app coerce]; [ reflexivity | apply IHcs1 ]. Qed.

(* A value stays a value under a [fold]; an unfold of a fold is a step.  So a
   coercion pair that cancels costs no more than the steps it takes. *)
Example unfold_fold_cancels : forall v, value v ->
  multistep (coerce [d_fold; d_unfold] v) v.
Proof.
  intros v Hv. cbn [coerce coerce1].
  eapply ms_step; [ apply st_unfold_fold; exact Hv | apply ms_refl ].
Qed.
