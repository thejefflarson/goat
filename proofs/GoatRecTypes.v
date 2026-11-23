(* Iso-recursive types: worked examples (docs/semantics.md sections 4 and 6,
   ADR 0032, ADR 0037 decision 3).  Tags do not exist in the calculus yet, so
   the recursion is the method-shaped record of ADR 0032, in goat source:

     P    = mu t. {moved: (t) -> t; x: Int}
     ball = fold {moved: program(s) do s done, x: 1}
     step = program(p) do (unfold p).moved(p) done

   The accepted examples fail to compile if a rule is dropped; the rejected
   ones fail if the guard on recursion is dropped or weakened. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatLit.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatMu.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

(* ---- the type ---- *)

Definition P_body : typ :=
  typ_Record (row_Ext 0 (typ_Arrow (typ_Bvar 0) (typ_Bvar 0)) (row_Ext 1 typ_Int row_Empty)).

Definition P : typ := typ_Mu P_body.

Example P_is_closed : lct 0 P.
Proof. simpl. repeat split; first [ exact I | lia ]. Qed.

Example P_is_guarded : guarded P_body.
Proof. unfold guarded. simpl. repeat split; auto. Qed.

Example P_unrolls :
  open_typ 0 P P_body =
  typ_Record (row_Ext 0 (typ_Arrow P P) (row_Ext 1 typ_Int row_Empty)).
Proof. reflexivity. Qed.

(* Iso: a recursive type is not equal to its unrolling. *)
Example P_is_not_its_unrolling : ~ teq P (open_typ 0 P P_body).
Proof.
  intros H. apply teq_Mu_inv in H. destruct H as [B [E _]]. discriminate E.
Qed.

(* ---- the terms ---- *)

Definition ball : exp :=
  e_fold (e_rec (fs_cons 0 (e_abs (e_fvar_b 0)) (fs_cons 1 (e_num 1) fs_nil))).

Definition step_fn : exp :=
  e_abs (e_app (e_proj (e_unfold (e_fvar_b 0)) 0) (e_fvar_b 0)).

Example ball_types : typing d_any nil ball P.
Proof.
  unfold ball. apply T_Fold; [ apply P_is_closed | apply P_is_guarded | ].
  change (typ_Mu P_body) with P. rewrite P_unrolls. apply T_Record; [ | reflexivity ]. eapply FT_cons.
  - apply T_Abs with (L := {}). intros s Hs.
    cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
    apply T_Var with (s := sch_mono P);
      [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_mono_self ].
  - eapply FT_cons; [ apply T_Num; [ solve_uniq | exact I ] | apply FT_nil; solve_uniq ].
Qed.

Example step_types : typing d_any nil step_fn (typ_Arrow P P).
Proof.
  unfold step_fn. apply T_Abs with (L := {}). intros p Hp.
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
  assert (Hp_ty : typing d_any ((p ~ sch_mono P) ++ nil) (e_fvar_f p) P)
    by (apply T_Var with (s := sch_mono P);
        [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_mono_self ]).
  assert (Hu : typing d_any ((p ~ sch_mono P) ++ nil) (e_unfold (e_fvar_f p))
                 (typ_Record (row_Ext 0 (typ_Arrow P P) (row_Ext 1 typ_Int row_Empty)))).
  { rewrite <- P_unrolls.
    apply T_Unfold; [ apply P_is_closed | apply P_is_guarded | exact Hp_ty ]. }
  eapply T_App; [ eapply T_Proj; exact Hu | exact Hp_ty ].
Qed.

(* step(ball) runs: the unfold cancels the fold, the method is read off the
   record and applied to the receiver, and the receiver comes back. *)
Example step_ball_runs : multistep (e_app step_fn ball) ball.
Proof.
  unfold step_fn, ball.
  eapply ms_step; [ apply st_beta; repeat constructor | ].
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec open_fields_wrt_exp_rec].
  eapply ms_step.
  { apply st_app1. apply st_proj. apply st_unfold_fold. repeat constructor. }
  eapply ms_step.
  { apply st_app1. apply st_projrec; [ repeat constructor | reflexivity ]. }
  eapply ms_step; [ apply st_beta; repeat constructor | ].
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec]. apply ms_refl.
Qed.

Example step_ball_types : typing d_any nil (e_app step_fn ball) P.
Proof. eapply T_App; [ exact step_types | exact ball_types ]. Qed.

(* ---- what has no derivation ---- *)

(* A fold whose payload is not the unrolling: the field x is missing. *)
Example ill_typed_fold_rejected :
  ~ typing d_any nil (e_fold (e_rec (fs_cons 1 e_true fs_nil))) P.
Proof.
  intros H. destruct (fold_inv _ _ _ _ H) as [B [Hteq [_ [_ Hb]]]].
  pose proof (teq_unroll B P_body Hteq) as Hun.
  change (typ_Mu P_body) with P in Hun. rewrite P_unrolls in Hun.
  destruct (rec_inv _ _ _ _ Hb) as [R [Hft Hr]].
  pose proof (teq_trans _ _ _ Hr Hun) as Hrr.
  destruct (teq_Record_inv _ _ Hrr) as [R2 [E Hreq]]. injection E as E. subst R2.
  inversion Hft; subst.
  match goal with Hf : field_typing _ _ fs_nil _ |- _ => inversion Hf; subst end.
  pose proof (req_pi _ _ Hreq 0) as Hpi. cbn in Hpi. inversion Hpi.
Qed.

(* Guarded recursion (ADR 0032): the index sits under a record field and under
   a function type.  Self-application, the vacuous mu, and a record with no
   function are all unguarded. *)
Example self_application_is_unguarded : ~ guarded (typ_Arrow (typ_Bvar 0) (typ_Bvar 0)).
Proof. unfold guarded. simpl. intros [H _]. destruct (H eq_refl) as [Hf _]. discriminate. Qed.

Example vacuous_mu_is_unguarded : ~ guarded (typ_Bvar 0).
Proof. unfold guarded. simpl. intros H. destruct (H eq_refl) as [Hf _]. discriminate. Qed.

Example record_without_function_is_unguarded :
  ~ guarded (typ_Record (row_Ext 0 (typ_Bvar 0) row_Empty)).
Proof. unfold guarded. simpl. intros [H _]. destruct (H eq_refl) as [_ Hf]. discriminate. Qed.

(* mu t. (t) -> t has no fold, whatever the conversion in between, so the
   rules cannot type the self-application that makes the untyped lambda
   calculus loop. *)
Theorem no_fold_at_self_application : forall D G e T,
  typing D G (e_fold e) T ->
  ~ teq T (typ_Mu (typ_Arrow (typ_Bvar 0) (typ_Bvar 0))).
Proof.
  intros D G e T H Heq. destruct (fold_inv _ _ _ _ H) as [B [Hteq [_ [Hg _]]]].
  pose proof (teq_trans _ _ _ Hteq Heq) as H2.
  destruct (teq_Mu_inv _ _ H2) as [B' [E Hb]]. injection E as E. subst B'.
  apply self_application_is_unguarded. eapply guarded_teq; [ exact Hb | exact Hg ].
Qed.
