(* Record arithmetic (ADR 0012): worked examples.

   In goat source, with the labels x = 0, y = 1 and p = 2:

     {x: 1} + {x: 2}                           = {x: 3}
     {p: {x: 2, y: 3}, x: 4} * {x: 5, p: {y: 7, x: 11}}
                                               = {p: {x: 22, y: 21}, x: 20}
     {x: 1, y: true} + {x: 2, y: false}        has no derivation

   The second sum lists its fields in another order at both levels, and each
   field finds its partner by label.  The accepted examples fail to compile if
   a rule is dropped; the rejected one fails if a record that holds a
   non-number becomes [Numeric].  The differential test runs the inference
   algorithm on record sums (differential/README.md); evaluating it here
   exceeds any reasonable time. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatLit.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatPresence.
Require Import Goat.GoatRecArith.
Require Import Goat.GoatMeta.
Require Import Goat.GoatPhase1.
Require Import Goat.GoatSound.
Require Import Stdlib.Lists.List.
Import ListNotations.

Definition lx : label := 0.
Definition ly : label := 1.
Definition lp : label := 2.

Definition xrec (n : exp) : exp := e_rec (fs_cons lx n fs_nil).

(* ---- {x: 1} + {x: 2} ---- *)

Definition row_x : row := row_Ext lx typ_Int row_Empty.

Example xrec_types : forall n, typing d_any nil (xrec (e_num n)) (typ_Record row_x).
Proof.
  intros n. unfold xrec, row_x. apply T_Record; [ | reflexivity ]. eapply FT_cons;
    [ apply T_Num; [ solve_uniq | exact I ] | apply FT_nil; solve_uniq ].
Qed.

Example record_sum_types :
  typing d_any nil (e_bin (xrec (e_num 1)) bop_add (xrec (e_num 2))) (typ_Record row_x).
Proof.
  eapply T_Bin with (A := typ_Record row_x) (B := typ_Record row_x);
    [ apply xrec_types | apply xrec_types | apply sig_ring ].
  - reflexivity.
  - simpl. split; exact I.
Qed.

Example record_sum_runs :
  multistep (e_bin (xrec (e_num 1)) bop_add (xrec (e_num 2))) (xrec (e_num 3)).
Proof.
  unfold xrec.
  eapply ms_step.
  { apply st_binrec; [ repeat constructor | repeat constructor | ].
    eapply rz_cons; [ reflexivity | apply rz_nil ]. }
  eapply ms_step.
  { apply st_rec, stf_here. apply st_bin; [ constructor | constructor | ].
    exact (bs_ring_int bop_add 1 2 eq_refl eq_refl). }
  apply ms_refl.
Qed.

(* ---- nested records, in another order ---- *)

Definition row_inner : row := row_Ext lx typ_Int (row_Ext ly typ_Int row_Empty).
Definition row_outer : row := row_Ext lp (typ_Record row_inner) (row_Ext lx typ_Int row_Empty).

Definition inner_l : exp := e_rec (fs_cons lx (e_num 2) (fs_cons ly (e_num 3) fs_nil)).
Definition inner_r : exp := e_rec (fs_cons ly (e_num 7) (fs_cons lx (e_num 11) fs_nil)).
Definition outer_l : exp := e_rec (fs_cons lp inner_l (fs_cons lx (e_num 4) fs_nil)).
Definition outer_r : exp := e_rec (fs_cons lx (e_num 5) (fs_cons lp inner_r fs_nil)).

Example inner_l_types : typing d_any nil inner_l (typ_Record row_inner).
Proof.
  unfold inner_l, row_inner. apply T_Record; [ | reflexivity ]. eapply FT_cons;
    [ apply T_Num; [ solve_uniq | exact I ] | ].
  eapply FT_cons; [ apply T_Num; [ solve_uniq | exact I ] | apply FT_nil; solve_uniq ].
Qed.

Example inner_r_types : typing d_any nil inner_r (typ_Record row_inner).
Proof.
  unfold inner_r, row_inner.
  eapply T_Conv with (T := typ_Record (row_Ext ly typ_Int (row_Ext lx typ_Int row_Empty))).
  - apply T_Record; [ | reflexivity ]. eapply FT_cons; [ apply T_Num; [ solve_uniq | exact I ] | ].
    eapply FT_cons; [ apply T_Num; [ solve_uniq | exact I ] | apply FT_nil; solve_uniq ].
  - apply teq_rec. apply req_swap. unfold lx, ly. discriminate.
Qed.

Example outer_l_types : typing d_any nil outer_l (typ_Record row_outer).
Proof.
  unfold outer_l, row_outer. apply T_Record; [ | reflexivity ]. eapply FT_cons; [ exact inner_l_types | ].
  eapply FT_cons; [ apply T_Num; [ solve_uniq | exact I ] | apply FT_nil; solve_uniq ].
Qed.

Example outer_r_types : typing d_any nil outer_r (typ_Record row_outer).
Proof.
  unfold outer_r, row_outer.
  eapply T_Conv with (T := typ_Record (row_Ext lx typ_Int
                             (row_Ext lp (typ_Record row_inner) row_Empty))).
  - apply T_Record; [ | reflexivity ]. eapply FT_cons; [ apply T_Num; [ solve_uniq | exact I ] | ].
    eapply FT_cons; [ exact inner_r_types | apply FT_nil; solve_uniq ].
  - apply teq_rec. apply req_swap. unfold lx, lp. discriminate.
Qed.

Example nested_product_types :
  typing d_any nil (e_bin outer_l bop_mul outer_r) (typ_Record row_outer).
Proof.
  eapply T_Bin with (A := typ_Record row_outer) (B := typ_Record row_outer);
    [ apply outer_l_types | apply outer_r_types | apply sig_ring ].
  - reflexivity.
  - simpl. repeat split; exact I.
Qed.

Example nested_product_runs :
  multistep (e_bin outer_l bop_mul outer_r)
    (e_rec (fs_cons lp (e_rec (fs_cons lx (e_num 22) (fs_cons ly (e_num 21) fs_nil)))
              (fs_cons lx (e_num 20) fs_nil))).
Proof.
  unfold outer_l, outer_r, inner_l, inner_r.
  eapply ms_step.
  { apply st_binrec; [ repeat constructor | repeat constructor | ].
    eapply rz_cons; [ reflexivity | ].
    eapply rz_cons; [ reflexivity | apply rz_nil ]. }
  eapply ms_step.
  { apply st_rec, stf_here. apply st_binrec; [ repeat constructor | repeat constructor | ].
    eapply rz_cons; [ reflexivity | ].
    eapply rz_cons; [ reflexivity | apply rz_nil ]. }
  eapply ms_step.
  { apply st_rec, stf_here, st_rec, stf_here. apply st_bin; [ constructor | constructor | ].
    exact (bs_ring_int bop_mul 2 11 eq_refl eq_refl). }
  eapply ms_step.
  { apply st_rec, stf_here, st_rec, stf_cons; [ constructor | ].
    apply stf_here. apply st_bin; [ constructor | constructor | ].
    exact (bs_ring_int bop_mul 3 7 eq_refl eq_refl). }
  eapply ms_step.
  { apply st_rec, stf_cons; [ repeat constructor | ].
    apply stf_here. apply st_bin; [ constructor | constructor | ].
    exact (bs_ring_int bop_mul 4 5 eq_refl eq_refl). }
  apply ms_refl.
Qed.

(* ---- what has no derivation ---- *)

(* A field that is not a number: {y: true} is not [Numeric], so the sum of two
   such records has no type, whatever the other fields are. *)
Definition mixed_l : exp := e_rec (fs_cons lx (e_num 1) (fs_cons ly e_true fs_nil)).
Definition mixed_r : exp := e_rec (fs_cons lx (e_num 2) (fs_cons ly e_false fs_nil)).

Example mixed_record_sum_rejected : forall T,
  ~ typing d_any nil (e_bin mixed_l bop_add mixed_r) T.
Proof.
  intros T H. unfold mixed_l, mixed_r in H.
  destruct (bin_inv _ _ _ _ _ _ H) as [A [B [R [H1 [H2 [Hs _]]]]]].
  destruct (rec_inv _ _ _ _ H1) as [Rf [Hft Hq]].
  destruct (teq_Record_inv _ _ Hq) as [R2 [-> Hr]].
  destruct (bin_sig_record _ _ _ _ _ Hs) as [-> [-> Hrow]].
  inversion Hft; subst.
  match goal with Hf : field_typing _ _ (fs_cons ly e_true fs_nil) _ |- _ => inversion Hf; subst end.
  match goal with Ht : typing _ _ e_true _ |- _ => apply true_inv in Ht end.
  match goal with Hf : field_typing _ _ fs_nil _ |- _ => inversion Hf; subst end.
  match goal with
  | Hr : req (row_Ext lx ?T0 (row_Ext ly ?T1 row_Empty)) R2 |- _ =>
      destruct (rm_req _ _ Hr ly T1 (row_Ext lx T0 row_Empty)
                  (rm_ext_skip ly lx T0 (row_Ext ly T1 row_Empty) T1 row_Empty
                     ltac:(unfold lx, ly; discriminate) (rm_ext_here ly T1 row_Empty)))
        as [T' [R' [Hrm [Hteq _]]]]
  end.
  destruct (rm_row_sig _ _ _ _ _ _ Hrow Hrm) as [Hb _].
  match goal with Ht : teq typ_Bool ?T1 |- _ =>
    assert (Hbt : teq typ_Bool T') by (eapply teq_trans; [ exact Ht | exact Hteq ]) end.
  apply teq_Bool_inv in Hbt. subst T'.
  sig_absurd Hb.
Qed.
