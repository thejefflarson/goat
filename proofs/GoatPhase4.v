(* Phase 4 of ADR 0037: worked examples for spread and restrict
   (docs/design/phase4-proof-plan.md).

   In goat source, with the labels x = 0 and y = 1:

     {...{x: 1, y: 2}, x: 5}     an update: the result has the base's type
     {...{y: 2}, x: 5}           an extension: the result adds x
     set_x = program(r) do {...r, x: 1} done
                                 one function for a record with an x and one
                                 without, by a presence variable
     {x, ...rest} = {x: 1, y: 2}  rest = restrict(..., x)

   The accepted examples fail to compile if a rule is dropped.  The rejected
   ones fail if the update keeps no field type, or a restrict is allowed on a
   record that lacks the label. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatLit.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatPresence.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSpread.
Require Import Goat.GoatSubst.
Require Import Goat.GoatPhase1.
Require Import Goat.GoatSound.
Require Import Stdlib.Lists.List.
Import ListNotations.

Definition lx : label := 0.
Definition ly : label := 1.

(* {x: 1, y: 2} and {y: 2} *)
Definition xy : exp := e_rec (fs_cons lx (e_num 1) (fs_cons ly (e_num 2) fs_nil)).
Definition only_y : exp := e_rec (fs_cons ly (e_num 2) fs_nil).

Definition row_y : row := row_Ext ly typ_Int row_Empty.
Definition row_xy : row := row_Ext lx typ_Int row_y.

Example xy_types : typing d_any nil xy (typ_Record row_xy).
Proof.
  unfold xy, row_xy, row_y. apply T_Record; [ | reflexivity ]. eapply FT_cons;
    [ apply T_Num; [ solve_uniq | exact I ] | ].
  eapply FT_cons; [ apply T_Num; [ solve_uniq | exact I ] | apply FT_nil; solve_uniq ].
Qed.

Example only_y_types : typing d_any nil only_y (typ_Record row_y).
Proof.
  unfold only_y, row_y. apply T_Record; [ | reflexivity ]. eapply FT_cons;
    [ apply T_Num; [ solve_uniq | exact I ] | apply FT_nil; solve_uniq ].
Qed.

(* ---- an update keeps the base's type ---- *)

Definition update_x : exp := e_spread xy lx (e_num 5).

Example update_types : typing d_any nil update_x (typ_Record row_xy).
Proof.
  unfold update_x. eapply T_Spread with (P := typ_Unit) (T := typ_Int) (R := row_y).
  - eapply T_Conv; [ exact xy_types | apply teq_rec; apply req_sym; apply req_pre ].
  - apply T_Num; [ solve_uniq | exact I ].
Qed.

Example update_runs : multistep update_x
  (e_rec (fs_cons lx (e_num 5) (fs_cons ly (e_num 2) fs_nil))).
Proof.
  unfold update_x, xy.
  eapply ms_step; [ apply st_spread; repeat constructor | ].
  apply ms_refl.
Qed.

(* ---- an extension adds a field the base lacks ---- *)

Definition extend_x : exp := e_spread only_y lx (e_num 5).

Example extend_types : typing d_any nil extend_x (typ_Record row_xy).
Proof.
  unfold extend_x. eapply T_Spread with (P := typ_Bool) (T := typ_Int) (R := row_y).
  - eapply T_Conv; [ exact only_y_types | ].
    apply teq_rec. apply req_sym. apply req_abs. reflexivity.
  - apply T_Num; [ solve_uniq | exact I ].
Qed.

Example extend_runs : multistep extend_x
  (e_rec (fs_cons lx (e_num 5) (fs_cons ly (e_num 2) fs_nil))).
Proof.
  unfold extend_x, only_y.
  eapply ms_step; [ apply st_spread; repeat constructor | ].
  apply ms_refl.
Qed.

(* ---- one function for both: a presence variable ---- *)

(* set_x at any presence [P] and rest [R]: the argument has [x] at Int, or
   none, and the result always has it. *)
Definition set_x : exp := e_abs (e_spread (e_fvar_b 0) lx (e_num 1)).

Lemma set_x_types : forall P R,
  typing d_any nil set_x
    (typ_Arrow (typ_Record (row_Maybe lx P typ_Int R)) (typ_Record (row_Ext lx typ_Int R))).
Proof.
  intros P R. unfold set_x. apply T_Abs with (L := {}). intros x Hx.
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec]. unfold lx.
  eapply T_Spread.
  - apply T_Var with (s := sch_mono (typ_Record (row_Maybe 0 P typ_Int R)));
      [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_mono_self ].
  - apply T_Num; [ solve_uniq | exact I ].
Qed.

(* set_x on {x: 1, y: 2}: presence Unit, the rest the one field y. *)
Example set_x_on_xy : typing d_any nil (e_app set_x xy) (typ_Record row_xy).
Proof.
  eapply T_App.
  - apply (set_x_types typ_Unit row_y).
  - eapply T_Conv; [ exact xy_types | apply teq_rec; apply req_sym; apply req_pre ].
Qed.

(* ... and on {y: 2}: presence Bool, the rest the one field y.  The same
   function, no second definition. *)
Example set_x_on_only_y : typing d_any nil (e_app set_x only_y) (typ_Record row_xy).
Proof.
  eapply T_App.
  - apply (set_x_types typ_Bool row_y).
  - eapply T_Conv; [ exact only_y_types | ].
    apply teq_rec. apply req_sym. apply req_abs. reflexivity.
Qed.

Example set_x_runs : multistep (e_app set_x only_y)
  (e_rec (fs_cons lx (e_num 1) (fs_cons ly (e_num 2) fs_nil))).
Proof.
  unfold set_x, only_y.
  eapply ms_step; [ apply st_beta; repeat constructor | ].
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec open_fields_wrt_exp_rec].
  eapply ms_step; [ apply st_spread; repeat constructor | ].
  apply ms_refl.
Qed.

(* ---- restrict ---- *)

Example restrict_types : typing d_any nil (e_restrict xy lx) (typ_Record row_y).
Proof.
  eapply T_Restrict; [ exact xy_types | unfold row_xy; apply rm_ext_here ].
Qed.

Example restrict_runs : multistep (e_restrict xy lx)
  (e_rec (fs_cons ly (e_num 2) fs_nil)).
Proof.
  unfold xy.
  eapply ms_step; [ apply st_restrict; repeat constructor | ].
  apply ms_refl.
Qed.

(* ---- what has no derivation ---- *)

(* An update keeps the field's type: x is a Bool in {x: true}, and "a" is a
   String. *)
Definition bool_x : exp := e_rec (fs_cons lx e_true fs_nil).

Example type_change_rejected : forall T,
  ~ typing d_any nil (e_spread bool_x lx (e_str [97])) T.
Proof.
  intros T H. destruct (spread_inv _ _ _ _ _ _ H) as [T0 [R [H2 [_ [[P H1] | [H1 Hl]]]]]].
  2: { (* the base's row would have to lack the label it has *)
    destruct (rec_inv _ _ _ _ H1) as [Rf [Hft Hteq]].
    destruct (teq_Record_inv _ _ Hteq) as [R2 [E Hreq]]. inversion E; subst R2.
    inversion Hft; subst.
    match goal with Hf : field_typing _ _ fs_nil _ |- _ => inversion Hf; subst end.
    pose proof (req_pi _ _ Hreq lx) as Hp. simpl in Hp.
    rewrite (rlacksD_pi d_any lx R Hl) in Hp. inversion Hp. }
  apply str_inv in H2.
  destruct (rec_inv _ _ _ _ H1) as [Rf [Hft Hteq]].
  destruct (teq_Record_inv _ _ Hteq) as [R2 [E Hreq]]. inversion E; subst R2.
  inversion Hft; subst.
  match goal with Hf : field_typing _ _ fs_nil _ |- _ => inversion Hf; subst end.
  match goal with Ht : typing _ _ e_true _ |- _ => apply true_inv in Ht end.
  destruct (presence_inv (row_Ext lx T1 row_Empty) lx P T0 R eq_refl Hreq) as [-> | [-> [_ Hpi]]].
  - assert (Hex : req (row_Ext lx T1 row_Empty) (row_Ext lx T0 R))
      by (eapply req_trans; [ exact Hreq | apply req_pre ]).
    destruct (req_surface _ _ _ _ Hex) as [T' [rest [Hpi Hq]]].
    cbn in Hpi. inversion Hpi; subst.
    assert (Hbs : teq typ_Bool typ_String).
    { eapply teq_trans; [ eassumption | ]. eapply teq_trans; [ exact Hq | ].
      apply teq_sym. exact H2. }
    apply teq_Bool_inv in Hbs. discriminate Hbs.
  - cbn in Hpi. discriminate Hpi.
Qed.

(* A restrict needs the label: {y: 2} has no x to take out. *)
Example restrict_missing_rejected : forall T,
  ~ typing d_any nil (e_restrict only_y lx) T.
Proof.
  intros T H. destruct (restrict_inv _ _ _ _ _ H) as [R0 [T0 [R [H1 [Hrm _]]]]].
  destruct (rec_inv _ _ _ _ H1) as [Rf [Hft Hteq]].
  destruct (teq_Record_inv _ _ Hteq) as [R2 [E Hreq]]. inversion E; subst R2.
  destruct (rm_req _ _ (req_sym _ _ Hreq) _ _ _ Hrm) as [T' [R' [Hrm' _]]].
  inversion Hft; subst.
  match goal with Hf : field_typing _ _ fs_nil _ |- _ => inversion Hf; subst end.
  destruct (rm_ext_inv _ _ _ _ _ _ Hrm') as [[E1 _] | [_ [R3 [Hr3 _]]]].
  - unfold lx, ly in *. discriminate E1.
  - exact (rm_empty_inv _ _ _ Hr3).
Qed.
