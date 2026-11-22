(* Recursion and the value restriction: worked examples (docs/semantics.md
   sections 4 and 6, ADR 0003, ADR 0027).  The accepted examples fail to
   compile if a rule is dropped, and the classification examples if the
   predicate of the value restriction changes. *)

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

Arguments bs_cmp_int o a%_znum_scope b%_znum_scope _.

Definition a0 : atom := fresh nil.

(* ---- the value restriction: what a [let] may generalize ---- *)

Example unit_generalizes : is_gen_value e_unit = true.
Proof. reflexivity. Qed.

Example literal_generalizes : is_gen_value (e_num 3) = true.
Proof. reflexivity. Qed.

Example name_generalizes : is_gen_value (e_fvar_f a0) = true.
Proof. reflexivity. Qed.

Example function_generalizes : is_gen_value (e_abs (e_fvar_b 0)) = true.
Proof. reflexivity. Qed.

Example record_of_values_generalizes :
  is_gen_value (e_rec (fs_cons 0 (e_abs (e_fvar_b 0)) (fs_cons 1 (e_num 1) fs_nil))) = true.
Proof. reflexivity. Qed.

Example coerced_literal_generalizes : is_gen_value (e_tofloat (e_num 3)) = true.
Proof. reflexivity. Qed.

Example call_does_not_generalize :
  is_gen_value (e_app (e_abs (e_fvar_b 0)) (e_num 1)) = false.
Proof. reflexivity. Qed.

Example projection_does_not_generalize :
  is_gen_value (e_proj (e_rec fs_nil) 0) = false.
Proof. reflexivity. Qed.

Example record_with_a_call_does_not_generalize :
  is_gen_value (e_rec (fs_cons 0 (e_app (e_abs (e_fvar_b 0)) (e_num 1)) fs_nil)) = false.
Proof. reflexivity. Qed.

Example operation_does_not_generalize :
  is_gen_value (e_bin (e_num 1) bop_add (e_num 2)) = false.
Proof. reflexivity. Qed.

Example let_does_not_generalize :
  is_gen_value (e_let (e_num 1) (e_fvar_b 0)) = false.
Proof. reflexivity. Qed.

(* ---- a generalized binding is used at two types ---- *)

(* id = program(x) do x done, then {0: id(1), 1: id(true)} *)

Definition id_pair : exp :=
  e_let (e_abs (e_fvar_b 0))
        (e_rec (fs_cons 0 (e_app (e_fvar_b 0) (e_num 1))
               (fs_cons 1 (e_app (e_fvar_b 0) e_true) fs_nil))).

Lemma inst_id_at : forall U, lct 0 U ->
  inst d_any (typ_Arrow U U) (gen nil (typ_Arrow (typ_Var a0) (typ_Var a0)) (fun _ => k_Any)).
Proof.
  intros U HL.
  exists (fun a => if a == a0 then U else typ_Var a), idr.
  split; [ | split; [ | split; [ | split ] ] ].
  - intros a Ha. simpl in Ha. destruct (a == a0) as [E|E]; [ subst; exfalso; apply Ha; fsetdec | reflexivity ].
  - intros r _. reflexivity.
  - simpl. destruct (a0 == a0) as [E|E]; [ reflexivity | congruence ].
  - intros a Ha. apply sat_any.
  - split; [ intros a; simpl; match goal with |- context [if ?c then _ else _] => destruct c end; [ exact HL | exact I ] | intros r; exact I ].
Qed.

Example let_of_a_function_is_used_at_two_types :
  typing d_any nil id_pair
    (typ_Record (row_Ext 0 typ_Int (row_Ext 1 typ_Bool row_Empty))).
Proof.
  unfold id_pair.
  apply T_Let with (L := {}) (T1 := typ_Arrow (typ_Var a0) (typ_Var a0)) (k := fun _ => k_Any);
    [ reflexivity | | ].
  - apply T_Abs with (L := {}). intros x Hx.
    cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
    apply T_Var with (s := sch_mono (typ_Var a0));
      [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_mono_self ].
  - intros f Hf.
    cbn [open_exp_wrt_exp open_exp_wrt_exp_rec open_fields_wrt_exp_rec].
    apply T_Record. eapply FT_cons.
    + eapply T_App; [ | apply T_Num; [ solve_uniq | ] ].
      * apply T_Var with (s := gen nil (typ_Arrow (typ_Var a0) (typ_Var a0)) (fun _ => k_Any));
          [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_id_at; exact I ].
      * exact I.
    + eapply FT_cons; [ | apply FT_nil; solve_uniq ].
      eapply T_App; [ | apply T_True; solve_uniq ].
      apply T_Var with (s := gen nil (typ_Arrow (typ_Var a0) (typ_Var a0)) (fun _ => k_Any));
        [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_id_at; exact I ].
Qed.

(* ---- a recursive group ---- *)

(* letrec p = {0: program(n) do if n < 1 then 0 else p.0(n - 1) done} in p.0(2):
   inside the member the group name is index 1 and the parameter is index 0 *)
Definition countdown_member : exp :=
  e_abs (e_ite (e_bin (e_fvar_b 0) bop_lt (e_num 1))
               (e_num 0)
               (e_app (e_proj (e_fvar_b 1) 0)
                      (e_bin (e_fvar_b 0) bop_sub (e_num 1)))).

Definition countdown : exp :=
  e_letrec (fs_cons 0 countdown_member fs_nil)
           (e_app (e_proj (e_fvar_b 0) 0) (e_num 2)).

Definition countdown_row : row := row_Ext 0 (typ_Arrow typ_Int typ_Int) row_Empty.

Example recursive_group_types : typing d_any nil countdown typ_Int.
Proof.
  unfold countdown.
  apply T_Letrec with (L := {}) (R := countdown_row) (k := fun _ => k_Any).
  - repeat constructor.
  - intros p Hp.
    unfold open_fields_wrt_exp. cbn [open_fields_wrt_exp_rec open_exp_wrt_exp_rec].
    unfold countdown_member. cbn [open_exp_wrt_exp_rec].
    eapply FT_cons; [ | apply FT_nil; solve_uniq ].
    apply T_Abs with (L := {{p}}). intros n Hn.
    cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
    apply T_If.
    + eapply T_Bin; [ | | apply sig_cmp ].
      * apply T_Var with (s := sch_mono typ_Int);
          [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_mono_self ].
      * apply T_Num; [ solve_uniq | exact I ].
      * constructor.
      * constructor.
    + apply T_Num; [ solve_uniq | exact I ].
    + eapply T_App.
      * eapply T_Proj.
        apply T_Var with (s := sch_mono (typ_Record countdown_row));
          [ solve_uniq | apply binds_cons_3; apply binds_cons_2; reflexivity
          | apply inst_mono_self ].
      * eapply T_Bin; [ | | apply sig_ring ].
        -- apply T_Var with (s := sch_mono typ_Int);
             [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_mono_self ].
        -- apply T_Num; [ solve_uniq | exact I ].
        -- reflexivity.
        -- exact I.
  - intros p Hp.
    cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
    eapply T_App.
    + eapply T_Proj.
      apply T_Var with (s := gen nil (typ_Record countdown_row) (fun _ => k_Any));
        [ solve_uniq | apply binds_cons_2; reflexivity | ].
      exists idt, idr. split; [ | split; [ | split; [ | split ] ] ].
      * intros a Ha. reflexivity.
      * intros r Hr. reflexivity.
      * symmetry. apply ap_typ_pointwise_id; reflexivity.
      * intros a Ha. apply sat_any.
      * apply lc_sub_id.
    + apply T_Num; [ solve_uniq | exact I ].
Qed.

(* The group unrolls when it is reached: its name becomes the record of its
   functions, in which each reference to the group is the group again. *)
Example recursive_group_unrolls :
  step countdown
    (e_app (e_proj (e_rec (fs_cons 0
              (e_abs (e_ite (e_bin (e_fvar_b 0) bop_lt (e_num 1))
                            (e_num 0)
                            (e_app (e_proj
                                      (e_letrec (fs_cons 0 countdown_member fs_nil)
                                                (e_fvar_b 0)) 0)
                                   (e_bin (e_fvar_b 0) bop_sub (e_num 1)))))
              fs_nil)) 0) (e_num 2)).
Proof.
  apply st_letrec. repeat constructor.
Qed.

(* A function that does not mention its group steps like a [let] of it. *)
Example group_without_recursion_runs :
  multistep
    (e_letrec (fs_cons 0 (e_abs (e_fvar_b 0)) fs_nil)
              (e_app (e_proj (e_fvar_b 0) 0) (e_num 7)))
    (e_num 7).
Proof.
  eapply ms_step; [ apply st_letrec; repeat constructor | ].
  cbn.
  eapply ms_step; [ apply st_app1; apply st_projrec; [ repeat constructor | reflexivity ] | ].
  cbn.
  eapply ms_step; [ apply st_beta; constructor | ].
  cbn. apply ms_refl.
Qed.

(* ---- widening at a join site (ADR 0040) ----
   The checker accepts [if c then 7 // 2 else 2.5 done] and a call
   [f(7 // 2, 2.5)] to [program(a, b) do a + b done]: an Int branch or argument
   widens to the Float it meets. There is no subtyping: elaboration writes
   [float(e)] at the Int side, and the rules type the elaborated term. *)

Example widened_branch_types :
  typing d_any nil
    (e_ite e_true (e_tofloat (e_num 3)) (e_dec 0)) typ_Float.
Proof.
  apply T_If; [ apply T_True; solve_uniq | | apply T_Dec; solve_uniq ].
  apply T_ToFloat with (A := typ_Int); [ apply T_Num; [ solve_uniq | exact I ] | exact I ].
Qed.

Example widened_call_types :
  typing d_any nil
    (e_app (e_app (e_abs (e_abs (e_bin (e_fvar_b 1) bop_add (e_fvar_b 0))))
              (e_tofloat (e_num 3)))
           (e_dec 0))
    typ_Float.
Proof.
  eapply T_App; [ | apply T_Dec; solve_uniq ].
  eapply T_App; [ | apply T_ToFloat with (A := typ_Int); [ apply T_Num; [ solve_uniq | exact I ] | exact I ] ].
  apply T_Abs with (L := {}). intros x Hx.
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
  apply T_Abs with (L := {{x}}). intros y Hy.
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
  eapply T_Bin; [ eapply T_Var | eapply T_Var | apply sig_ring ].
  all: first [ solve_uniq
             | (unfold binds; simpl; destruct (x == x); [ reflexivity | congruence ])
             | apply inst_mono_self | reflexivity | exact I ].
Qed.

(* A group member must be a function: a member that is a literal has no
   derivation, because the group would not unroll to a record of values. *)
Example group_member_must_be_a_function : forall e2 T,
  ~ typing d_any nil (e_letrec (fs_cons 0 (e_num 1) fs_nil) e2) T.
Proof.
  intros e2 T H. destruct (letrec_inv _ _ _ _ _ H) as [L [R [T2 [k [Hfg _]]]]].
  inversion Hfg.
Qed.

(* ---- a comparison on a number a later use settles ----
   Both terms are derivable, so the checker is sound where it accepts them: the
   numeral's type is whatever the rules need, here chosen as Float and as Int. *)

Example compared_let_bound_numeral_types :
  typing d_any nil
    (e_let (e_bin (e_num 71) bop_fdiv (e_num 88))
           (e_ite (e_bin (e_fvar_b 0) bop_lte (e_fvar_b 0))
                  (e_bin (e_fvar_b 0) bop_sub (e_dec 0))
                  (e_dec 0)))
    typ_Float.
Proof.
  apply T_LetMono with (L := {}) (T1 := typ_Float).
  - apply T_Bin with (A := typ_Float) (B := typ_Float); [ apply T_Num | apply T_Num | apply sig_whole ].
    all: first [ solve_uniq | reflexivity | exact I ].
  - intros x Hx.
    cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
    apply T_If; [ | | apply T_Dec; solve_uniq ].
    + eapply T_Bin; [ eapply T_Var | eapply T_Var | apply sig_cmp ].
      all: first [ solve_uniq
                 | (unfold binds; simpl; destruct (x == x); [ reflexivity | congruence ])
                 | apply inst_mono_self | reflexivity | constructor ].
    + eapply T_Bin; [ eapply T_Var | apply T_Dec | apply sig_ring ].
      all: first [ solve_uniq
                 | (unfold binds; simpl; destruct (x == x); [ reflexivity | congruence ])
                 | apply inst_mono_self | reflexivity | exact I ].
Qed.

Example compared_parameter_types :
  typing d_any nil
    (e_app (e_abs (e_bin (e_fvar_b 0) bop_eq (e_bin (e_fvar_b 0) bop_rem (e_fvar_b 0))))
           (e_num 90))
    typ_Bool.
Proof.
  apply T_App with (T1 := typ_Int); [ | apply T_Num; [ solve_uniq | exact I ] ].
  apply T_Abs with (L := {}). intros x Hx.
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
  eapply T_Bin; [ eapply T_Var | eapply T_Bin; [ eapply T_Var | eapply T_Var | apply sig_whole ] | apply sig_cmp ].
  all: first [ solve_uniq
             | (unfold binds; simpl; destruct (x == x); [ reflexivity | congruence ])
             | apply inst_mono_self | reflexivity | exact I | constructor ].
Qed.
