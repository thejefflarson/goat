(* Unit, strings, [if], the operators on Int, Float, String and Bool, and the
   Int-to-Float coercion: worked examples (docs/semantics.md sections 4, 6 and
   9, ADR 0017, ADR 0036).  Programs the rules accept type and run; programs
   they reject have no derivation.  The accepted examples fail to compile if a
   rule is dropped, and the rejected ones if a rule is loosened. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatLit.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* Integer arguments of the constructors below are written as numerals. *)
Arguments bs_ring_int o a%_znum_scope b%_znum_scope _ _.
Arguments bs_whole o a%_znum_scope b%_znum_scope _ _ _.
Arguments bs_cmp_int o a%_znum_scope b%_znum_scope _.
Arguments bt_ring_overflow o a%_znum_scope b%_znum_scope _ _.
Arguments bt_whole_overflow o a%_znum_scope b%_znum_scope _ _ _.
Arguments st_tofloat z%_znum_scope d.

(* ---- inversion for the literals, used by the rejections below ---- *)

Lemma str_inv : forall D G q T, typing D G (e_str q) T -> teq typ_String T.
Proof.
  intros D G q T H. remember (e_str q) as e0 eqn:He.
  induction H; try discriminate He.
  - eapply teq_trans; [ apply IHtyping; exact He | assumption ].
  - apply teq_refl.
Qed.

Lemma true_inv : forall D G T, typing D G e_true T -> teq typ_Bool T.
Proof.
  intros D G T H. remember e_true as e0 eqn:He.
  induction H; try discriminate He.
  - apply teq_refl.
  - eapply teq_trans; [ apply IHtyping; exact He | assumption ].
Qed.

(* What an operator's signature rules out, after the operand types are known. *)
Ltac sig_absurd Hs :=
  inversion Hs; subst;
  repeat match goal with
         | H : cmp_typ _ |- _ => inversion H; subst; clear H
         end;
  simpl in *;
  first [ discriminate | congruence ].

(* A type [T] equal to a known head is that head. *)
Ltac head_eq H :=
  first [ apply teq_Int_inv in H | apply teq_Float_inv in H
        | apply teq_Bool_inv in H | apply teq_String_inv in H ].

(* ---- accepted ---- *)

(* 1.5 / 2.5 is a Float *)
Example quot_types : typing d_any nil (e_bin (e_dec 0) bop_div (e_dec 1)) typ_Float.
Proof.
  eapply T_Bin; [ apply T_Dec | apply T_Dec | apply sig_quot ]; constructor.
Qed.

(* 1 - 2 is an Int *)
Example sub_types : typing d_any nil (e_bin (e_num 1) bop_sub (e_num 2)) typ_Int.
Proof.
  eapply T_Bin; [ apply T_Num | apply T_Num | apply sig_ring ]; first [ constructor | reflexivity | exact I ].
Qed.

(* 5 // 0 is an Int, and traps when it runs *)
Example floor_division_types : typing d_any nil (e_bin (e_num 5) bop_fdiv (e_num 0)) typ_Int.
Proof.
  eapply T_Bin; [ apply T_Num | apply T_Num | apply sig_whole ]; first [ constructor | reflexivity | exact I ].
Qed.

(* 7.5 // 2.5 and 7.5 % 2.5 are Floats *)
Example float_floor_division_types :
  typing d_any nil (e_bin (e_dec 0) bop_fdiv (e_dec 1)) typ_Float /\
  typing d_any nil (e_bin (e_dec 0) bop_rem (e_dec 1)) typ_Float.
Proof.
  split; (eapply T_Bin; [ apply T_Dec | apply T_Dec | apply sig_whole ]; first [ constructor | reflexivity | exact I ]).
Qed.

(* 7 / 2 is a Float: elaboration coerces both Ints, so the quotient is Float / Float *)
Example int_quotient_types :
  typing d_any nil (e_bin (e_tofloat (e_num 7)) bop_div (e_tofloat (e_num 2))) typ_Float.
Proof.
  eapply T_Bin;
    [ apply T_ToFloat with (A := typ_Int); [ apply T_Num | exact I ] | apply T_ToFloat with (A := typ_Int); [ apply T_Num | exact I ]
    | apply sig_quot ];
    first [ constructor | exact I ].
Qed.

(* 1 + 1.5 is a Float: elaboration coerces the Int *)
Example mixed_sum_types :
  typing d_any nil (e_bin (e_tofloat (e_num 1)) bop_add (e_dec 0)) typ_Float.
Proof.
  eapply T_Bin; [ apply T_ToFloat with (A := typ_Int); [ apply T_Num | exact I ] | apply T_Dec | apply sig_ring ];
    first [ reflexivity | constructor | exact I ].
Qed.

(* 1 < 1.5: a comparison coerces the Int *)
Example mixed_comparison_types :
  typing d_any nil (e_bin (e_tofloat (e_num 1)) bop_lt (e_dec 0)) typ_Bool.
Proof.
  eapply T_Bin; [ apply T_ToFloat with (A := typ_Int); [ apply T_Num | exact I ] | apply T_Dec | apply sig_cmp ];
    first [ constructor | reflexivity | exact I ].
Qed.

(* (program(x) do x + 1.5 done)(1): the checker accepts an Int for a Float
   parameter, and elaboration writes float(1) at the call *)
Example call_coerces_its_argument :
  typing d_any nil
    (e_app (e_abs (e_bin (e_fvar_b 0) bop_add (e_dec 0))) (e_tofloat (e_num 1)))
    typ_Float.
Proof.
  eapply T_App; [ | apply T_ToFloat with (A := typ_Int); [ apply T_Num; first [ constructor | exact I ] | exact I ] ].
  apply T_Abs with (L := {}). intros x Hx.
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
  eapply T_Bin; [ eapply T_Var | apply T_Dec | apply sig_ring ].
  all: first [ solve_uniq
             | (unfold binds; simpl; destruct (x == x); [ reflexivity | congruence ])
             | apply inst_mono_self | reflexivity | exact I ].
Qed.

Example unit_types : typing d_any nil e_unit typ_Unit.
Proof. apply T_Unit; constructor. Qed.

(* "a" < "b" *)
Example string_order_types :
  typing d_any nil (e_bin (e_str [97]) bop_lt (e_str [98])) typ_Bool.
Proof.
  eapply T_Bin; [ apply T_Str | apply T_Str | apply sig_cmp ];
    first [ constructor | reflexivity ].
Qed.

(* false < true *)
Example bool_order_types : typing d_any nil (e_bin e_false bop_lt e_true) typ_Bool.
Proof.
  eapply T_Bin; [ apply T_False | apply T_True | apply sig_cmp ];
    first [ constructor | reflexivity ].
Qed.

(* ---- they run ---- *)

(* The largest Int plus 0 stays an Int *)
Example largest_int_fits :
  bin_step bop_add (e_num 9223372036854775807) (e_num 0) (e_num 9223372036854775807).
Proof.
  pose proof (bs_ring_int bop_add 9223372036854775807 0 eq_refl eq_refl) as H. exact H.
Qed.

(* 1 - 2 == -1: integers are signed *)
Example subtraction_goes_negative :
  bin_step bop_sub (e_num 1) (e_num 2) (e_num (-1)).
Proof.
  pose proof (bs_ring_int bop_sub 1 2 eq_refl eq_refl) as H. exact H.
Qed.

(* The smallest Int times 1 stays an Int; the smallest Int % -1 is 0 *)
Example smallest_int_fits :
  bin_step bop_mul (e_num (-9223372036854775808)) (e_num 1) (e_num (-9223372036854775808)).
Proof.
  pose proof (bs_ring_int bop_mul (-9223372036854775808) 1 eq_refl eq_refl) as H. exact H.
Qed.

Example smallest_int_remainder_fits :
  bin_step bop_rem (e_num (-9223372036854775808)) (e_num (-1)) (e_num 0).
Proof.
  pose proof (bs_whole bop_rem (-9223372036854775808) (-1) eq_refl eq_refl eq_refl) as H.
  exact H.
Qed.

(* 7 // 2 == 3, -7 // 2 == -4 and -7 % 3 == 2: floor division and the sign of
   the divisor *)
Example floor_division_runs : bin_step bop_fdiv (e_num 7) (e_num 2) (e_num 3).
Proof.
  pose proof (bs_whole bop_fdiv 7 2 eq_refl eq_refl eq_refl) as H. exact H.
Qed.

Example floor_division_rounds_down :
  bin_step bop_fdiv (e_num (-7)) (e_num 2) (e_num (-4)).
Proof.
  pose proof (bs_whole bop_fdiv (-7) 2 eq_refl eq_refl eq_refl) as H. exact H.
Qed.

Example remainder_takes_the_divisors_sign :
  bin_step bop_rem (e_num (-7)) (e_num 3) (e_num 2).
Proof.
  pose proof (bs_whole bop_rem (-7) 3 eq_refl eq_refl eq_refl) as H. exact H.
Qed.

(* A Float operation is unspecified: any Float, so the model fixes no rounding,
   infinity or NaN.  A quotient by a zero Float is an ordinary Float step. *)
Example float_sum_is_any_float : forall x y d,
  bin_step bop_add (e_dec x) (e_dec y) (e_dec d).
Proof. intros. apply bs_float; [ left; reflexivity | constructor ]. Qed.

Example float_floor_division_and_remainder_are_any_float : forall x y d,
  bin_step bop_fdiv (e_dec x) (e_dec y) (e_dec d) /\
  bin_step bop_rem (e_dec x) (e_dec y) (e_dec d).
Proof. intros. split; apply bs_whole_float; [ reflexivity | constructor | reflexivity | constructor ]. Qed.

Example float_division_by_zero_is_not_a_trap : forall x y d,
  bin_step bop_div (e_dec x) (e_dec y) (e_dec d).
Proof. intros. apply bs_float; [ right; reflexivity | constructor ]. Qed.

(* A comparison of two Floats is unspecified: either Bool *)
Example float_comparison_is_either_bool : forall x y c,
  bin_step bop_lt (e_dec x) (e_dec y) (of_bool c).
Proof. intros. apply bs_cmp_float; [ reflexivity | constructor ]. Qed.

(* The Int comparison is exact *)
Example int_comparison_runs : bin_step bop_lt (e_num 1) (e_num 2) e_true.
Proof. pose proof (bs_cmp_int bop_lt 1 2 eq_refl) as H. exact H. Qed.

(* float(n) steps to a Float, and takes a step before its operand is a value *)
Example coercion_runs : forall d, step (e_tofloat (e_num 3)) (e_dec d).
Proof. intros d. apply st_tofloat. Qed.

Example coercion_steps_its_operand :
  step (e_tofloat (e_bin (e_num 1) bop_add (e_num 2))) (e_tofloat (e_num 3)).
Proof.
  apply st_tofloat1. apply st_bin; [ constructor | constructor | ].
  pose proof (bs_ring_int bop_add 1 2 eq_refl eq_refl) as H. exact H.
Qed.

(* a prefix comes before the longer string; the first differing byte decides *)
Example prefix_orders_first :
  bin_step bop_lt (e_str [97]) (e_str [97; 98]) e_true.
Proof. pose proof (bs_cmp_str bop_lt [97] [97; 98] eq_refl) as H. exact H. Qed.

Example first_byte_decides :
  bin_step bop_gt (e_str [98]) (e_str [97; 122]) e_true.
Proof. pose proof (bs_cmp_str bop_gt [98] [97; 122] eq_refl) as H. exact H. Qed.

Example false_before_true : bin_step bop_lt e_false e_true e_true.
Proof. pose proof (bs_cmp_bool bop_lt e_false e_true false true eq_refl eq_refl eq_refl) as H. exact H. Qed.

Example unequal_strings : bin_step bop_ne (e_str [1]) (e_str [2]) e_true.
Proof. pose proof (bs_cmp_str bop_ne [1] [2] eq_refl) as H. exact H. Qed.

(* if 1 < 2 then 10 else 20 runs to 10 *)
Example if_runs :
  multistep (e_ite (e_bin (e_num 1) bop_lt (e_num 2)) (e_num 10) (e_num 20)) (e_num 10).
Proof.
  eapply ms_step.
  - apply st_ite1. apply st_bin; [ constructor | constructor | ].
    pose proof (bs_cmp_int bop_lt 1 2 eq_refl) as H. exact H.
  - cbn. eapply ms_step; [ apply st_ite_true | apply ms_refl ].
Qed.

(* ---- they trap ---- *)

(* 5 // 0 traps with a division by zero, and does not step *)
Example floor_division_by_zero_traps :
  traps (e_bin (e_num 5) bop_fdiv (e_num 0)) trap_div_zero.
Proof.
  apply tr_bin; [ constructor | constructor | apply bt_div_zero; reflexivity ].
Qed.

Example remainder_by_zero_traps :
  traps (e_bin (e_num 5) bop_rem (e_num 0)) trap_div_zero.
Proof.
  apply tr_bin; [ constructor | constructor | apply bt_div_zero; reflexivity ].
Qed.

(* The largest Int plus 1 leaves the 64-bit range: it traps *)
Example addition_overflow_traps :
  traps (e_bin (e_num 9223372036854775807) bop_add (e_num 1)) trap_overflow.
Proof.
  apply tr_bin; [ constructor | constructor | ].
  apply (bt_ring_overflow bop_add 9223372036854775807 1); reflexivity.
Qed.

(* The smallest Int minus 1 likewise *)
Example subtraction_overflow_traps :
  traps (e_bin (e_num (-9223372036854775808)) bop_sub (e_num 1)) trap_overflow.
Proof.
  apply tr_bin; [ constructor | constructor | ].
  apply (bt_ring_overflow bop_sub (-9223372036854775808) 1); reflexivity.
Qed.

Example multiplication_overflow_traps :
  traps (e_bin (e_num 9223372036854775807) bop_mul (e_num 2)) trap_overflow.
Proof.
  apply tr_bin; [ constructor | constructor | ].
  apply (bt_ring_overflow bop_mul 9223372036854775807 2); reflexivity.
Qed.

(* The smallest Int // -1 is the one quotient that does not fit *)
Example floor_division_overflow_traps :
  traps (e_bin (e_num (-9223372036854775808)) bop_fdiv (e_num (-1))) trap_overflow.
Proof.
  apply tr_bin; [ constructor | constructor | ].
  apply (bt_whole_overflow bop_fdiv (-9223372036854775808) (-1)); reflexivity.
Qed.

Example floor_division_by_zero_does_not_step : forall e',
  ~ step (e_bin (e_num 5) bop_fdiv (e_num 0)) e'.
Proof.
  intros e' H. inversion H; subst.
  - match goal with Hs : step (e_num _) _ |- _ => inversion Hs end.
  - match goal with Hs : step (e_num _) _ |- _ => inversion Hs end.
  - match goal with Hb : bin_step _ _ _ _ |- _ => inversion Hb; subst end;
      first [ discriminate | (vm_compute in *; discriminate)
            | (match goal with Hf : fl_pair _ _ |- _ => inversion Hf end)
            | (match goal with Hd : _ \/ _ |- _ => destruct Hd; vm_compute in *; discriminate end) ].
Qed.

Example addition_overflow_does_not_step : forall e',
  ~ step (e_bin (e_num 9223372036854775807) bop_add (e_num 1)) e'.
Proof.
  intros e' H. inversion H; subst.
  - match goal with Hs : step (e_num _) _ |- _ => inversion Hs end.
  - match goal with Hs : step (e_num _) _ |- _ => inversion Hs end.
  - match goal with Hb : bin_step _ _ _ _ |- _ => inversion Hb; subst end;
      first [ discriminate | (vm_compute in *; discriminate)
            | (match goal with Hf : fl_pair _ _ |- _ => inversion Hf end)
            | (match goal with Hd : _ \/ _ |- _ => destruct Hd; vm_compute in *; discriminate end) ].
Qed.

(* 1 + (5 // 0): the trap rises out of the right operand *)
Example trap_rises_through_an_operator :
  traps (e_bin (e_num 1) bop_add (e_bin (e_num 5) bop_fdiv (e_num 0))) trap_div_zero.
Proof.
  apply tr_bin2; [ constructor | apply floor_division_by_zero_traps ].
Qed.

(* float(5 // 0): the trap rises out of a coercion *)
Example trap_rises_through_a_coercion :
  traps (e_tofloat (e_bin (e_num 5) bop_fdiv (e_num 0))) trap_div_zero.
Proof. apply tr_tofloat. apply floor_division_by_zero_traps. Qed.

(* ---- accepted by the unsugared rules ---- *)

(* 1 + 1.5 with no coercion is a Float: the numeral is typed at [Float], a
   [Literal] type, so the operands agree *)
Example uncoerced_mixed_sum_types :
  typing d_any nil (e_bin (e_num 1) bop_add (e_dec 0)) typ_Float.
Proof.
  eapply T_Bin; [ apply T_Num | apply T_Dec | apply sig_ring ];
    first [ reflexivity | constructor | exact I ].
Qed.

(* float(true): the coercion takes a number *)
Example coercion_of_bool_rejected : forall T,
  ~ typing d_any nil (e_tofloat e_true) T.
Proof.
  intros T H. destruct (tofloat_inv _ _ _ _ H) as [A [H1 [Hs _]]].
  apply true_inv in H1. head_eq H1. subst A. simpl in Hs. discriminate.
Qed.

(* float(1.5) is the Float itself: the coercion is the identity on a Float *)
Example coercion_of_float_types :
  typing d_any nil (e_tofloat (e_dec 0)) typ_Float.
Proof. apply T_ToFloat with (A := typ_Float); [ apply T_Dec; constructor | exact I ]. Qed.

Example coercion_of_float_runs : forall d, step (e_tofloat (e_dec d)) (e_dec d).
Proof. intros d. apply st_tofloat_dec. Qed.

(* 1 < "a": a number does not meet a string *)
Example mixed_comparison_rejected : forall T,
  ~ typing d_any nil (e_bin (e_num 1) bop_lt (e_str [97])) T.
Proof.
  intros T H. destruct (bin_inv _ _ _ _ _ _ H) as [A [B [R [H1 [H2 [Hs _]]]]]].
  apply str_inv in H2. head_eq H2. subst B.
  inversion Hs; subst;
    first [ (apply num_inv in H1; simpl in H1; discriminate) | (simpl in *; discriminate) | congruence ].
Qed.

(* true + true: arithmetic wants numbers *)
Example boolean_arithmetic_rejected : forall T,
  ~ typing d_any nil (e_bin e_true bop_add e_true) T.
Proof.
  intros T H. destruct (bin_inv _ _ _ _ _ _ H) as [A [B [R [H1 [H2 [Hs _]]]]]].
  apply true_inv in H1. head_eq H1. subst A. sig_absurd Hs.
Qed.

(* if 1 then 2 else 3: the condition is a number *)
Example number_condition_rejected : forall T,
  ~ typing d_any nil (e_ite (e_num 1) (e_num 2) (e_num 3)) T.
Proof.
  intros T H. destruct (ite_inv _ _ _ _ _ _ H) as [T' [H1 _]].
  apply num_inv in H1. simpl in H1. discriminate.
Qed.

(* if true then 1 else 2.5 done is a Float: the numeral takes the branch's type *)
Example int_branch_against_float_types :
  typing d_any nil (e_ite e_true (e_num 1) (e_dec 0)) typ_Float.
Proof.
  apply T_If; [ apply T_True; constructor | apply T_Num; first [ constructor | exact I ]
              | apply T_Dec; constructor ].
Qed.

(* ---- generic operators: sorted type variables (ADR 0037) ---- *)

Definition ga : atom := fresh nil.

(* Every variable a [let] generalizes below is a numeral's: [Literal]. *)
Definition k_lit : sort_fn := fun _ => k_Literal.

Lemma inst_at_lit : forall U,
  sat d_any k_Literal U -> lct 0 U ->
  inst d_any (typ_Arrow U U) (gen nil (typ_Arrow (typ_Var ga) (typ_Var ga)) k_lit).
Proof.
  intros U HU HL.
  exists (fun a => if a == ga then U else typ_Var a), idr.
  split; [ | split; [ | split; [ | split ] ] ].
  - intros a Ha. simpl in Ha. destruct (a == ga) as [E|E];
      [ subst; exfalso; apply Ha; fsetdec | reflexivity ].
  - intros r _. reflexivity.
  - simpl. destruct (ga == ga) as [E|E]; [ reflexivity | congruence ].
  - intros a Ha. simpl in Ha. apply AtomSetFacts.diff_iff in Ha as [Ha _].
    simpl in Ha. assert (a = ga) by fsetdec. subst a.
    destruct (ga == ga) as [E|E]; [ exact HU | congruence ].
  - split; [ intros a; simpl; match goal with |- context [if ?c then _ else _] => destruct c end; [ exact HL | exact I ] | intros r; exact I ].
Qed.

(* A function that multiplies by a numeral is generic over [Literal]: a string
   instance of its scheme does not exist. *)
Example generic_scheme_rejects_strings :
  ~ inst d_any (typ_Arrow typ_String typ_String)
      (gen nil (typ_Arrow (typ_Var ga) (typ_Var ga)) k_lit).
Proof.
  intros [st [sr [Hst [Hsr [Heq [Hsat _]]]]]]. simpl in Heq.
  injection Heq as Hs _.
  assert (Hin : ga `in` AtomSetImpl.diff (ftv_typ (typ_Arrow (typ_Var ga) (typ_Var ga))) {})
    by (simpl; apply AtomSetFacts.diff_iff; split; [ fsetdec | fsetdec ]).
  pose proof (Hsat ga Hin) as H. cbn [gen s_sk s_tq] in H. rewrite <- Hs in H. simpl in H. discriminate.
Qed.

(* let double = program(x) do x * 2 done, then {0: double(1), 1: double(1.5)} *)
Definition double_pair : exp :=
  e_let (e_abs (e_bin (e_fvar_b 0) bop_mul (e_num 2)))
        (e_rec (fs_cons 0 (e_app (e_fvar_b 0) (e_num 1))
               (fs_cons 1 (e_app (e_fvar_b 0) (e_dec 0)) fs_nil))).

Example generic_function_is_used_at_int_and_float :
  typing d_any nil double_pair
    (typ_Record (row_Ext 0 typ_Int (row_Ext 1 typ_Float row_Empty))).
Proof.
  unfold double_pair.
  apply T_Let with (L := {}) (T1 := typ_Arrow (typ_Var ga) (typ_Var ga)) (k := k_lit);
    [ reflexivity | | ].
  - apply T_Abs with (L := {}). intros x Hx.
    cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
    assert (Hga : ga `in` AtomSetImpl.diff (ftv_typ (typ_Arrow (typ_Var ga) (typ_Var ga))) (ftv_ctx nil))
      by (simpl; apply AtomSetFacts.diff_iff; split; [ fsetdec | fsetdec ]).
    assert (Hs : forall k0, finer k_Literal k0 ->
               sat (ext d_any (AtomSetImpl.diff (ftv_typ (typ_Arrow (typ_Var ga) (typ_Var ga))) (ftv_ctx nil)) k_lit)
                   k0 (typ_Var ga)).
    { intros k0 Hf. cbn [sat]. rewrite (ext_in _ _ _ ga Hga). exact Hf. }
    eapply T_Bin; [ | | apply sig_ring ].
    + apply T_Var with (s := sch_mono (typ_Var ga));
        [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_mono_self ].
    + apply T_Num; [ solve_uniq | apply Hs; apply finer_refl ].
    + reflexivity.
    + apply Hs. apply finer_lit.
  - intros f Hf.
    cbn [open_exp_wrt_exp open_exp_wrt_exp_rec open_fields_wrt_exp_rec].
    apply T_Record. eapply FT_cons.
    + eapply T_App; [ | apply T_Num; [ solve_uniq | ] ].
      * apply T_Var with (s := gen nil (typ_Arrow (typ_Var ga) (typ_Var ga)) k_lit);
          [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_at_lit; exact I ].
      * exact I.
    + eapply FT_cons; [ | apply FT_nil; solve_uniq ].
      eapply T_App; [ | apply T_Dec; solve_uniq ].
      apply T_Var with (s := gen nil (typ_Arrow (typ_Var ga) (typ_Var ga)) k_lit);
        [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_at_lit; exact I ].
Qed.

(* let n = 1 in n, or n = -3: a numeral binding is generic, so it is an Int or a Float
   as its use asks.  Which one an unconstrained use takes is the elaborator's
   choice at the program judgment (ADR 0017 defaults to Int). *)
Lemma numeral_binding_at : forall n U,
  sat d_any k_Literal U -> lct 0 U ->
  typing d_any nil (e_let (e_num n) (e_fvar_b 0)) U.
Proof.
  intros n U HU HL.
  apply T_Let with (L := {}) (T1 := typ_Var ga) (k := k_lit); [ reflexivity | | ].
  - apply T_Num; [ constructor | ].
    cbn [sat]. rewrite (ext_in _ _ _ ga).
    + apply finer_refl.
    + simpl. apply AtomSetFacts.diff_iff. split; [ fsetdec | fsetdec ].
  - intros f Hf. cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
    apply T_Var with (s := gen nil (typ_Var ga) k_lit);
      [ solve_uniq | apply binds_cons_2; reflexivity | ].
    exists (fun a => if a == ga then U else typ_Var a), idr.
    split; [ | split; [ | split; [ | split ] ] ].
    + intros a Ha. simpl in Ha. destruct (a == ga) as [E|E];
        [ subst; exfalso; apply Ha; fsetdec | reflexivity ].
    + intros r _. reflexivity.
    + simpl. destruct (ga == ga) as [E|E]; [ reflexivity | congruence ].
    + intros a Ha. simpl in Ha. apply AtomSetFacts.diff_iff in Ha as [Ha _].
      simpl in Ha. assert (a = ga) by fsetdec. subst a.
      destruct (ga == ga) as [E|E]; [ exact HU | congruence ].
    + split; [ intros a; simpl; match goal with |- context [if ?c then _ else _] => destruct c end; [ exact HL | exact I ] | intros r; exact I ].
Qed.

Example numeral_binding_is_generic :
  typing d_any nil (e_let (e_num 1) (e_fvar_b 0)) typ_Int /\
  typing d_any nil (e_let (e_num 1) (e_fvar_b 0)) typ_Float.
Proof. split; apply numeral_binding_at; exact I. Qed.

(* A negative literal is one numeral too: the checker lowers -3 to it, not to
   0 - 3. *)
Example negative_numeral_binding_is_generic :
  typing d_any nil (e_let (e_num (-3)) (e_fvar_b 0)) typ_Int /\
  typing d_any nil (e_let (e_num (-3)) (e_fvar_b 0)) typ_Float.
Proof. split; apply numeral_binding_at; exact I. Qed.

Lemma inst_numeral_at : forall U,
  sat d_any k_Literal U ->
  inst d_any U (gen nil (typ_Var ga) k_lit).
Proof.
  intros U HU.
  exists (fun a => if a == ga then U else typ_Var a), idr.
  split; [ | split; [ | split; [ | split ] ] ].
  - intros a Ha. simpl in Ha. destruct (a == ga) as [E|E];
      [ subst; exfalso; apply Ha; fsetdec | reflexivity ].
  - intros r _. reflexivity.
  - simpl. destruct (ga == ga) as [E|E]; [ reflexivity | congruence ].
  - intros a Ha. simpl in Ha. apply AtomSetFacts.diff_iff in Ha as [Ha _].
    simpl in Ha. assert (a = ga) by fsetdec. subst a.
    destruct (ga == ga) as [E|E]; [ exact HU | congruence ].
  - split; [ | intros r; exact I ].
    intros a. simpl.
    match goal with |- context [if ?c then _ else _] => destruct c end;
      [ | exact I ].
    destruct U; first [ exact I | discriminate HU ].
Qed.

(* n = 3 {a: n + 1.5, b: n * 2}: the one numeral is a Float in the first field
   and an Int in the second, whichever order the fields are written in (the
   rules have no order; ADR 0039).  The checker accepts it the same way. *)
Example numeral_binding_adapts_in_one_record :
  typing d_any nil
    (e_let (e_num 3)
       (e_rec (fs_cons 0 (e_bin (e_fvar_b 0) bop_add (e_dec 0))
              (fs_cons 1 (e_bin (e_fvar_b 0) bop_mul (e_num 2)) fs_nil))))
    (typ_Record (row_Ext 0 typ_Float (row_Ext 1 typ_Int row_Empty))).
Proof.
  apply T_Let with (L := {}) (T1 := typ_Var ga) (k := k_lit); [ reflexivity | | ].
  - apply T_Num; [ constructor | ].
    cbn [sat]. rewrite (ext_in _ _ _ ga).
    + apply finer_refl.
    + simpl. apply AtomSetFacts.diff_iff. split; [ fsetdec | fsetdec ].
  - intros f Hf. cbn [open_exp_wrt_exp open_exp_wrt_exp_rec open_fields_wrt_exp_rec].
    apply T_Record. eapply FT_cons.
    + eapply T_Bin with (A := typ_Float); [ | apply T_Dec; solve_uniq | apply sig_ring ].
      * apply T_Var with (s := gen nil (typ_Var ga) k_lit);
          [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_numeral_at; exact I ].
      * reflexivity.
      * exact I.
    + eapply FT_cons; [ | apply FT_nil; solve_uniq ].
      eapply T_Bin with (A := typ_Int) (B := typ_Int); [ | apply T_Num; [ solve_uniq | exact I ] | apply sig_ring ].
      * apply T_Var with (s := gen nil (typ_Var ga) k_lit);
          [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_numeral_at; exact I ].
      * reflexivity.
      * exact I.
Qed.

(* A generic function runs as the concrete one: (program(x) do x * 2 done)(1.5)
   multiplies two Floats, and two bare numerals multiply as Ints. *)
Example generic_call_on_a_decimal_runs : forall d,
  bin_step bop_mul (e_dec d) (e_num 2) (e_dec d).
Proof. intros d. apply bs_float; [ left; reflexivity | constructor ]. Qed.

Example generic_call_on_numerals_runs :
  bin_step bop_mul (e_num 3) (e_num 2) (e_num 6).
Proof. pose proof (bs_ring_int bop_mul 3 2 eq_refl eq_refl) as H. exact H. Qed.

(* ---- the inference algorithm accepts and rejects them ---- *)

(* A numeral gets a fresh sorted variable, and Metalib's atoms are opaque to
   computation, so the examples with numerals are not run here; the
   differential test runs the extracted algorithm on them (differential/README.md). *)

Example infer_if_branches :
  infer_closed 20 (e_ite (e_bin (e_str [97]) bop_lt (e_str [98])) e_unit e_unit)
  = Some typ_Unit.
Proof. vm_compute. reflexivity. Qed.
