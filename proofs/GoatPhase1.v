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

Lemma num_inv : forall G n T, typing G (e_num n) T -> teq typ_Int T.
Proof.
  intros G n T H. remember (e_num n) as e0 eqn:He.
  induction H; try discriminate He.
  - apply teq_refl.
  - eapply teq_trans; [ apply IHtyping; exact He | assumption ].
Qed.

Lemma dec_inv : forall G d T, typing G (e_dec d) T -> teq typ_Float T.
Proof.
  intros G d T H. remember (e_dec d) as e0 eqn:He.
  induction H; try discriminate He.
  - apply teq_refl.
  - eapply teq_trans; [ apply IHtyping; exact He | assumption ].
Qed.

Lemma str_inv : forall G q T, typing G (e_str q) T -> teq typ_String T.
Proof.
  intros G q T H. remember (e_str q) as e0 eqn:He.
  induction H; try discriminate He.
  - eapply teq_trans; [ apply IHtyping; exact He | assumption ].
  - apply teq_refl.
Qed.

Lemma true_inv : forall G T, typing G e_true T -> teq typ_Bool T.
Proof.
  intros G T H. remember e_true as e0 eqn:He.
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
  first [ discriminate | congruence ].

(* A type [T] equal to a known head is that head. *)
Ltac head_eq H :=
  first [ apply teq_Int_inv in H | apply teq_Float_inv in H
        | apply teq_Bool_inv in H | apply teq_String_inv in H ].

(* ---- accepted ---- *)

(* 1.5 / 2.5 is a Float *)
Example quot_types : typing nil (e_bin (e_dec 0) bop_div (e_dec 1)) typ_Float.
Proof.
  eapply T_Bin; [ apply T_Dec | apply T_Dec | apply sig_quot ]; constructor.
Qed.

(* 1 - 2 is an Int *)
Example sub_types : typing nil (e_bin (e_num 1) bop_sub (e_num 2)) typ_Int.
Proof.
  eapply T_Bin; [ apply T_Num | apply T_Num | apply sig_ring_int ]; constructor || reflexivity.
Qed.

(* 5 // 0 is an Int, and traps when it runs *)
Example floor_division_types : typing nil (e_bin (e_num 5) bop_fdiv (e_num 0)) typ_Int.
Proof.
  eapply T_Bin; [ apply T_Num | apply T_Num | apply sig_whole ]; constructor || reflexivity.
Qed.

(* 7 / 2 is a Float: elaboration coerces both Ints, so the quotient is Float / Float *)
Example int_quotient_types :
  typing nil (e_bin (e_tofloat (e_num 7)) bop_div (e_tofloat (e_num 2))) typ_Float.
Proof.
  eapply T_Bin;
    [ apply T_ToFloat; apply T_Num | apply T_ToFloat; apply T_Num | apply sig_quot ];
    constructor.
Qed.

(* 1 + 1.5 is a Float: elaboration coerces the Int *)
Example mixed_sum_types :
  typing nil (e_bin (e_tofloat (e_num 1)) bop_add (e_dec 0)) typ_Float.
Proof.
  eapply T_Bin; [ apply T_ToFloat; apply T_Num | apply T_Dec | apply sig_ring_float ];
    first [ reflexivity | constructor ].
Qed.

(* 1 < 1.5: a comparison coerces the Int *)
Example mixed_comparison_types :
  typing nil (e_bin (e_tofloat (e_num 1)) bop_lt (e_dec 0)) typ_Bool.
Proof.
  eapply T_Bin; [ apply T_ToFloat; apply T_Num | apply T_Dec | apply sig_cmp ];
    constructor || reflexivity.
Qed.

(* (program(x) do x + 1.5 done)(1): the checker accepts an Int for a Float
   parameter, and elaboration writes float(1) at the call *)
Example call_coerces_its_argument :
  typing nil
    (e_app (e_abs (e_bin (e_fvar_b 0) bop_add (e_dec 0))) (e_tofloat (e_num 1)))
    typ_Float.
Proof.
  eapply T_App; [ | apply T_ToFloat; apply T_Num; constructor ].
  apply T_Abs with (L := {}). intros x Hx.
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
  eapply T_Bin; [ eapply T_Var | apply T_Dec | apply sig_ring_float ].
  all: first [ solve_uniq
             | (unfold binds; simpl; destruct (x == x); [ reflexivity | congruence ])
             | apply inst_mono_self | reflexivity ].
Qed.

Example unit_types : typing nil e_unit typ_Unit.
Proof. apply T_Unit; constructor. Qed.

(* "a" < "b" *)
Example string_order_types :
  typing nil (e_bin (e_str [97]) bop_lt (e_str [98])) typ_Bool.
Proof.
  eapply T_Bin; [ apply T_Str | apply T_Str | apply sig_cmp ];
    first [ constructor | reflexivity ].
Qed.

(* false < true *)
Example bool_order_types : typing nil (e_bin e_false bop_lt e_true) typ_Bool.
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
Proof. intros. apply bs_float. left. reflexivity. Qed.

Example float_division_by_zero_is_not_a_trap : forall x y d,
  bin_step bop_div (e_dec x) (e_dec y) (e_dec d).
Proof. intros. apply bs_float. right. reflexivity. Qed.

(* A comparison of two Floats is unspecified: either Bool *)
Example float_comparison_is_either_bool : forall x y c,
  bin_step bop_lt (e_dec x) (e_dec y) (of_bool c).
Proof. intros. apply bs_cmp_float. reflexivity. Qed.

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
      first [ discriminate | (vm_compute in *; discriminate) ].
Qed.

Example addition_overflow_does_not_step : forall e',
  ~ step (e_bin (e_num 9223372036854775807) bop_add (e_num 1)) e'.
Proof.
  intros e' H. inversion H; subst.
  - match goal with Hs : step (e_num _) _ |- _ => inversion Hs end.
  - match goal with Hs : step (e_num _) _ |- _ => inversion Hs end.
  - match goal with Hb : bin_step _ _ _ _ |- _ => inversion Hb; subst end;
      first [ discriminate | (vm_compute in *; discriminate) ].
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

(* ---- rejected ---- *)

(* 1.5 // 2: floor division wants whole numbers *)
Example float_floor_division_rejected : forall T,
  ~ typing nil (e_bin (e_dec 0) bop_fdiv (e_num 2)) T.
Proof.
  intros T H. destruct (bin_inv _ _ _ _ _ H) as [A [B [R [H1 [H2 [Hs _]]]]]].
  apply dec_inv in H1. head_eq H1. subst A. sig_absurd Hs.
Qed.

(* 1.5 % 2 likewise *)
Example float_remainder_rejected : forall T,
  ~ typing nil (e_bin (e_dec 0) bop_rem (e_num 2)) T.
Proof.
  intros T H. destruct (bin_inv _ _ _ _ _ H) as [A [B [R [H1 [H2 [Hs _]]]]]].
  apply dec_inv in H1. head_eq H1. subst A. sig_absurd Hs.
Qed.

(* 1 + 1.5 with no coercion has no derivation: the calculus has no mixed
   signature, so an Int meets a Float only through float(...) *)
Example uncoerced_mixed_sum_rejected : forall T,
  ~ typing nil (e_bin (e_num 1) bop_add (e_dec 0)) T.
Proof.
  intros T H. destruct (bin_inv _ _ _ _ _ H) as [A [B [R [H1 [H2 [Hs _]]]]]].
  apply num_inv in H1. head_eq H1. subst A.
  apply dec_inv in H2. head_eq H2. subst B. sig_absurd Hs.
Qed.

(* float(true), float(1.5): the coercion takes an Int *)
Example coercion_of_bool_rejected : forall T,
  ~ typing nil (e_tofloat e_true) T.
Proof.
  intros T H. destruct (tofloat_inv _ _ _ H) as [H1 _].
  apply true_inv in H1. head_eq H1. discriminate.
Qed.

Example coercion_of_float_rejected : forall T,
  ~ typing nil (e_tofloat (e_dec 0)) T.
Proof.
  intros T H. destruct (tofloat_inv _ _ _ H) as [H1 _].
  apply dec_inv in H1. head_eq H1. discriminate.
Qed.

(* 1 < "a": a number does not meet a string *)
Example mixed_comparison_rejected : forall T,
  ~ typing nil (e_bin (e_num 1) bop_lt (e_str [97])) T.
Proof.
  intros T H. destruct (bin_inv _ _ _ _ _ H) as [A [B [R [H1 [H2 [Hs _]]]]]].
  apply str_inv in H2. head_eq H2. subst B.
  apply num_inv in H1. head_eq H1. subst A. sig_absurd Hs.
Qed.

(* true + true: arithmetic wants numbers *)
Example boolean_arithmetic_rejected : forall T,
  ~ typing nil (e_bin e_true bop_add e_true) T.
Proof.
  intros T H. destruct (bin_inv _ _ _ _ _ H) as [A [B [R [H1 [H2 [Hs _]]]]]].
  apply true_inv in H1. head_eq H1. subst A. sig_absurd Hs.
Qed.

(* if 1 then 2 else 3: the condition is a number *)
Example number_condition_rejected : forall T,
  ~ typing nil (e_ite (e_num 1) (e_num 2) (e_num 3)) T.
Proof.
  intros T H. destruct (ite_inv _ _ _ _ _ H) as [T' [H1 _]].
  apply num_inv in H1. head_eq H1. discriminate.
Qed.

(* if true then 1 else 2.5 done: with no coercion the branches disagree *)
Example int_branch_against_float_rejected : forall T,
  ~ typing nil (e_ite e_true (e_num 1) (e_dec 0)) T.
Proof.
  intros T H. destruct (ite_inv _ _ _ _ _ H) as [T' [_ [H2 [H3 E]]]].
  apply num_inv in H2. apply dec_inv in H3.
  assert (Hf : teq typ_Float typ_Int)
    by (eapply teq_trans; [ exact H3 | apply teq_sym; exact H2 ]).
  apply teq_Float_inv in Hf. discriminate.
Qed.
