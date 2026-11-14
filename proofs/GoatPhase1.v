(* Unit, strings, [if], and the operators on Int, Float, String and Bool:
   worked examples (docs/semantics.md section 8, ADR 0017, ADR 0036).
   Programs the rules accept type and run; programs they reject have no
   derivation.  The accepted examples fail to compile if a rule is dropped, and
   the rejected ones if a rule is loosened.  Each example that has a goat
   source is checked against a release build of the compiler in the table in
   the pull request that introduced this file. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatLit.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSound.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* Integer arguments of the constructors below are written as numerals. *)
Arguments q_of_z z%_znum_scope.
Arguments nv_num z%_znum_scope.
Arguments bs_ring_int o a%_znum_scope b%_znum_scope _.
Arguments bs_whole o a%_znum_scope b%_znum_scope _ _.

(* ---- inversion for the literals, used by the rejections below ---- *)

Lemma num_inv : forall G n T,
  typing G (e_num n) T -> teq typ_Int T \/ teq typ_Float T.
Proof.
  intros G n T H. remember (e_num n) as e0 eqn:He.
  induction H; try discriminate He.
  - left. apply teq_refl.
  - right. apply teq_refl.
  - destruct (IHtyping He) as [H1 | H1]; [ left | right ]; eapply teq_trans; eassumption.
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
         | H : num_typ _ |- _ => inversion H; subst; clear H
         | H : base_typ _ |- _ => inversion H; subst; clear H
         | H : _ \/ _ |- _ => destruct H
         end;
  first [ discriminate | congruence ].

(* A type [T] equal to a known head is that head. *)
Ltac head_eq H :=
  first [ apply teq_Int_inv in H | apply teq_Float_inv in H
        | apply teq_Bool_inv in H | apply teq_String_inv in H ].

(* ---- accepted ---- *)

(* 7 / 2 is a Float *)
Example quot_types : typing nil (e_bin (e_num 7) bop_div (e_num 2)) typ_Float.
Proof.
  eapply T_Bin; [ apply T_Num | apply T_Num | apply sig_quot ]; constructor.
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

(* 1 + 1.5 is a Float: an Int meets a Float *)
Example mixed_sum_types :
  typing nil (e_bin (e_num 1) bop_add (e_dec (dec_of_q (q_of_ratio 3 2)))) typ_Float.
Proof.
  eapply T_Bin; [ apply T_Num | apply T_Dec | apply sig_ring_float ];
    first [ reflexivity | (right; reflexivity) | constructor ].
Qed.

(* 1 < 1.5: a comparison widens the Int *)
Example mixed_comparison_types :
  typing nil (e_bin (e_num 1) bop_lt (e_dec (dec_of_q (q_of_ratio 3 2)))) typ_Bool.
Proof.
  eapply T_Bin; [ apply T_Num | apply T_Dec | apply sig_cmp_num ]; constructor || reflexivity.
Qed.

(* if true then 1 else 2.5 done: the whole-number literal settles as a Float *)
Example literal_settles_as_float :
  typing nil (e_ite e_true (e_num 1) (e_dec (dec_of_q (q_of_ratio 5 2)))) typ_Float.
Proof.
  apply T_If; [ apply T_True | apply T_NumFloat | apply T_Dec ]; constructor.
Qed.

Example unit_types : typing nil e_unit typ_Unit.
Proof. apply T_Unit; constructor. Qed.

(* "a" < "b" *)
Example string_order_types :
  typing nil (e_bin (e_str [97]) bop_lt (e_str [98])) typ_Bool.
Proof.
  eapply T_Bin; [ apply T_Str | apply T_Str | apply sig_cmp_base ];
    first [ constructor | reflexivity ].
Qed.

(* false < true *)
Example bool_order_types : typing nil (e_bin e_false bop_lt e_true) typ_Bool.
Proof.
  eapply T_Bin; [ apply T_False | apply T_True | apply sig_cmp_base ];
    first [ constructor | reflexivity ].
Qed.

(* ---- they run ---- *)

(* 7 / 2 == 3.5 *)
Example quotient_runs :
  bin_step bop_div (e_num 7) (e_num 2) (e_dec (dec_of_q (q_of_ratio 7 2))).
Proof. eapply bs_quot; [ apply nv_num | apply nv_num | reflexivity ]. Qed.

Example quotient_is_three_and_a_half :
  q_cmp (q_of_ratio 7 2) (q_of_ratio 35 10) = Eq.
Proof. reflexivity. Qed.

(* 1 - 2 == -1: integers are signed *)
Example subtraction_goes_negative :
  bin_step bop_sub (e_num 1) (e_num 2) (e_num (-1)).
Proof.
  pose proof (bs_ring_int bop_sub 1 2 eq_refl) as H. exact H.
Qed.

(* 7 // 2 == 3, -7 // 2 == -4 and -7 % 3 == 2: floor division and the sign of
   the divisor *)
Example floor_division_runs : bin_step bop_fdiv (e_num 7) (e_num 2) (e_num 3).
Proof.
  pose proof (bs_whole bop_fdiv 7 2 eq_refl eq_refl) as H. exact H.
Qed.

Example floor_division_rounds_down :
  bin_step bop_fdiv (e_num (-7)) (e_num 2) (e_num (-4)).
Proof.
  pose proof (bs_whole bop_fdiv (-7) 2 eq_refl eq_refl) as H. exact H.
Qed.

Example remainder_takes_the_divisors_sign :
  bin_step bop_rem (e_num (-7)) (e_num 3) (e_num 2).
Proof.
  pose proof (bs_whole bop_rem (-7) 3 eq_refl eq_refl) as H. exact H.
Qed.

(* 1 + 1.5 == 2.5 *)
Example mixed_sum_runs :
  bin_step bop_add (e_num 1) (e_dec (dec_of_q (q_of_ratio 3 2)))
    (e_dec (dec_of_q (q_of_ratio 5 2))).
Proof.
  eapply bs_ring_float with (p := q_of_z 1) (q := q_of_dec (dec_of_q (q_of_ratio 3 2)));
    [ reflexivity | apply nv_num | apply nv_dec | intros [a [b [E1 E2]]]; discriminate ].
Qed.

(* 1 < 1.5, 2 == 2.0, 1 != 1.5 *)
Example mixed_less_runs :
  bin_step bop_lt (e_num 1) (e_dec (dec_of_q (q_of_ratio 3 2))) e_true.
Proof.
  pose proof (bs_cmp_num bop_lt (e_num 1) (e_dec (dec_of_q (q_of_ratio 3 2)))
    (q_of_z 1) (q_of_dec (dec_of_q (q_of_ratio 3 2))) eq_refl (nv_num 1) (nv_dec _)) as H.
  exact H.
Qed.

Example whole_equals_decimal :
  bin_step bop_eq (e_num 2) (e_dec (dec_of_q (q_of_ratio 4 2))) e_true.
Proof.
  pose proof (bs_cmp_num bop_eq (e_num 2) (e_dec (dec_of_q (q_of_ratio 4 2)))
    (q_of_z 2) (q_of_dec (dec_of_q (q_of_ratio 4 2))) eq_refl (nv_num 2) (nv_dec _)) as H.
  exact H.
Qed.

(* 5 / 0 is a Float, not a trap: IEEE infinity, which the model leaves
   unspecified (any decimal) *)
Example float_division_by_zero_is_not_a_trap : forall d,
  bin_step bop_div (e_num 5) (e_num 0) (e_dec d).
Proof.
  intros d. eapply bs_quot_zero; [ apply nv_num | apply nv_num | reflexivity ].
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
    pose proof (bs_cmp_num bop_lt (e_num 1) (e_num 2) (q_of_z 1) (q_of_z 2)
      eq_refl (nv_num 1) (nv_num 2)) as H. exact H.
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

Example floor_division_by_zero_does_not_step : forall e',
  ~ step (e_bin (e_num 5) bop_fdiv (e_num 0)) e'.
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

(* ---- rejected ---- *)

(* 1.5 // 2: floor division wants whole numbers *)
Example float_floor_division_rejected : forall T,
  ~ typing nil (e_bin (e_dec (dec_of_q (q_of_ratio 3 2))) bop_fdiv (e_num 2)) T.
Proof.
  intros T H. destruct (bin_inv _ _ _ _ _ H) as [A [B [R [H1 [H2 [Hs _]]]]]].
  apply dec_inv in H1. head_eq H1. subst A. sig_absurd Hs.
Qed.

(* 1.5 % 2 likewise *)
Example float_remainder_rejected : forall T,
  ~ typing nil (e_bin (e_dec (dec_of_q (q_of_ratio 3 2))) bop_rem (e_num 2)) T.
Proof.
  intros T H. destruct (bin_inv _ _ _ _ _ H) as [A [B [R [H1 [H2 [Hs _]]]]]].
  apply dec_inv in H1. head_eq H1. subst A. sig_absurd Hs.
Qed.

(* 1 < "a": a number does not meet a string *)
Example mixed_comparison_rejected : forall T,
  ~ typing nil (e_bin (e_num 1) bop_lt (e_str [97])) T.
Proof.
  intros T H. destruct (bin_inv _ _ _ _ _ H) as [A [B [R [H1 [H2 [Hs _]]]]]].
  apply str_inv in H2. head_eq H2. subst B.
  destruct (num_inv _ _ _ H1) as [E | E]; head_eq E; subst A; sig_absurd Hs.
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
  destruct (num_inv _ _ _ H1) as [E | E]; head_eq E; discriminate.
Qed.

(* if true then 7 // 2 else 2.5 done: a concrete Int does not settle as a
   Float, so the branches disagree (only an operator widens it) *)
Example int_branch_against_float_rejected : forall T,
  ~ typing nil (e_ite e_true (e_bin (e_num 7) bop_fdiv (e_num 2))
                           (e_dec (dec_of_q (q_of_ratio 5 2)))) T.
Proof.
  intros T H. destruct (ite_inv _ _ _ _ _ H) as [T' [_ [H2 [H3 _]]]].
  destruct (bin_inv _ _ _ _ _ H2) as [A [B [R [_ [_ [Hs E]]]]]].
  apply dec_inv in H3.
  assert (Hr : R = typ_Int) by (inversion Hs; subst; try reflexivity;
                                 first [ discriminate | congruence ]).
  subst R.
  assert (Hf : teq typ_Float typ_Int)
    by (eapply teq_trans; [ exact H3 | apply teq_sym; exact E ]).
  apply teq_Float_inv in Hf. discriminate.
Qed.
