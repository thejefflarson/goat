(* Unit, strings, [if], arithmetic and comparison of base types: worked
   examples (docs/semantics.md section 8, ADR 0036).  Programs the rules accept
   type and run; programs they reject have no derivation.  The accepted examples
   fail to compile if a rule is dropped, and the rejected ones if a rule is
   loosened. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSound.
Require Import Coq.Lists.List.
Import ListNotations.

(* ---- accepted ---- *)

Example if_types : typing nil (e_ite e_true (e_num 1) (e_num 2)) typ_Number.
Proof.
  apply T_If; [ apply T_True | apply T_Num | apply T_Num ]; constructor.
Qed.

Example arith_types : typing nil (e_bin (e_num 1) bop_add (e_num 2)) typ_Number.
Proof. apply T_Arith; [ reflexivity | apply T_Num | apply T_Num ]; constructor. Qed.

Example unit_types : typing nil e_unit typ_Unit.
Proof. apply T_Unit; constructor. Qed.

(* "a" < "b" *)
Example string_order_types :
  typing nil (e_bin (e_str [97]) bop_lt (e_str [98])) typ_Bool.
Proof.
  apply T_Cmp with (B := typ_String);
    [ reflexivity | constructor | apply T_Str | apply T_Str ]; constructor.
Qed.

(* false < true *)
Example bool_order_types : typing nil (e_bin e_false bop_lt e_true) typ_Bool.
Proof.
  apply T_Cmp with (B := typ_Bool);
    [ reflexivity | constructor | apply T_False | apply T_True ]; constructor.
Qed.

(* ---- they run ---- *)

Example arith_runs : step (e_bin (e_num 7) bop_sub (e_num 2)) (e_num 5).
Proof. apply (st_bin (e_num 7) bop_sub (e_num 2)); constructor. Qed.

Example floor_division_runs : step (e_bin (e_num 7) bop_fdiv (e_num 2)) (e_num 3).
Proof. apply (st_bin (e_num 7) bop_fdiv (e_num 2)); constructor. Qed.

Example remainder_runs : step (e_bin (e_num 7) bop_rem (e_num 2)) (e_num 1).
Proof. apply (st_bin (e_num 7) bop_rem (e_num 2)); constructor. Qed.

(* a prefix comes before the longer string; the first differing byte decides *)
Example prefix_orders_first :
  eval_bin bop_lt (e_str [97]) (e_str [97; 98]) = e_true.
Proof. reflexivity. Qed.

Example first_byte_decides :
  eval_bin bop_gt (e_str [98]) (e_str [97; 122]) = e_true.
Proof. reflexivity. Qed.

Example false_before_true : eval_bin bop_lt e_false e_true = e_true.
Proof. reflexivity. Qed.

Example equal_numbers : eval_bin bop_eq (e_num 3) (e_num 3) = e_true.
Proof. reflexivity. Qed.

Example unequal_strings : eval_bin bop_ne (e_str [1]) (e_str [2]) = e_true.
Proof. reflexivity. Qed.

(* if 1 < 2 then 10 else 20 runs to 10 *)
Example if_runs :
  multistep (e_ite (e_bin (e_num 1) bop_lt (e_num 2)) (e_num 10) (e_num 20)) (e_num 10).
Proof.
  eapply ms_step.
  - apply st_ite1. apply (st_bin (e_num 1) bop_lt (e_num 2)); constructor.
  - cbn. eapply ms_step; [ apply st_ite_true | apply ms_refl ].
Qed.

(* ---- rejected ---- *)

Lemma num_inv : forall G n T, typing G (e_num n) T -> teq typ_Number T.
Proof.
  intros G n T H. remember (e_num n) as e0 eqn:He.
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

(* 1 < "a": a number does not meet a string *)
Example mixed_comparison_rejected : forall T,
  ~ typing nil (e_bin (e_num 1) bop_lt (e_str [97])) T.
Proof.
  intros T H. destruct (bin_inv _ _ _ _ _ H)
    as [[Ho _] | [_ [B [HB [H1 [H2 _]]]]]].
  - discriminate Ho.
  - apply num_inv in H1. apply str_inv in H2.
    assert (Hs : teq typ_Number typ_String) by (eapply teq_trans; [ exact H1 | apply teq_sym; exact H2 ]).
    apply teq_Number_inv in Hs. discriminate Hs.
Qed.

(* true + true: arithmetic wants numbers *)
Example boolean_arithmetic_rejected : forall T,
  ~ typing nil (e_bin e_true bop_add e_true) T.
Proof.
  intros T H. destruct (bin_inv _ _ _ _ _ H)
    as [[_ [H1 _]] | [Ho _]].
  - apply true_inv in H1. apply teq_Bool_inv in H1. discriminate H1.
  - discriminate Ho.
Qed.

(* if 1 then 2 else 3: the condition is a number *)
Example number_condition_rejected : forall T,
  ~ typing nil (e_ite (e_num 1) (e_num 2) (e_num 3)) T.
Proof.
  intros T H. destruct (ite_inv _ _ _ _ _ H) as [T' [H1 _]].
  apply num_inv in H1. apply teq_Number_inv in H1. discriminate H1.
Qed.
