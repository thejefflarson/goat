(* The integer arithmetic behind whole-number literals.  It lives apart from
   [GoatDefs] because ZArith defines notations (for example [p~1]) that clash
   with Metalib's [x ~ T] context notation, so the development imports it here
   and nowhere else. *)

Require Import Stdlib.ZArith.ZArith.

Definition znum : Set := Z.

(* Integer numerals outside this file, without importing ZArith's notations. *)
Declare Scope znum_scope.
Number Notation Z Z.of_num_int Z.to_num_int : znum_scope.

Definition z_add (a b : znum) : znum := (a + b)%Z.
Definition z_sub (a b : znum) : znum := (a - b)%Z.
Definition z_mul (a b : znum) : znum := (a * b)%Z.

(* Z.div rounds toward negative infinity and Z.modulo takes the sign of the
   divisor, which is what [//] and [%] do (ADR 0017). *)
Definition z_div (a b : znum) : znum := Z.div a b.
Definition z_mod (a b : znum) : znum := Z.modulo a b.
Definition z_is_zero (b : znum) : bool := Z.eqb b 0%Z.
Definition z_cmp (a b : znum) : comparison := Z.compare a b.

(* An [Int] is a signed 64-bit integer, as on the desktop target. *)
Definition int_min : znum := (- 2 ^ 63)%Z.
Definition int_max : znum := (2 ^ 63 - 1)%Z.
Definition in_int (z : znum) : bool := (Z.leb int_min z && Z.leb z int_max)%bool.

Definition z_of_nat (n : nat) : znum := Z.of_nat n.
Definition nat_of_z (z : znum) : nat := Z.to_nat z.
Definition z_nonneg (z : znum) : bool := Z.leb 0%Z z.

Lemma nat_of_z_of_nat : forall n, nat_of_z (z_of_nat n) = n.
Proof. intros n. unfold nat_of_z, z_of_nat. apply Nat2Z.id. Qed.

Lemma z_of_nat_of_z : forall z, z_nonneg z = true -> z_of_nat (nat_of_z z) = z.
Proof.
  intros z H. unfold z_nonneg in H. apply Z.leb_le in H.
  unfold z_of_nat, nat_of_z. apply Z2Nat.id. exact H.
Qed.
