(* The arithmetic behind whole-number and decimal literals.  It lives apart
   from [GoatDefs] because ZArith and QArith define notations (for example
   [p~1]) that clash with Metalib's [x ~ T] context notation, so the
   development imports them here and nowhere else. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.QArith.QArith.

Definition znum : Set := Z.

(* Integer numerals outside this file, without importing ZArith's notations. *)
Declare Scope znum_scope.
Number Notation Z Z.of_num_int Z.to_num_int : znum_scope.
Definition qnum : Set := Q.

Definition q_of_z (z : znum) : qnum := inject_Z z.
Definition q_of_dec (d : Z * positive) : qnum := Qmake (fst d) (snd d).
Definition dec_of_q (q : qnum) : Z * positive := (Qnum q, Qden q).

Definition z_add (a b : znum) : znum := (a + b)%Z.
Definition z_sub (a b : znum) : znum := (a - b)%Z.
Definition z_mul (a b : znum) : znum := (a * b)%Z.

(* Z.div rounds toward negative infinity and Z.modulo takes the sign of the
   divisor, which is what [//] and [%] do (ADR 0017). *)
Definition z_div (a b : znum) : znum := Z.div a b.
Definition z_mod (a b : znum) : znum := Z.modulo a b.
Definition z_is_zero (b : znum) : bool := Z.eqb b 0%Z.

Definition q_add (p q : qnum) : qnum := (p + q)%Q.
Definition q_sub (p q : qnum) : qnum := (p - q)%Q.
Definition q_mul (p q : qnum) : qnum := (p * q)%Q.
Definition q_div (p q : qnum) : qnum := (p / q)%Q.
Definition q_cmp (p q : qnum) : comparison := Qcompare p q.
Definition q_is_zero (q : qnum) : bool := Qeq_bool q 0%Q.

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

(* The ratio [a / b] as a rational, for stating decimal results. *)
Definition q_of_ratio (a b : znum) : qnum := q_div (q_of_z a) (q_of_z b).
Arguments q_of_ratio a%_znum_scope b%_znum_scope.
