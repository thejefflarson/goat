(* Helper lemmas and tactics for building derivations of the PEG relation
   (GoatPeg.v). No theorem about goat lives here. *)

From Coq Require Import String List.
Import ListNotations.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Open Scope string_scope.
Open Scope list_scope.

Lemma peg_cast : forall e s r1 r2, peg e s r1 -> r1 = r2 -> peg e s r2.
Proof. intros e s r1 r2 H <-. exact H. Qed.

Lemma peg_term_ok : forall t s ts s',
  term_step t s = Ok ts s' -> peg (E_term t) s (Ok ts s').
Proof. intros t s ts s' H. rewrite <- H. apply P_term. Qed.

Lemma peg_term_fail : forall t s, term_step t s = Fail -> peg (E_term t) s Fail.
Proof. intros t s H. rewrite <- H. apply P_term. Qed.

Lemma peg_node : forall r s ts s' ts_all,
  silent r = false -> peg (body r) s (Ok ts s') -> ts_all = [Node r ts] ->
  peg (E_rule r) s (Ok ts_all s').
Proof.
  intros r s ts s' ts_all Hs Hb ->. apply (peg_cast _ _ (wrap r (Ok ts s'))).
  - apply P_rule. exact Hb.
  - simpl. rewrite Hs. reflexivity.
Qed.

Lemma peg_splice : forall r s ts s',
  silent r = true -> peg (body r) s (Ok ts s') -> peg (E_rule r) s (Ok ts s').
Proof.
  intros r s ts s' Hs Hb. apply (peg_cast _ _ (wrap r (Ok ts s'))).
  - apply P_rule. exact Hb.
  - simpl. rewrite Hs. reflexivity.
Qed.

Lemma peg_rule_fail : forall r s, peg (body r) s Fail -> peg (E_rule r) s Fail.
Proof. intros r s H. exact (P_rule r s Fail H). Qed.

Lemma peg_seq_ok : forall a b s ts s1 ts' s2 ts_all,
  peg a s (Ok ts s1) -> peg b s1 (Ok ts' s2) -> ts_all = ts ++ ts' ->
  peg (E_seq a b) s (Ok ts_all s2).
Proof.
  intros a b s ts s1 ts' s2 ts_all Ha Hb ->.
  exact (P_seq a b s ts s1 (Ok ts' s2) Ha Hb).
Qed.

Lemma peg_seq_fail2 : forall a b s ts s1,
  peg a s (Ok ts s1) -> peg b s1 Fail -> peg (E_seq a b) s Fail.
Proof.
  intros a b s ts s1 Ha Hb.
  exact (P_seq a b s ts s1 Fail Ha Hb).
Qed.

Lemma peg_star_cons : forall a s ts s1 ts' s2 ts_all,
  peg a s (Ok ts s1) -> peg (E_star a) s1 (Ok ts' s2) -> ts_all = ts ++ ts' ->
  peg (E_star a) s (Ok ts_all s2).
Proof.
  intros a s ts s1 ts' s2 ts_all Ha Hs ->.
  exact (P_star_step a s ts s1 ts' s2 Ha Hs).
Qed.

Lemma peg_plus_ok : forall a s ts s',
  peg (E_seq a (E_star a)) s (Ok ts s') -> peg (E_plus a) s (Ok ts s').
Proof. intros a s ts s' H. exact (P_plus a s _ H). Qed.

Lemma peg_plus_fail : forall a s, peg a s Fail -> peg (E_plus a) s Fail.
Proof.
  intros a s H. apply P_plus. apply P_seq_fail. exact H.
Qed.

Lemma peg_alt_fail : forall a b s,
  peg a s Fail -> peg b s Fail -> peg (E_alt a b) s Fail.
Proof. intros a b s Ha Hb. exact (P_alt_right a b s Fail Ha Hb). Qed.

(* ---- the derivation builders ---- *)

Ltac pcat := first [ reflexivity | (rewrite ?app_nil_r; reflexivity) ].

(* [pok ext] builds a derivation of a goal [peg e s (Ok ?ts ?s')] by following
   the expression, trying a choice's left branch before its right, and a
   repetition's step before its stop. [ext] closes goals the tactic cannot
   (a hypothesis about a subterm). *)
Ltac pok ext :=
  first
  [ solve [ ext ]
  | eapply peg_term_ok; reflexivity
  | (eapply peg_node; [ reflexivity | cbn [body]; pok ext | pcat ])
  | (eapply peg_splice; [ reflexivity | cbn [body]; pok ext ])
  | (eapply peg_seq_ok; [ pok ext | pok ext | pcat ])
  | (eapply P_alt_left; pok ext)
  | (eapply P_alt_right; [ pfail ext | pok ext ])
  | (eapply peg_star_cons; [ pok ext | pok ext | pcat ])
  | (eapply P_star_stop; pfail ext)
  | (eapply P_opt_some; pok ext)
  | (eapply P_opt_none; pfail ext)
  | (eapply peg_plus_ok; pok ext)
  | (eapply P_expect; pok ext)
  ]
with pfail ext :=
  first
  [ solve [ ext ]
  | (eapply peg_term_fail; reflexivity)
  | (eapply peg_rule_fail; cbn [body]; pfail ext)
  | (eapply P_seq_fail; pfail ext)
  | (eapply peg_seq_fail2; [ pok ext | pfail ext ])
  | (eapply peg_alt_fail; [ pfail ext | pfail ext ])
  | (eapply peg_plus_fail; pfail ext)
  | (eapply P_expect; pfail ext)
  ].

Ltac nope := fail.
