(* Ford-style relational semantics of the generated grammar (GoatGrammar.v)
   over a token stream, and its determinism (T2, ADR 0030). Recovery
   annotations are not in the generated grammar, so the relation describes
   valid input only. The lexer is trusted: a token stream is the input. *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Goat.GoatGrammar.

Inductive tok : Type :=
  | TName (s : string)
  | TNum (n : nat)
  | TStr
  | TSym (s : string).

Inductive tree : Type :=
  | Leaf (k : tok)
  | Node (r : rule) (cs : list tree).

Inductive result : Type :=
  | Fail
  | Ok (ts : list tree) (rest : list tok).

Definition accepts (t : terminal) (k : tok) : bool :=
  match t, k with
  | T_text s, TSym s' => String.eqb s s'
  | T_name, TName _ => true
  | T_number, TNum _ => true
  | T_string, TStr => true
  | _, _ => false
  end.

Definition term_step (t : terminal) (s : list tok) : result :=
  match t, s with
  | T_eoi, [] => Ok [] []
  | T_eoi, _ :: _ => Fail
  | _, [] => Fail
  | _, k :: s' => if accepts t k then Ok [Leaf k] s' else Fail
  end.

Definition wrap (r : rule) (res : result) : result :=
  match res with
  | Fail => Fail
  | Ok ts s => Ok (if silent r then ts else [Node r ts]) s
  end.

Definition prepend (ts : list tree) (res : result) : result :=
  match res with
  | Fail => Fail
  | Ok ts' s => Ok (ts ++ ts') s
  end.

Inductive peg : pexpr -> list tok -> result -> Prop :=
  | P_term : forall t s,
      peg (E_term t) s (term_step t s)
  | P_rule : forall r s res,
      peg (body r) s res ->
      peg (E_rule r) s (wrap r res)
  | P_seq : forall a b s ts s1 res,
      peg a s (Ok ts s1) ->
      peg b s1 res ->
      peg (E_seq a b) s (prepend ts res)
  | P_seq_fail : forall a b s,
      peg a s Fail ->
      peg (E_seq a b) s Fail
  | P_alt_left : forall a b s ts s',
      peg a s (Ok ts s') ->
      peg (E_alt a b) s (Ok ts s')
  | P_alt_right : forall a b s res,
      peg a s Fail ->
      peg b s res ->
      peg (E_alt a b) s res
  | P_star_stop : forall a s,
      peg a s Fail ->
      peg (E_star a) s (Ok [] s)
  | P_star_step : forall a s ts s1 ts' s2,
      peg a s (Ok ts s1) ->
      peg (E_star a) s1 (Ok ts' s2) ->
      peg (E_star a) s (Ok (ts ++ ts') s2)
  | P_plus : forall a s res,
      peg (E_seq a (E_star a)) s res ->
      peg (E_plus a) s res
  | P_opt_some : forall a s ts s',
      peg a s (Ok ts s') ->
      peg (E_opt a) s (Ok ts s')
  | P_opt_none : forall a s,
      peg a s Fail ->
      peg (E_opt a) s (Ok [] s)
  | P_expect : forall a s res,
      peg a s res ->
      peg (E_expect a) s res.


(* ---- what a derivation of each expression form can look like ---- *)

Lemma inv_term : forall {t s r}, peg (E_term t) s r -> r = term_step t s.
Proof. intros t s r H. inversion H. reflexivity. Qed.

Lemma inv_rule : forall {x s r},
  peg (E_rule x) s r -> exists res, peg (body x) s res /\ r = wrap x res.
Proof. intros x s r H. inversion H; subst. eauto. Qed.

Lemma inv_seq : forall {a b s r},
  peg (E_seq a b) s r ->
  (exists ts s1 res, peg a s (Ok ts s1) /\ peg b s1 res /\ r = prepend ts res)
  \/ (peg a s Fail /\ r = Fail).
Proof.
  intros a b s r H. inversion H; subst.
  - left. eauto 8.
  - right. eauto.
Qed.

Lemma inv_alt : forall {a b s r},
  peg (E_alt a b) s r ->
  (exists ts s', peg a s (Ok ts s') /\ r = Ok ts s')
  \/ (peg a s Fail /\ peg b s r).
Proof.
  intros a b s r H. inversion H; subst.
  - left. eauto.
  - right. eauto.
Qed.

Lemma inv_star : forall {a s r},
  peg (E_star a) s r ->
  (peg a s Fail /\ r = Ok [] s)
  \/ (exists ts s1 ts' s2,
        peg a s (Ok ts s1) /\ peg (E_star a) s1 (Ok ts' s2) /\ r = Ok (ts ++ ts') s2).
Proof.
  intros a s r H. inversion H; subst.
  - left. eauto.
  - right. eauto 8.
Qed.

Lemma inv_plus : forall {a s r},
  peg (E_plus a) s r -> peg (E_seq a (E_star a)) s r.
Proof. intros a s r H. inversion H; subst. assumption. Qed.

Lemma inv_opt : forall {a s r},
  peg (E_opt a) s r ->
  (exists ts s', peg a s (Ok ts s') /\ r = Ok ts s')
  \/ (peg a s Fail /\ r = Ok [] s).
Proof.
  intros a s r H. inversion H; subst.
  - left. eauto.
  - right. eauto.
Qed.

Lemma inv_expect : forall {a s r}, peg (E_expect a) s r -> peg a s r.
Proof. intros a s r H. inversion H; subst. assumption. Qed.

(* T2 *)
Theorem peg_deterministic : forall e s r1,
  peg e s r1 -> forall r2, peg e s r2 -> r1 = r2.
Proof.
  intros e s r1 D1.
  induction D1 as
    [ t s
    | r s res Hbody IH
    | a b s ts s1 res Ha IHa Hb IHb
    | a b s Ha IHa
    | a b s ts s' Ha IHa
    | a b s res Ha IHa Hb IHb
    | a s Ha IHa
    | a s ts s1 ts' s2 Ha IHa Hstar IHstar
    | a s res Hseq IH
    | a s ts s' Ha IHa
    | a s Ha IHa
    | a s res Ha IH ];
    intros r2 D2.
  - (* term *)
    rewrite (inv_term D2). reflexivity.
  - (* rule *)
    destruct (inv_rule D2) as (res2 & Hbody2 & ->).
    assert (Hres : res = res2) by (apply IH; exact Hbody2).
    rewrite Hres. reflexivity.
  - (* seq, first part succeeds *)
    destruct (inv_seq D2) as [(ts2 & s2 & res2 & Ha2 & Hb2 & ->) | (Ha2 & ->)].
    + assert (Hok : Ok ts s1 = Ok ts2 s2) by (apply IHa; exact Ha2).
      injection Hok as <- <-.
      assert (Hres : res = res2) by (apply IHb; exact Hb2).
      rewrite Hres. reflexivity.
    + assert (Hbad : Ok ts s1 = Fail) by (apply IHa; exact Ha2).
      discriminate Hbad.
  - (* seq, first part fails *)
    destruct (inv_seq D2) as [(ts2 & s2 & res2 & Ha2 & Hb2 & ->) | (Ha2 & ->)].
    + assert (Hbad : Fail = Ok ts2 s2) by (apply IHa; exact Ha2).
      discriminate Hbad.
    + reflexivity.
  - (* alt, left succeeds *)
    destruct (inv_alt D2) as [(ts2 & s2 & Ha2 & ->) | (Ha2 & Hb2)].
    + assert (Hok : Ok ts s' = Ok ts2 s2) by (apply IHa; exact Ha2).
      exact Hok.
    + assert (Hbad : Ok ts s' = Fail) by (apply IHa; exact Ha2).
      discriminate Hbad.
  - (* alt, left fails *)
    destruct (inv_alt D2) as [(ts2 & s2 & Ha2 & ->) | (Ha2 & Hb2)].
    + assert (Hbad : Fail = Ok ts2 s2) by (apply IHa; exact Ha2).
      discriminate Hbad.
    + apply IHb. exact Hb2.
  - (* star, stops *)
    destruct (inv_star D2) as [(Ha2 & ->) | (ts2 & s2 & ts2' & s3 & Ha2 & Hstar2 & ->)].
    + reflexivity.
    + assert (Hbad : Fail = Ok ts2 s2) by (apply IHa; exact Ha2).
      discriminate Hbad.
  - (* star, steps *)
    destruct (inv_star D2) as [(Ha2 & ->) | (ts3 & s3 & ts3' & s4 & Ha3 & Hstar3 & ->)].
    + assert (Hbad : Ok ts s1 = Fail) by (apply IHa; exact Ha2).
      discriminate Hbad.
    + assert (Hhead : Ok ts s1 = Ok ts3 s3) by (apply IHa; exact Ha3).
      injection Hhead as <- <-.
      assert (Htail : Ok ts' s2 = Ok ts3' s4) by (apply IHstar; exact Hstar3).
      injection Htail as <- <-.
      reflexivity.
  - (* plus *)
    apply IH. exact (inv_plus D2).
  - (* opt, present *)
    destruct (inv_opt D2) as [(ts2 & s2 & Ha2 & ->) | (Ha2 & ->)].
    + assert (Hok : Ok ts s' = Ok ts2 s2) by (apply IHa; exact Ha2).
      exact Hok.
    + assert (Hbad : Ok ts s' = Fail) by (apply IHa; exact Ha2).
      discriminate Hbad.
  - (* opt, absent *)
    destruct (inv_opt D2) as [(ts2 & s2 & Ha2 & ->) | (Ha2 & ->)].
    + assert (Hbad : Fail = Ok ts2 s2) by (apply IHa; exact Ha2).
      discriminate Hbad.
    + reflexivity.
  - (* expect *)
    apply IH. exact (inv_expect D2).
Qed.
