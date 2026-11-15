(* Parsing a printed chain: a primary expression followed by postfixes (calls and
   field accesses). The facts the later proofs need about where such a chain
   stops and what it can be mistaken for. *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatPegTac.
Require Import Goat.GoatDen.
Require Import Goat.GoatPrint.
Open Scope string_scope.
Open Scope list_scope.

(* What can follow a printed expression or value. *)
Inductive Stop : list tok -> Prop :=
  | Stop_nil : Stop []
  | Stop_rparen : forall r, Stop (TSym ")" :: r)
  | Stop_comma : forall r, Stop (TSym "," :: r)
  | Stop_rbrace : forall r, Stop (TSym "}" :: r)
  | Stop_done : forall r, Stop (TSym "done" :: r)
  | Stop_then : forall r, Stop (TSym "then" :: r)
  | Stop_else : forall r, Stop (TSym "else" :: r)
  | Stop_semi : forall r, Stop (TSym ";" :: r).

(* What can follow an expression, as opposed to a value. *)
Inductive StopE : list tok -> Prop :=
  | StopE_nil : StopE []
  | StopE_rparen : forall r, StopE (TSym ")" :: r)
  | StopE_comma : forall r, StopE (TSym "," :: r)
  | StopE_rbrace : forall r, StopE (TSym "}" :: r)
  | StopE_done : forall r, StopE (TSym "done" :: r)
  | StopE_then : forall r, StopE (TSym "then" :: r)
  | StopE_else : forall r, StopE (TSym "else" :: r).

Lemma stop_of_stopE : forall r, StopE r -> Stop r.
Proof. intros r H. inversion H; constructor. Qed.

(* What can follow a chain: what follows an expression, or an operator. *)
Inductive StopC : list tok -> Prop :=
  | StopC_stop : forall r, Stop r -> StopC r
  | StopC_op : forall o r, StopC (TSym (op_text o) :: r).

(* The next token is not "=": a name here is not the start of a binding. *)
Definition NotEq (r : list tok) : Prop :=
  match r with TSym s :: _ => s <> "=" | _ => True end.

Definition NotDecl (s : list tok) : Prop :=
  match s with TName _ :: TSym s1 :: _ => s1 <> "=" | _ => True end.

(* The first token is not one that starts an operator, a tag declaration or a
   foreign binding. *)
Definition Plain (s : list tok) : Prop :=
  match s with
  | TSym x :: _ => x <> "not" /\ x <> "-" /\ x <> "tag" /\ x <> "foreign"
  | _ => True
  end.

Lemma text_fail : forall t s1 r, s1 <> t -> peg (E_term (T_text t)) (TSym s1 :: r) Fail.
Proof.
  intros t s1 r Hne. apply peg_term_fail. simpl.
  destruct (String.eqb t s1) eqn:Heq; [ | reflexivity ].
  apply String.eqb_eq in Heq. subst. contradiction.
Qed.

Ltac ext_text := eapply text_fail; assumption.

Lemma notEq_stop : forall r, Stop r -> NotEq r.
Proof. intros r H. inversion H; subst; simpl; try exact I; intro Hx; discriminate Hx. Qed.

Lemma notEq_stopC : forall r, StopC r -> NotEq r.
Proof.
  intros r H. inversion H; subst.
  - apply notEq_stop. assumption.
  - destruct o; simpl; intro Hx; discriminate Hx.
Qed.

Lemma stopC_postfix_fail : forall r, StopC r -> peg (E_rule R__postfix) r Fail.
Proof.
  intros r H. inversion H; subst.
  - match goal with Hs : Stop _ |- _ => inversion Hs; subst end; pfail nope.
  - destruct o; pfail nope.
Qed.

Lemma stop_more_math : forall r, Stop r ->
  peg (E_star (E_rule R__more_math)) r (Ok [] r).
Proof. intros r H. inversion H; subst; pok nope. Qed.

Lemma notdecl_fail : forall s, NotDecl s -> peg (E_rule R_declaration) s Fail.
Proof.
  intros s H. destruct s as [| [x | n | | y] s1]; try (pfail nope; fail).
  destruct s1 as [| [x1 | n1 | | y1] s2]; simpl in H; try (pfail nope; fail).
  pfail ext_text.
Qed.

Lemma plain_not : forall s, Plain s -> peg (E_rule R_not_op) s Fail.
Proof.
  intros s H. destruct s as [| [x | n | | y] s1]; try (pfail nope; fail).
  simpl in H. destruct H as (H1 & H2 & H3 & H4). pfail ext_text.
Qed.

Lemma plain_neg : forall s, Plain s -> peg (E_rule R_negation) s Fail.
Proof.
  intros s H. destruct s as [| [x | n | | y] s1]; try (pfail nope; fail).
  simpl in H. destruct H as (H1 & H2 & H3 & H4). pfail ext_text.
Qed.

Lemma plain_foreign : forall s, Plain s -> peg (E_rule R_foreign_decl) s Fail.
Proof.
  intros s H. destruct s as [| [x | n | | y] s1]; try (pfail nope; fail).
  simpl in H. destruct H as (H1 & H2 & H3 & H4). pfail ext_text.
Qed.

Lemma plain_tag : forall s, Plain s -> peg (E_rule R_tag_decl) s Fail.
Proof.
  intros s H. destruct s as [| [x | n | | y] s1]; try (pfail nope; fail).
  simpl in H. destruct H as (H1 & H2 & H3 & H4). pfail ext_text.
Qed.

(* ---- chains ---- *)

(* A primary expression: its parse does not depend on what follows, provided
   that is not "=" (which would make a name the start of a binding). *)
Definition PrimOK (H : list tree) : Prop :=
  forall r, NotEq r ->
    Plain (flats H ++ r) /\ NotDecl (flats H ++ r) /\
    peg (E_rule R__primary) (flats H ++ r) (Ok H r).

Definition PostOK (p : tree) : Prop :=
  (forall r, NotEq (flat p ++ r)) /\
  forall r, peg (E_rule R__postfix) (flat p ++ r) (Ok [p] r).

Definition Chain (ks : list tree) : Prop :=
  exists H Ps, ks = H ++ Ps /\ PrimOK H /\ Forall PostOK Ps.

Lemma notEq_posts : forall Ps r,
  Forall PostOK Ps -> NotEq r -> NotEq (flats Ps ++ r).
Proof.
  intros Ps r Hp Hr. destruct Ps as [| p Ps]; [ exact Hr | ].
  inversion Hp as [| ? ? [Hne _] _]; subst. rewrite flats_cons, <- app_assoc.
  apply Hne.
Qed.

Lemma star_posts : forall Ps r,
  Forall PostOK Ps -> StopC r ->
  peg (E_star (E_rule R__postfix)) (flats Ps ++ r) (Ok Ps r).
Proof.
  induction Ps as [| p Ps IH]; intros r Hp Hstop.
  - pok ltac:(exact (stopC_postfix_fail _ Hstop)).
  - inversion Hp as [| ? ? [_ Hpost] Hrest]; subst.
    rewrite flats_cons, <- app_assoc.
    pok ltac:(first [ exact (Hpost _) | exact (IH _ Hrest Hstop) ]).
Qed.

Lemma chain_operand : forall ks r,
  Chain ks -> StopC r ->
  peg (E_rule R__operand) (flats ks ++ r) (Ok ks r).
Proof.
  intros ks r (H & Ps & -> & Hprim & Hposts) Hstop.
  assert (Hne : NotEq (flats Ps ++ r))
    by (apply notEq_posts; [ exact Hposts | apply notEq_stopC; exact Hstop ]).
  destruct (Hprim _ Hne) as (Hplain & _ & Hpeg).
  assert (Hstar : peg (E_star (E_rule R__postfix)) (flats Ps ++ r) (Ok Ps r))
    by (apply star_posts; assumption).
  rewrite flats_app, <- app_assoc.
  pok ltac:(first
    [ exact Hpeg | exact Hstar
    | (eapply plain_not; exact Hplain) | (eapply plain_neg; exact Hplain) ]).
Qed.

Lemma chain_plain : forall ks r,
  Chain ks -> StopC r -> Plain (flats ks ++ r).
Proof.
  intros ks r (H & Ps & -> & Hprim & Hposts) Hstop.
  assert (Hne : NotEq (flats Ps ++ r))
    by (apply notEq_posts; [ exact Hposts | apply notEq_stopC; exact Hstop ]).
  destruct (Hprim _ Hne) as (Hplain & _ & _).
  rewrite flats_app, <- app_assoc. exact Hplain.
Qed.

Lemma chain_notdecl : forall ks r,
  Chain ks -> StopC r -> NotDecl (flats ks ++ r).
Proof.
  intros ks r (H & Ps & -> & Hprim & Hposts) Hstop.
  assert (Hne : NotEq (flats Ps ++ r))
    by (apply notEq_posts; [ exact Hposts | apply notEq_stopC; exact Hstop ]).
  destruct (Hprim _ Hne) as (_ & Hnd & _).
  rewrite flats_app, <- app_assoc. exact Hnd.
Qed.

Lemma chain_snoc : forall ks p, Chain ks -> PostOK p -> Chain (ks ++ [p]).
Proof.
  intros ks p (H & Ps & -> & Hprim & Hposts) Hp.
  exists H, (Ps ++ [p]). split; [ symmetry; apply app_assoc | ].
  split; [ exact Hprim | ].
  apply Forall_app. split; [ exact Hposts | constructor; [ exact Hp | constructor ] ].
Qed.

Lemma chain_statement : forall ks r,
  Chain ks -> Stop r ->
  peg (E_rule R__statement) (flats ks ++ r) (Ok ks r).
Proof.
  intros ks r Hchain Hstop.
  pok ltac:(first [ exact (chain_operand _ _ Hchain (StopC_stop _ Hstop))
                  | exact (stop_more_math _ Hstop) ]).
Qed.

Lemma chain_value : forall ks r,
  Chain ks -> Stop r ->
  peg (E_rule R_value) (flats ks ++ r) (Ok [Node R_value ks] r).
Proof.
  intros ks r Hchain Hstop.
  pok ltac:(first [ exact (chain_operand _ _ Hchain (StopC_stop _ Hstop))
                  | exact (stop_more_math _ Hstop) ]).
Qed.

(* ---- a binary operation: two chains round an operator ---- *)

Lemma infix_parses : forall o r,
  peg (E_rule R__infix) (TSym (op_text o) :: r) (Ok [op_tree o] r).
Proof. intros o r. destruct o; pok nope. Qed.

Lemma flats_op : forall o ks,
  flats (op_tree o :: ks) = TSym (op_text o) :: flats ks.
Proof.
  intros o ks. unfold op_tree.
  rewrite flats_cons, flat_node, flats_cons, flat_leaf, flats_nil. reflexivity.
Qed.

Definition Bin (ks : list tree) : Prop :=
  exists k1 o k2, ks = k1 ++ op_tree o :: k2 /\ Chain k1 /\ Chain k2.

(* What the last statement of a block can be: one chain, or two round an
   operator. *)
Definition Fin (ks : list tree) : Prop := Chain ks \/ Bin ks.

Lemma flats_bin : forall k1 o k2 r,
  flats (k1 ++ op_tree o :: k2) ++ r
  = flats k1 ++ TSym (op_text o) :: (flats k2 ++ r).
Proof.
  intros k1 o k2 r. rewrite flats_app, flats_op, <- app_assoc. reflexivity.
Qed.

Lemma bin_math : forall k1 o k2 r,
  Chain k1 -> Chain k2 -> Stop r ->
  peg (E_seq (E_rule R__operand) (E_star (E_rule R__more_math)))
      (flats k1 ++ TSym (op_text o) :: (flats k2 ++ r))
      (Ok (k1 ++ op_tree o :: k2) r).
Proof.
  intros k1 o k2 r H1 H2 Hr.
  eapply peg_seq_ok;
    [ exact (chain_operand _ _ H1 (StopC_op o _)) | | pcat ].
  eapply peg_star_cons;
    [ | exact (stop_more_math _ Hr) | pcat ].
  pok ltac:(first
    [ exact (infix_parses o _)
    | exact (chain_operand _ _ H2 (StopC_stop _ Hr)) ]).
Qed.

Lemma fin_statement : forall ks r,
  Fin ks -> Stop r ->
  peg (E_rule R__statement) (flats ks ++ r) (Ok ks r).
Proof.
  intros ks r [Hc | (k1 & o & k2 & -> & H1 & H2)] Hstop.
  - exact (chain_statement _ _ Hc Hstop).
  - rewrite flats_bin. eapply peg_splice; [ reflexivity | ].
    cbn [body]. exact (bin_math _ _ _ _ H1 H2 Hstop).
Qed.

Lemma fin_value : forall ks r,
  Fin ks -> Stop r ->
  peg (E_rule R_value) (flats ks ++ r) (Ok [Node R_value ks] r).
Proof.
  intros ks r [Hc | (k1 & o & k2 & -> & H1 & H2)] Hstop.
  - exact (chain_value _ _ Hc Hstop).
  - rewrite flats_bin. eapply peg_node; [ reflexivity | | reflexivity ].
    cbn [body]. exact (bin_math _ _ _ _ H1 H2 Hstop).
Qed.

Lemma fin_plain : forall ks r,
  Fin ks -> Stop r -> Plain (flats ks ++ r).
Proof.
  intros ks r [Hc | (k1 & o & k2 & -> & H1 & H2)] Hstop.
  - exact (chain_plain _ _ Hc (StopC_stop _ Hstop)).
  - rewrite flats_bin. exact (chain_plain _ _ H1 (StopC_op o _)).
Qed.

Lemma fin_notdecl : forall ks r,
  Fin ks -> Stop r -> NotDecl (flats ks ++ r).
Proof.
  intros ks r [Hc | (k1 & o & k2 & -> & H1 & H2)] Hstop.
  - exact (chain_notdecl _ _ Hc (StopC_stop _ Hstop)).
  - rewrite flats_bin. exact (chain_notdecl _ _ H1 (StopC_op o _)).
Qed.
