(* The forests the generated grammar can produce for the core fragment, and the
   shape of the children of each core node (ADR 0030). [gen e ts] says the
   expression [e] can produce the forest [ts] using core rules only; it does not
   look at the input. *)

From Coq Require Import String List.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Lia.
Open Scope string_scope.
Open Scope list_scope.

Definition core_rule (r : rule) : bool :=
  match r with
  | R_goat | R_expr | R_value | R_declaration | R_local | R_function | R_params
  | R_call | R_arguments | R_access | R_take | R_name | R_number | R_boolean | R_true_lit
  | R_false_lit | R_record | R_field | R_string | R_conditional
  | R_plus | R_minus | R_multiply | R_floor_divide | R_divide | R_remainder
  | R_equal | R_not_equal | R_lte | R_lt | R_gte | R_gt => true
  | _ => false
  end.

Inductive gen : pexpr -> list tree -> Prop :=
  | G_text : forall s,
      gen (E_term (T_text s)) [Leaf (TSym s)]
  | G_name : forall x,
      gen (E_term T_name) [Leaf (TName x)]
  | G_number : forall n,
      gen (E_term T_number) [Leaf (TNum n)]
  | G_string :
      gen (E_term T_string) [Leaf TStr]
  | G_eoi :
      gen (E_term T_eoi) []
  | G_node : forall r cs,
      silent r = false -> core_rule r = true -> gen (body r) cs ->
      gen (E_rule r) [Node r cs]
  | G_splice : forall r ts,
      silent r = true -> gen (body r) ts ->
      gen (E_rule r) ts
  | G_seq : forall a b ts1 ts2,
      gen a ts1 -> gen b ts2 ->
      gen (E_seq a b) (ts1 ++ ts2)
  | G_alt_left : forall a b ts,
      gen a ts -> gen (E_alt a b) ts
  | G_alt_right : forall a b ts,
      gen b ts -> gen (E_alt a b) ts
  | G_star_nil : forall a,
      gen (E_star a) []
  | G_star_cons : forall a ts1 ts2,
      gen a ts1 -> gen (E_star a) ts2 ->
      gen (E_star a) (ts1 ++ ts2)
  | G_plus : forall a ts,
      gen (E_seq a (E_star a)) ts -> gen (E_plus a) ts
  | G_opt_some : forall a ts,
      gen a ts -> gen (E_opt a) ts
  | G_opt_none : forall a,
      gen (E_opt a) []
  | G_expect : forall a ts,
      gen a ts -> gen (E_expect a) ts.

(* ---- inversions ---- *)

Lemma gen_text_inv : forall {s ts}, gen (E_term (T_text s)) ts -> ts = [Leaf (TSym s)].
Proof. intros s ts H. inversion H. reflexivity. Qed.

Lemma gen_name_inv : forall {ts}, gen (E_term T_name) ts -> exists x, ts = [Leaf (TName x)].
Proof. intros ts H. inversion H. eauto. Qed.

Lemma gen_number_inv : forall {ts}, gen (E_term T_number) ts -> exists n, ts = [Leaf (TNum n)].
Proof. intros ts H. inversion H. eauto. Qed.

Lemma gen_node_inv : forall {r ts},
  gen (E_rule r) ts -> silent r = false ->
  exists cs, ts = [Node r cs] /\ core_rule r = true /\ gen (body r) cs.
Proof.
  intros r ts H Hsilent. inversion H; subst.
  - eauto.
  - congruence.
Qed.

Lemma gen_splice_inv : forall {r ts},
  gen (E_rule r) ts -> silent r = true -> gen (body r) ts.
Proof.
  intros r ts H Hsilent. inversion H; subst.
  - congruence.
  - assumption.
Qed.

Lemma gen_seq_inv : forall {a b ts},
  gen (E_seq a b) ts ->
  exists ts1 ts2, ts = ts1 ++ ts2 /\ gen a ts1 /\ gen b ts2.
Proof. intros a b ts H. inversion H; subst. eauto 6. Qed.

Lemma gen_alt_inv : forall {a b ts},
  gen (E_alt a b) ts -> gen a ts \/ gen b ts.
Proof. intros a b ts H. inversion H; subst; auto. Qed.

Lemma gen_opt_inv : forall {a ts},
  gen (E_opt a) ts -> gen a ts \/ ts = [].
Proof. intros a ts H. inversion H; subst; auto. Qed.

Lemma gen_plus_inv : forall {a ts},
  gen (E_plus a) ts -> gen (E_seq a (E_star a)) ts.
Proof. intros a ts H. inversion H; subst. assumption. Qed.

Lemma gen_expect_inv : forall {a ts}, gen (E_expect a) ts -> gen a ts.
Proof. intros a ts H. inversion H; subst. assumption. Qed.

Lemma gen_star_inv : forall {a ts},
  gen (E_star a) ts ->
  ts = [] \/ exists ts1 ts2, ts = ts1 ++ ts2 /\ gen a ts1 /\ gen (E_star a) ts2.
Proof.
  intros a ts H. inversion H; subst.
  - left. reflexivity.
  - right. eauto 6.
Qed.

(* A rule with no core derivation: a rule that makes a node but is outside the
   fragment contributes nothing. *)
Lemma gen_outside : forall {r ts},
  gen (E_rule r) ts -> silent r = false -> core_rule r = false -> False.
Proof.
  intros r ts H Hsilent Hcore.
  destruct (gen_node_inv H Hsilent) as (cs & _ & Hc & _).
  congruence.
Qed.

(* Induction on a star by its parts: the property holds of the empty forest and
   is preserved by prepending a forest the starred expression produces. *)
Lemma gen_star_ind : forall a (P : list tree -> Prop),
  P [] ->
  (forall ts1 ts2, gen a ts1 -> P ts2 -> P (ts1 ++ ts2)) ->
  forall ts, gen (E_star a) ts -> P ts.
Proof.
  intros a P Hnil Hcons ts H.
  remember (E_star a) as e eqn:Heq.
  induction H; try discriminate Heq.
  - exact Hnil.
  - injection Heq as <-.
    apply Hcons; [ assumption | apply IHgen2; reflexivity ].
Qed.

(* ---- the children of each core node ---- *)

Ltac text_leaf H := apply gen_text_inv in H; subst.

Tactic Notation "split_seq" hyp(H) "as" simple_intropattern(p) :=
  destruct (gen_seq_inv H) as p; clear H.

Lemma shape_name : forall cs,
  gen (body R_name) cs -> exists x, cs = [Leaf (TName x)].
Proof. intros cs H. exact (gen_name_inv H). Qed.

Lemma shape_number : forall cs,
  gen (body R_number) cs -> exists n, cs = [Leaf (TNum n)].
Proof. intros cs H. exact (gen_number_inv H). Qed.

(* a name node, as a child *)
Lemma gen_ident : forall ts,
  gen (E_rule R_name) ts -> exists x, ts = [ident x].
Proof.
  intros ts H.
  destruct (gen_node_inv H eq_refl) as (cs & -> & _ & Hbody).
  destruct (shape_name cs Hbody) as (x & ->).
  exists x. reflexivity.
Qed.

Lemma shape_access : forall cs,
  gen (body R_access) cs -> exists l, cs = [sym "."; ident l].
Proof.
  intros cs H. simpl in H.
  split_seq H as (ts1 & ts2 & -> & H1 & H2). text_leaf H1.
  apply gen_expect_inv in H2.
  destruct (gen_ident _ H2) as (l & ->).
  exists l. reflexivity.
Qed.

Lemma shape_take : forall cs,
  gen (body R_take) cs -> exists l, cs = [sym "::"; ident l].
Proof.
  intros cs H. simpl in H.
  split_seq H as (ts1 & ts2 & -> & H1 & H2). text_leaf H1.
  apply gen_expect_inv in H2.
  destruct (gen_ident _ H2) as (l & ->).
  exists l. reflexivity.
Qed.

Definition has (r : rule) (cs : list tree) : Prop :=
  exists c, In (Node r c) cs.

Ltac absurd_has H :=
  destruct H as (? & Hin); simpl in Hin;
  repeat (destruct Hin as [Hin | Hin]; [ discriminate Hin | ]);
  contradiction.

Lemma gen_node_of : forall {r ts},
  gen (E_rule r) ts -> silent r = false ->
  exists cs, ts = [Node r cs] /\ gen (body r) cs.
Proof.
  intros r ts H Hsilent.
  destruct (gen_node_inv H Hsilent) as (cs & Hts & _ & Hbody).
  exists cs. split; assumption.
Qed.

Lemma shape_declaration : forall cs,
  gen (body R_declaration) cs ->
  exists x c,
    cs = [ident x; sym "="; Node R_value c]
    \/ cs = [ident x; sym "="; Node R_value c; sym ";"].
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsx & ts1 & -> & Hx & H1).
  destruct (gen_ident _ Hx) as (x & ->).
  split_seq H1 as (tseq & ts2 & -> & Hseq & H2). text_leaf Hseq.
  split_seq H2 as (tsv & tssemi & -> & Hv & Hsemi).
  apply gen_expect_inv in Hv.
  destruct (gen_alt_inv Hv) as [Hforeign | Hvalue].
  - exfalso. exact (gen_outside Hforeign eq_refl eq_refl).
  - destruct (gen_node_of Hvalue eq_refl) as (c & -> & _).
    exists x, c.
    destruct (gen_opt_inv Hsemi) as [Hs | ->].
    + apply gen_text_inv in Hs. subst. right. reflexivity.
    + left. reflexivity.
Qed.

Lemma shape_field : forall cs,
  gen (body R_field) cs ->
  exists l c, cs = [ident l; sym ":"; Node R_expr c].
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsl & ts1 & -> & Hl & H1).
  destruct (gen_ident _ Hl) as (l & ->).
  split_seq H1 as (tscolon & ts2 & -> & Hcolon & H2). text_leaf Hcolon.
  apply gen_expect_inv in H2.
  destruct (gen_node_of H2 eq_refl) as (c & -> & _).
  exists l, c. reflexivity.
Qed.

Lemma shape_params : forall cs,
  gen (body R_params) cs ->
  exists x tail,
    cs = ident x :: tail
    /\ gen (E_star (E_seq (E_term (T_text ",")) (E_rule R__param))) tail.
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsx & tail & -> & Hx & Htail).
  assert (Hname : gen (E_rule R_name) tsx).
  { pose proof (gen_splice_inv Hx eq_refl) as Halt. simpl in Halt.
    destruct (gen_alt_inv Halt) as [Hrec | Hrest].
    - exfalso. exact (gen_outside Hrec eq_refl eq_refl).
    - destruct (gen_alt_inv Hrest) as [Hlist | Hname].
      + exfalso. exact (gen_outside Hlist eq_refl eq_refl).
      + exact Hname. }
  destruct (gen_ident _ Hname) as (x & ->).
  exists x, tail. split; [ reflexivity | exact Htail ].
Qed.

Lemma shape_param : forall ts,
  gen (E_rule R__param) ts -> exists x, ts = [ident x].
Proof.
  intros ts Hx.
  pose proof (gen_splice_inv Hx eq_refl) as Halt. simpl in Halt.
  destruct (gen_alt_inv Halt) as [Hrec | Hrest].
  - exfalso. exact (gen_outside Hrec eq_refl eq_refl).
  - destruct (gen_alt_inv Hrest) as [Hlist | Hname].
    + exfalso. exact (gen_outside Hlist eq_refl eq_refl).
    + exact (gen_ident _ Hname).
Qed.

Lemma shape_arguments : forall cs,
  gen (body R_arguments) cs ->
  exists c tail fin,
    cs = Node R_expr c :: tail ++ fin
    /\ gen (E_star (E_seq (E_term (T_text ",")) (E_rule R_expr))) tail
    /\ (fin = [] \/ fin = [sym ","]).
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsa & ts1 & -> & Ha & H1).
  destruct (gen_node_of Ha eq_refl) as (c & -> & _).
  split_seq H1 as (tail & fin & -> & Htail & Hfin).
  exists c, tail, fin. split; [ reflexivity | split; [ exact Htail | ] ].
  destruct (gen_opt_inv Hfin) as [Hcomma | ->].
  - apply gen_text_inv in Hcomma. subst. right. reflexivity.
  - left. reflexivity.
Qed.

Lemma shape_call : forall cs,
  gen (body R_call) cs -> has R_arguments cs ->
  exists args, cs = [sym "("; Node R_arguments args; sym ")"].
Proof.
  intros cs H Hhas. simpl in H.
  split_seq H as (tsl & ts1 & -> & Hl & H1). text_leaf Hl.
  split_seq H1 as (tsa & tsr & -> & Ha & Hr).
  apply gen_expect_inv in Hr. text_leaf Hr.
  destruct (gen_opt_inv Ha) as [Hargs | ->].
  - destruct (gen_node_of Hargs eq_refl) as (args & -> & _).
    exists args. reflexivity.
  - exfalso. absurd_has Hhas.
Qed.

Lemma shape_boolean : forall cs,
  gen (body R_boolean) cs ->
  cs = [Node R_true_lit [sym "true"]] \/ cs = [Node R_false_lit [sym "false"]].
Proof.
  intros cs H. simpl in H.
  destruct (gen_alt_inv H) as [Ht | Hf].
  - left. destruct (gen_node_of Ht eq_refl) as (c & -> & Hc).
    simpl in Hc. apply gen_text_inv in Hc. subst. reflexivity.
  - right. destruct (gen_node_of Hf eq_refl) as (c & -> & Hc).
    simpl in Hc. apply gen_text_inv in Hc. subst. reflexivity.
Qed.

Lemma shape_local : forall cs,
  gen (body R_local) cs -> has R_expr cs ->
  exists d b, cs = [Node R_declaration d; Node R_expr b].
Proof.
  intros cs H Hhas. simpl in H.
  split_seq H as (tsd & ts1 & -> & Hd & H1).
  destruct (gen_node_of Hd eq_refl) as (d & -> & _).
  destruct (gen_opt_inv H1) as [Hb | ->].
  - destruct (gen_node_of Hb eq_refl) as (b & -> & _).
    exists d, b. reflexivity.
  - exfalso. absurd_has Hhas.
Qed.

Lemma shape_function : forall cs,
  gen (body R_function) cs -> has R_params cs -> has R_expr cs ->
  exists kw ps b,
    cs = [Leaf kw; sym "("; Node R_params ps; sym ")"; sym "do"; Node R_expr b; sym "done"].
Proof.
  intros cs H Hparams Hbody. simpl in H.
  split_seq H as (tskw & ts1 & -> & Hkw & H1).
  split_seq H1 as (tsl & ts2 & -> & Hl & H2).
  apply gen_expect_inv in Hl. text_leaf Hl.
  split_seq H2 as (tsp & ts3 & -> & Hp & H3).
  split_seq H3 as (tsr & ts4 & -> & Hr & H4).
  apply gen_expect_inv in Hr. text_leaf Hr.
  split_seq H4 as (tsd & ts5 & -> & Hd & H5).
  apply gen_expect_inv in Hd. text_leaf Hd.
  split_seq H5 as (tsb & tsend & -> & Hb & Hend).
  apply gen_expect_inv in Hend. text_leaf Hend.
  assert (Hkw' : exists kw, tskw = [Leaf kw]).
  { destruct (gen_alt_inv Hkw) as [Hk | Hk].
    - apply gen_text_inv in Hk. eauto.
    - destruct (gen_alt_inv Hk) as [Hk' | Hk'];
        apply gen_text_inv in Hk'; eauto. }
  destruct Hkw' as (kw & ->).
  destruct (gen_opt_inv Hp) as [Hps | ->].
  - destruct (gen_node_of Hps eq_refl) as (ps & -> & _).
    destruct (gen_opt_inv Hb) as [Hbd | ->].
    + destruct (gen_node_of Hbd eq_refl) as (b & -> & _).
      exists kw, ps, b. reflexivity.
    + exfalso. absurd_has Hbody.
  - exfalso.
    destruct (gen_opt_inv Hb) as [Hbd | ->].
    + destruct (gen_node_of Hbd eq_refl) as (b & -> & _). absurd_has Hparams.
    + absurd_has Hparams.
Qed.

Lemma shape_record_item : forall ts,
  gen (E_rule R__record_item) ts -> exists c, ts = [Node R_field c].
Proof.
  intros ts H.
  pose proof (gen_splice_inv H eq_refl) as Halt. simpl in Halt.
  destruct (gen_alt_inv Halt) as [Hspread | Hfield].
  - exfalso. exact (gen_outside Hspread eq_refl eq_refl).
  - destruct (gen_node_of Hfield eq_refl) as (c & -> & _).
    exists c. reflexivity.
Qed.

Lemma shape_record : forall cs,
  gen (body R_record) cs ->
  exists rest,
    cs = sym "{" :: rest
    /\ (rest = [sym "}"]
        \/ exists c tail fin,
             rest = Node R_field c :: tail ++ fin ++ [sym "}"]
             /\ gen (E_star (E_seq (E_term (T_text ",")) (E_rule R__record_item))) tail
             /\ (fin = [] \/ fin = [sym ","])).
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsl & ts1 & -> & Hl & H1). text_leaf Hl.
  split_seq H1 as (tsi & tsr & -> & Hitems & Hr).
  apply gen_expect_inv in Hr. text_leaf Hr.
  destruct (gen_opt_inv Hitems) as [Hsome | ->].
  - split_seq Hsome as (tsf & ts2 & -> & Hf & H2).
    split_seq H2 as (tail & fin & -> & Htail & Hfin).
    destruct (shape_record_item _ Hf) as (c & ->).
    exists (Node R_field c :: tail ++ fin ++ [sym "}"]).
    split; [ simpl; rewrite <- app_assoc; reflexivity | right ].
    exists c, tail, fin. split; [ reflexivity | split; [ exact Htail | ] ].
    destruct (gen_opt_inv Hfin) as [Hcomma | ->].
    + apply gen_text_inv in Hcomma. subst. right. reflexivity.
    + left. reflexivity.
  - exists [sym "}"]. split; [ reflexivity | left; reflexivity ].
Qed.

Lemma shape_string : forall cs, gen (body R_string) cs -> cs = [Leaf TStr].
Proof. intros cs H. simpl in H. inversion H. reflexivity. Qed.

Lemma shape_conditional : forall cs,
  gen (body R_conditional) cs -> In (sym "else") cs ->
  exists a b c,
    cs = [sym "if"; Node R_expr a; sym "then"; Node R_expr b; sym "else"; Node R_expr c;
          sym "done"].
Proof.
  intros cs H Hhas. simpl in H.
  split_seq H as (tsif & ts1 & -> & Hif & H1). text_leaf Hif.
  split_seq H1 as (tsa & ts2 & -> & Ha & H2).
  destruct (gen_node_of Ha eq_refl) as (a & -> & _).
  split_seq H2 as (tsthen & ts3 & -> & Hthen & H3).
  apply gen_expect_inv in Hthen. text_leaf Hthen.
  split_seq H3 as (tsb & ts4 & -> & Hb & H4).
  apply gen_expect_inv in Hb.
  destruct (gen_node_of Hb eq_refl) as (b & -> & _).
  split_seq H4 as (tsel & tsdone & -> & Hel & Hdone).
  apply gen_expect_inv in Hdone. text_leaf Hdone.
  destruct (gen_opt_inv Hel) as [Helse | ->].
  - pose proof (gen_splice_inv Helse eq_refl) as Hbody. simpl in Hbody.
    split_seq Hbody as (tse & ts5 & -> & He & Hc). text_leaf He.
    apply gen_expect_inv in Hc.
    destruct (gen_node_of Hc eq_refl) as (c & -> & _).
    exists a, b, c. reflexivity.
  - exfalso. simpl in Hhas.
    repeat (destruct Hhas as [Hhas | Hhas]; [ discriminate Hhas | ]). contradiction.
Qed.

Lemma shape_goat : forall cs,
  gen (body R_goat) cs -> has R_expr cs ->
  exists b, cs = [Node R_expr b].
Proof.
  intros cs H Hhas. simpl in H.
  split_seq H as (tstags & ts1 & -> & Htags & H1).
  split_seq H1 as (tse & tseoi & -> & He & Heoi).
  assert (Hnone : tstags = []).
  { destruct (gen_star_inv Htags) as [Hn | (t1 & t2 & _ & Ht1 & _)];
      [ exact Hn | exfalso; exact (gen_outside Ht1 eq_refl eq_refl) ]. }
  subst tstags. inversion Heoi; subst.
  destruct (gen_opt_inv He) as [Hexpr | ->].
  - destruct (gen_node_of Hexpr eq_refl) as (b & -> & _).
    exists b. reflexivity.
  - exfalso. absurd_has Hhas.
Qed.

(* ---- expressions: a block is declarations and then a chain ---- *)

Ltac dead :=
  match goal with
  | H : gen (E_rule _) _ |- False => exact (gen_outside H eq_refl eq_refl)
  end.

Definition is_op_rule (r : rule) : bool :=
  match r with
  | R_plus | R_minus | R_multiply | R_floor_divide | R_divide | R_remainder
  | R_equal | R_not_equal | R_lte | R_lt | R_gte | R_gt => true
  | _ => false
  end.

(* How many operator nodes sit among the children. *)
Fixpoint count_ops (cs : list tree) : nat :=
  match cs with
  | Node r _ :: rest => (if is_op_rule r then 1 else 0) + count_ops rest
  | _ :: rest => count_ops rest
  | [] => 0
  end.

Lemma count_ops_app : forall a b, count_ops (a ++ b) = count_ops a + count_ops b.
Proof.
  induction a as [| t a IH]; intros b; [ reflexivity | ].
  destruct t as [k | r c]; simpl; rewrite IH; lia.
Qed.

Lemma count_ops_op : forall o, count_ops [op_tree o] = 1.
Proof. intros o. destruct o; reflexivity. Qed.

Ltac op_case H o :=
  destruct (gen_node_of H eq_refl) as (? & -> & Hc);
  simpl in Hc; apply gen_text_inv in Hc; subst; exists o; reflexivity.

Ltac infix_step Halt o :=
  destruct (gen_alt_inv Halt) as [Hh | Halt']; [ op_case Hh o | clear Halt; rename Halt' into Halt ].

Lemma infix_shape : forall ts,
  gen (E_rule R__infix) ts -> exists o, ts = [op_tree o].
Proof.
  intros ts H.
  pose proof (gen_splice_inv H eq_refl) as Halt. simpl in Halt.
  destruct (gen_alt_inv Halt) as [Hand | Halt1].
  { exfalso. dead. }
  destruct (gen_alt_inv Halt1) as [Hor | Halt2].
  { exfalso. dead. }
  infix_step Halt2 bop_add.
  infix_step Halt2 bop_sub.
  infix_step Halt2 bop_mul.
  infix_step Halt2 bop_fdiv.
  infix_step Halt2 bop_div.
  infix_step Halt2 bop_rem.
  infix_step Halt2 bop_eq.
  infix_step Halt2 bop_ne.
  infix_step Halt2 bop_lte.
  infix_step Halt2 bop_lt.
  infix_step Halt2 bop_gte.
  op_case Halt2 bop_gt.
Qed.

Lemma more_math_shape : forall ts,
  gen (E_rule R__more_math) ts ->
  exists o c2, ts = op_tree o :: c2 /\ gen (E_rule R__operand) c2.
Proof.
  intros ts H.
  pose proof (gen_splice_inv H eq_refl) as Hseq. simpl in Hseq.
  split_seq Hseq as (tsi & ts1 & -> & Hinfix & Hop).
  destruct (infix_shape _ Hinfix) as (o & ->).
  apply gen_expect_inv in Hop.
  exists o, ts1. split; [ reflexivity | exact Hop ].
Qed.

Lemma star_more_math_zero : forall ts,
  gen (E_star (E_rule R__more_math)) ts -> count_ops ts = 0 -> ts = [].
Proof.
  intros ts H Hcount.
  destruct (gen_star_inv H) as [Hnil | (ts1 & ts2 & -> & H1 & _)]; [ exact Hnil | ].
  exfalso. destruct (more_math_shape _ H1) as (o & c2 & -> & _).
  rewrite count_ops_app in Hcount. cbn [app] in Hcount.
  change (op_tree o :: c2) with ([op_tree o] ++ c2) in Hcount.
  rewrite count_ops_app, count_ops_op in Hcount. lia.
Qed.

Lemma operand_term : forall cs,
  gen (E_rule R__operand) cs -> gen (E_rule R__term) cs.
Proof.
  intros cs H.
  pose proof (gen_splice_inv H eq_refl) as Hseq. simpl in Hseq.
  split_seq Hseq as (tsn & ts1 & -> & Hnot & Hterm).
  destruct (gen_star_inv Hnot) as [-> | (t1 & t2 & _ & Ht1 & _)].
  - exact Hterm.
  - exfalso. dead.
Qed.

Lemma term_shape : forall cs,
  gen (E_rule R__term) cs ->
  exists prim posts,
    cs = prim ++ posts
    /\ gen (E_rule R__primary) prim
    /\ gen (E_star (E_rule R__postfix)) posts.
Proof.
  intros cs H.
  pose proof (gen_splice_inv H eq_refl) as Halt. simpl in Halt.
  destruct (gen_alt_inv Halt) as [Hneg | Hseq].
  - exfalso. dead.
  - split_seq Hseq as (prim & posts & -> & Hprim & Hposts).
    exists prim, posts. split; [ reflexivity | split; assumption ].
Qed.

Lemma primary_shape : forall prim,
  gen (E_rule R__primary) prim ->
  (exists c, prim = [Node R_number c])
  \/ (exists c, prim = [Node R_string c])
  \/ (exists c, prim = [Node R_boolean c])
  \/ (exists c, prim = [Node R_conditional c])
  \/ (exists c, prim = [Node R_local c])
  \/ (exists c, prim = [Node R_function c])
  \/ (exists c, prim = [Node R_record c])
  \/ (exists c, prim = [Node R_name c])
  \/ (exists c, prim = [sym "("; Node R_expr c; sym ")"]).
Proof.
  intros prim H.
  pose proof (gen_splice_inv H eq_refl) as Halt. simpl in Halt.
  destruct (gen_alt_inv Halt) as [Hnumber | Halt1].
  { destruct (gen_node_of Hnumber eq_refl) as (c & -> & _). left. eauto. }
  destruct (gen_alt_inv Halt1) as [Hstring | Halt2].
  { destruct (gen_node_of Hstring eq_refl) as (c & -> & _). right; left. eauto. }
  destruct (gen_alt_inv Halt2) as [Hboolean | Halt3].
  { destruct (gen_node_of Hboolean eq_refl) as (c & -> & _). right; right; left. eauto. }
  destruct (gen_alt_inv Halt3) as [Hdestructure | Halt4].
  { exfalso. dead. }
  destruct (gen_alt_inv Halt4) as [Hlocal | Halt5].
  { destruct (gen_node_of Hlocal eq_refl) as (c & -> & _). right; right; right; right; left. eauto. }
  destruct (gen_alt_inv Halt5) as [Hfunction | Halt6].
  { destruct (gen_node_of Hfunction eq_refl) as (c & -> & _).
    right; right; right; right; right; left. eauto. }
  destruct (gen_alt_inv Halt6) as [Hconditional | Halt7].
  { destruct (gen_node_of Hconditional eq_refl) as (c & -> & _).
    right; right; right; left. eauto. }
  destruct (gen_alt_inv Halt7) as [Hmatch | Halt8].
  { exfalso. dead. }
  destruct (gen_alt_inv Halt8) as [Hrepeat | Halt9].
  { exfalso. dead. }
  destruct (gen_alt_inv Halt9) as [Hcount | Halt10].
  { exfalso. dead. }
  destruct (gen_alt_inv Halt10) as [Heach | Halt11].
  { exfalso. dead. }
  destruct (gen_alt_inv Halt11) as [Hrecord | Halt12].
  { destruct (gen_node_of Hrecord eq_refl) as (c & -> & _).
    right; right; right; right; right; right; left. eauto. }
  destruct (gen_alt_inv Halt12) as [Hlist | Hrest].
  { exfalso. dead. }
  destruct (gen_alt_inv Hrest) as [Hname | Hparen].
  - destruct (gen_node_of Hname eq_refl) as (c & -> & _).
    right; right; right; right; right; right; right; left. eauto.
  - split_seq Hparen as (tsl & ts1 & -> & Hl & H1). text_leaf Hl.
    split_seq H1 as (tse & tsr & -> & He & Hr).
    apply gen_expect_inv in Hr. text_leaf Hr.
    destruct (gen_node_of He eq_refl) as (c & -> & _).
    right; right; right; right; right; right; right; right. exists c. reflexivity.
Qed.

Lemma term_ops : forall cs, gen (E_rule R__term) cs -> count_ops cs = 0.
Proof.
  intros cs H.
  destruct (term_shape cs H) as (prim & posts & -> & Hprim & Hposts).
  rewrite count_ops_app.
  assert (Hp : count_ops prim = 0).
  { destruct (primary_shape prim Hprim) as
      [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | (c & ->)]]]]]]]];
      reflexivity. }
  assert (Hq : count_ops posts = 0).
  { apply (gen_star_ind (E_rule R__postfix) (fun ps => count_ops ps = 0)); [ | | exact Hposts ].
    - reflexivity.
    - intros ts1 ts2 Hpost IH. rewrite count_ops_app, IH.
      pose proof (gen_splice_inv Hpost eq_refl) as Halt. simpl in Halt.
      destruct (gen_alt_inv Halt) as [Ha | Halt'].
      + destruct (gen_node_of Ha eq_refl) as (c & -> & _). reflexivity.
      + destruct (gen_alt_inv Halt') as [Ht | Hc].
        * destruct (gen_node_of Ht eq_refl) as (c & -> & _). reflexivity.
        * destruct (gen_node_of Hc eq_refl) as (c & -> & _). reflexivity. }
  lia.
Qed.

Lemma expr_part : forall cs,
  gen (body R_expr) cs -> gen (E_rule R__part) cs.
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsp & ts1 & -> & Hpart & H1).
  split_seq H1 as (tsstar & tsopt & -> & Hstar & Hopt).
  assert (Hstar0 : tsstar = []).
  { destruct (gen_star_inv Hstar) as [Hnil | (t1 & t2 & _ & Ht1 & _)].
    - exact Hnil.
    - exfalso. split_seq Ht1 as (tss & tsp2 & _ & Hsequel & _). dead. }
  assert (Hopt0 : tsopt = []).
  { destruct (gen_opt_inv Hopt) as [Hsequel | Hnil].
    - exfalso. dead.
    - exact Hnil. }
  rewrite Hstar0, Hopt0. simpl. rewrite app_nil_r. exact Hpart.
Qed.

Lemma part_shape : forall cs,
  gen (E_rule R__part) cs ->
  (exists ds ss,
     cs = ds ++ ss
     /\ gen (E_plus (E_rule R_declaration)) ds
     /\ (gen (E_rule R__statement) ss \/ ss = []))
  \/ gen (E_rule R__statement) cs.
Proof.
  intros cs H.
  pose proof (gen_splice_inv H eq_refl) as Halt. simpl in Halt.
  destruct (gen_alt_inv Halt) as [Hdecls | Hstatement].
  - left. split_seq Hdecls as (ds & ss & -> & Hds & Hss).
    exists ds, ss. split; [ reflexivity | split; [ exact Hds | ] ].
    destruct (gen_opt_inv Hss) as [Hs | Hnil]; [ left | right ]; assumption.
  - right. exact Hstatement.
Qed.

Lemma declaration_nodes : forall ds,
  gen (E_star (E_rule R_declaration)) ds ->
  Forall (fun t => exists c, t = Node R_declaration c) ds.
Proof.
  intros ds H.
  apply (gen_star_ind (E_rule R_declaration)); [ | | exact H ].
  - apply Forall_nil.
  - intros ts1 ts2 H1 IH.
    destruct (gen_node_of H1 eq_refl) as (c & -> & _).
    apply Forall_cons; [ eauto | exact IH ].
Qed.

Lemma statement_math_value : forall cs,
  gen (body R_value) cs ->
  gen (E_seq (E_rule R__operand) (E_star (E_rule R__more_math))) cs.
Proof. intros cs H. exact H. Qed.

Lemma statement_math : forall cs,
  gen (E_rule R__statement) cs ->
  gen (E_seq (E_rule R__operand) (E_star (E_rule R__more_math))) cs.
Proof.
  intros cs H.
  pose proof (gen_splice_inv H eq_refl) as Hseq. simpl in Hseq.
  exact Hseq.
Qed.

(* ---- what the fragment excludes beyond its rules, and when a tree is valid ---- *)

Definition last_is_decl (cs : list tree) : Prop :=
  exists c, List.last cs (Leaf TStr) = Node R_declaration c.

(* No access is followed by a call. *)
Fixpoint no_dot (cs : list tree) : Prop :=
  match cs with
  | Node R_access _ :: rest => ~ starts_call rest /\ no_dot rest
  | _ :: rest => no_dot rest
  | [] => True
  end.

(* The postfixes of a variable: a leading dot call is allowed. *)
Definition head_ok (ps : list tree) : Prop :=
  match ps with
  | Node R_access _ :: Node R_call _ :: rest => no_dot rest
  | _ => no_dot ps
  end.

(* A dot call has a variable receiver: the chain after any bindings is either
   headed by a name or has no dot call. *)
Fixpoint dots_ok (cs : list tree) : Prop :=
  match cs with
  | Node R_declaration _ :: rest => dots_ok rest
  | Node R_name _ :: rest => head_ok rest
  | _ => no_dot cs
  end.

(* An expression with an operator has exactly one, and no dot call: its
   operands are chains, and precedence between operators is not modelled. *)
Definition ops_ok (cs : list tree) : Prop :=
  count_ops cs = 0 \/ (count_ops cs = 1 /\ no_dot cs).

(* The fragment has no empty parameter list, empty body, empty call, empty
   program, block that ends in a binding, or dot call on a receiver that is not
   a variable. *)
Definition complete_node (r : rule) (cs : list tree) : Prop :=
  match r with
  | R_goat | R_local => has R_expr cs
  | R_function => has R_params cs /\ has R_expr cs
  | R_call => has R_arguments cs
  | R_expr => ~ last_is_decl cs /\ dots_ok cs /\ ops_ok cs
  | R_value => dots_ok cs /\ ops_ok cs
  | R_conditional => In (sym "else") cs
  | _ => True
  end.

Inductive Complete : tree -> Prop :=
  | Cp_leaf : forall k, Complete (Leaf k)
  | Cp_node : forall r cs,
      complete_node r cs -> Forall Complete cs -> Complete (Node r cs).

Inductive core_tree : tree -> Prop :=
  | Core_leaf : forall k, core_tree (Leaf k)
  | Core_node : forall r cs,
      core_rule r = true -> Forall core_tree cs -> core_tree (Node r cs).

Definition valid (t : tree) : Prop :=
  match t with
  | Leaf _ => True
  | Node r _ => gen (E_rule r) [t]
  end.

Lemma gen_valid : forall e ts, gen e ts -> Forall valid ts.
Proof.
  intros e ts H. induction H.
  - apply Forall_cons; [ exact I | apply Forall_nil ].
  - apply Forall_cons; [ exact I | apply Forall_nil ].
  - apply Forall_cons; [ exact I | apply Forall_nil ].
  - apply Forall_cons; [ exact I | apply Forall_nil ].
  - apply Forall_nil.
  - (* node *)
    apply Forall_cons; [ | apply Forall_nil ].
    simpl. apply G_node; assumption.
  - (* splice *) assumption.
  - (* seq *) apply Forall_app. split; assumption.
  - assumption.
  - assumption.
  - apply Forall_nil.
  - apply Forall_app. split; assumption.
  - assumption.
  - assumption.
  - apply Forall_nil.
  - assumption.
Qed.

(* ---- from the PEG relation to the forests it can produce ---- *)

Lemma term_step_gen : forall t s ts s',
  term_step t s = Ok ts s' -> gen (E_term t) ts.
Proof.
  intros t s ts s' H. destruct s as [| k s0].
  - (* no tokens left: only the end of input matches *)
    destruct t; simpl in H; try discriminate H.
    injection H as <- _. apply G_eoi.
  - destruct t as [txt | | | | ]; destruct k as [x | n | | y]; simpl in H;
      try discriminate H.
    + (* text *)
      destruct (String.eqb txt y) eqn:Hmatch; [ | discriminate H ].
      injection H as <- _. apply String.eqb_eq in Hmatch. subst.
      apply G_text.
    + (* name *) injection H as <- _. apply G_name.
    + (* number *) injection H as <- _. apply G_number.
    + (* string *) injection H as <- _. apply G_string.
Qed.

Lemma peg_gen : forall e s res,
  peg e s res ->
  forall ts s', res = Ok ts s' -> Forall core_tree ts -> gen e ts.
Proof.
  intros e s res D.
  induction D as
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
    intros out s_out Hres Hcore.
  - (* term *) exact (term_step_gen t s out s_out Hres).
  - (* rule *)
    destruct res as [| ts0 s0]; [ discriminate Hres | ].
    simpl in Hres. destruct (silent r) eqn:Hsilent.
    + injection Hres as <- <-.
      apply G_splice; [ exact Hsilent | ]. apply (IH ts0 s0); [ reflexivity | exact Hcore ].
    + injection Hres as <- <-.
      inversion Hcore as [| ? ? Hnode _]; subst.
      inversion Hnode as [? | ? cs' Hrule Hkids]; subst.
      apply G_node; [ exact Hsilent | exact Hrule | ].
      apply (IH ts0 s0); [ reflexivity | exact Hkids ].
  - (* seq *)
    destruct res as [| ts2 s2]; [ discriminate Hres | ].
    simpl in Hres. injection Hres as <- <-.
    apply Forall_app in Hcore as [Hcore1 Hcore2].
    apply G_seq.
    + apply (IHa ts s1); [ reflexivity | exact Hcore1 ].
    + apply (IHb ts2 s2); [ reflexivity | exact Hcore2 ].
  - (* seq, first part fails *) discriminate Hres.
  - (* alt, left *)
    injection Hres as <- <-. apply G_alt_left. apply (IHa ts s'); [ reflexivity | exact Hcore ].
  - (* alt, right *)
    apply G_alt_right. apply (IHb out s_out); assumption.
  - (* star, stops *)
    injection Hres as <- <-. apply G_star_nil.
  - (* star, steps *)
    injection Hres as <- <-.
    apply Forall_app in Hcore as [Hcore1 Hcore2].
    apply G_star_cons.
    + apply (IHa ts s1); [ reflexivity | exact Hcore1 ].
    + apply (IHstar ts' s2); [ reflexivity | exact Hcore2 ].
  - (* plus *)
    apply G_plus. apply (IH out s_out); assumption.
  - (* opt, present *)
    injection Hres as <- <-. apply G_opt_some. apply (IHa ts s'); [ reflexivity | exact Hcore ].
  - (* opt, absent *)
    injection Hres as <- <-. apply G_opt_none.
  - (* expect *)
    apply G_expect. apply (IH out s_out); assumption.
Qed.

(* ---- totality: every valid, complete core tree has a denotation ---- *)

Section Totality.

  Variable var_of : string -> termvar.
  Variable tbl : list string.

  (* What a node of each core kind must yield, given its children do. *)
  Definition TotKind (t : tree) : Prop :=
    match t with
    | Leaf _ => True
    | Node r cs =>
        match r with
        | R_number | R_boolean | R_name | R_function | R_record | R_local
        | R_expr | R_value | R_string | R_conditional =>
            exists e, Den var_of tbl t e
        | R_declaration => exists x v, Den_decl var_of tbl t x v
        | R_field => exists l e, Den_field var_of tbl t l e
        | R_access => exists l, cs = [sym "."; ident l]
        | R_take => exists l, cs = [sym "::"; ident l]
        | R_call =>
            exists args es,
              cs = [sym "("; Node R_arguments args; sym ")"]
              /\ Den_args var_of tbl args es
        | R_arguments => exists es, Den_args var_of tbl cs es
        | R_params => exists xs, Den_params var_of tbl cs xs
        | _ => True
        end
    end.

  Lemma posts_den : forall ps,
    gen (E_star (E_rule R__postfix)) ps -> Forall TotKind ps -> no_dot ps ->
    forall acc, exists e', Den_posts var_of tbl acc ps e'.
  Proof.
    intros ps H.
    apply (gen_star_ind (E_rule R__postfix)
             (fun ps => Forall TotKind ps -> no_dot ps ->
                        forall acc, exists e', Den_posts var_of tbl acc ps e'));
      [ | | exact H ].
    - (* no postfix left *)
      intros _ _ acc. exists acc. apply DP_nil.
    - intros ts1 ts2 Hpost IH Hkids Hnd acc.
      apply Forall_app in Hkids as [Hkids1 Hkids2].
      pose proof (gen_splice_inv Hpost eq_refl) as Halt. simpl in Halt.
      destruct (gen_alt_inv Halt) as [Haccess | Htake_call].
      + (* .label *)
        destruct (gen_node_of Haccess eq_refl) as (c & -> & _).
        inversion Hkids1 as [| ? ? Hkid _]; subst. simpl in Hkid.
        destruct Hkid as (l & ->).
        simpl in Hnd. destruct Hnd as [Hnocall Hnd2].
        destruct (IH Hkids2 Hnd2 (e_proj acc (lab tbl l))) as (e' & Hrest).
        exists e'. apply DP_access; assumption.
      + destruct (gen_alt_inv Htake_call) as [Htake | Hcall].
        * (* ::label *)
          destruct (gen_node_of Htake eq_refl) as (c & -> & _).
          inversion Hkids1 as [| ? ? Hkid _]; subst. simpl in Hkid.
          destruct Hkid as (l & ->).
          simpl in Hnd.
          destruct (IH Hkids2 Hnd (e_proj acc (lab tbl l))) as (e' & Hrest).
          exists e'. apply DP_take. exact Hrest.
        * (* (arguments) *)
          destruct (gen_node_of Hcall eq_refl) as (c & -> & _).
          inversion Hkids1 as [| ? ? Hkid _]; subst. simpl in Hkid.
          destruct Hkid as (args & es & -> & Hargs).
          simpl in Hnd.
          destruct (IH Hkids2 Hnd (apps acc es)) as (e' & Hrest).
          exists e'. apply DP_call with (es := es); assumption.
  Qed.

  Lemma posts_den_var : forall x ps,
    gen (E_star (E_rule R__postfix)) ps -> Forall TotKind ps -> head_ok ps ->
    exists e', Den_posts var_of tbl (e_fvar_f x) ps e'.
  Proof.
    intros x ps H Hkids Hhead.
    destruct (gen_star_inv H) as [-> | (ts1 & ts2 & -> & Hpost & Hrest)].
    - exists (e_fvar_f x). apply DP_nil.
    - apply Forall_app in Hkids as [Hkids1 Hkids2].
      pose proof (gen_splice_inv Hpost eq_refl) as Halt. simpl in Halt.
      destruct (gen_alt_inv Halt) as [Haccess | Htake_call].
      + (* .label, then perhaps a call *)
        destruct (gen_node_of Haccess eq_refl) as (c & -> & _).
        inversion Hkids1 as [| ? ? Hkid _]; subst. simpl in Hkid.
        destruct Hkid as (l & ->).
        destruct (gen_star_inv Hrest) as [-> | (ts3 & ts4 & -> & Hpost3 & Hrest4)].
        * (* nothing after the access *)
          exists (e_proj (e_fvar_f x) (lab tbl l)).
          apply DP_access; [ exact (proj1 Hhead) | apply DP_nil ].
        * pose proof (gen_splice_inv Hpost3 eq_refl) as Halt3. simpl in Halt3.
          apply Forall_app in Hkids2 as [Hkids3 Hkids4].
          destruct (gen_alt_inv Halt3) as [Haccess3 | Htake_call3].
          -- (* a second access: the first is a plain projection *)
             destruct (gen_node_of Haccess3 eq_refl) as (c3 & -> & _).
             assert (Hrest34 : gen (E_star (E_rule R__postfix))
                                 ([Node R_access c3] ++ ts4))
               by (apply G_star_cons; assumption).
             assert (Hk34 : Forall TotKind ([Node R_access c3] ++ ts4))
               by (apply Forall_app; split; assumption).
             destruct (posts_den _ Hrest34 Hk34 (proj2 Hhead)
                         (e_proj (e_fvar_f x) (lab tbl l))) as (e' & Hposts).
             exists e'. apply DP_access; [ exact (proj1 Hhead) | exact Hposts ].
          -- destruct (gen_alt_inv Htake_call3) as [Htake3 | Hcall3].
             ++ (* a take: the first is a plain projection *)
                destruct (gen_node_of Htake3 eq_refl) as (c3 & -> & _).
                assert (Hrest34 : gen (E_star (E_rule R__postfix))
                                    ([Node R_take c3] ++ ts4))
                  by (apply G_star_cons; assumption).
                assert (Hk34 : Forall TotKind ([Node R_take c3] ++ ts4))
                  by (apply Forall_app; split; assumption).
                destruct (posts_den _ Hrest34 Hk34 (proj2 Hhead)
                            (e_proj (e_fvar_f x) (lab tbl l))) as (e' & Hposts).
                exists e'. apply DP_access; [ exact (proj1 Hhead) | exact Hposts ].
             ++ (* a call: a dot call on the variable *)
                destruct (gen_node_of Hcall3 eq_refl) as (c3 & -> & _).
                inversion Hkids3 as [| ? ? Hkid3 _]; subst. simpl in Hkid3.
                destruct Hkid3 as (args & es & -> & Hargs).
                destruct (posts_den ts4 Hrest4 Hkids4 Hhead
                            (apps (e_proj (e_fvar_f x) (lab tbl l)) (e_fvar_f x :: es)))
                  as (e' & Hposts).
                exists e'. apply DP_dot_call with (es := es); assumption.
      + destruct (gen_alt_inv Htake_call) as [Htake | Hcall].
        * (* ::label *)
          destruct (gen_node_of Htake eq_refl) as (c & -> & _).
          inversion Hkids1 as [| ? ? Hkid _]; subst. simpl in Hkid.
          destruct Hkid as (l & ->).
          assert (Hnd : no_dot ts2) by exact Hhead.
          destruct (posts_den ts2 Hrest Hkids2 Hnd (e_proj (e_fvar_f x) (lab tbl l)))
            as (e' & Hposts).
          exists e'. apply DP_take. exact Hposts.
        * (* (arguments) *)
          destruct (gen_node_of Hcall eq_refl) as (c & -> & _).
          inversion Hkids1 as [| ? ? Hkid _]; subst. simpl in Hkid.
          destruct Hkid as (args & es & -> & Hargs).
          destruct (posts_den ts2 Hrest Hkids2 Hhead (apps (e_fvar_f x) es))
            as (e' & Hposts).
          exists e'. apply DP_call with (es := es); assumption.
  Qed.

  Lemma chain_head : forall t posts e0,
    Den var_of tbl t e0 ->
    gen (E_star (E_rule R__postfix)) posts -> Forall TotKind posts ->
    no_dot posts ->
    exists e, Den_chain var_of tbl (t :: posts) e.
  Proof.
    intros t posts e0 Hden Hposts Hkids Hnd.
    destruct (posts_den posts Hposts Hkids Hnd e0) as (e & Hchain).
    exists e. apply DC_head with (e0 := e0); assumption.
  Qed.

  Lemma chain_den : forall cs,
    gen (E_rule R__term) cs -> Forall TotKind cs -> dots_ok cs ->
    exists e, Den_chain var_of tbl cs e.
  Proof.
    intros cs H Hkids Hdots.
    destruct (term_shape cs H) as (prim & posts & -> & Hprim & Hposts).
    apply Forall_app in Hkids as [Hkprim Hkposts].
    destruct (primary_shape prim Hprim) as
      [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | (c & ->)]]]]]]]].
    - (* number *)
      inversion Hkprim as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (e0 & Hden).
      assert (Hnd : no_dot posts) by exact Hdots.
      exact (chain_head _ _ e0 Hden Hposts Hkposts Hnd).
    - (* string *)
      inversion Hkprim as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (e0 & Hden).
      assert (Hnd : no_dot posts) by exact Hdots.
      exact (chain_head _ _ e0 Hden Hposts Hkposts Hnd).
    - (* conditional *)
      inversion Hkprim as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (e0 & Hden).
      assert (Hnd : no_dot posts) by exact Hdots.
      exact (chain_head _ _ e0 Hden Hposts Hkposts Hnd).
    - (* boolean *)
      inversion Hkprim as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (e0 & Hden).
      assert (Hnd : no_dot posts) by exact Hdots.
      exact (chain_head _ _ e0 Hden Hposts Hkposts Hnd).
    - (* local *)
      inversion Hkprim as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (e0 & Hden).
      assert (Hnd : no_dot posts) by exact Hdots.
      exact (chain_head _ _ e0 Hden Hposts Hkposts Hnd).
    - (* function *)
      inversion Hkprim as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (e0 & Hden).
      assert (Hnd : no_dot posts) by exact Hdots.
      exact (chain_head _ _ e0 Hden Hposts Hkposts Hnd).
    - (* record *)
      inversion Hkprim as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (e0 & Hden).
      assert (Hnd : no_dot posts) by exact Hdots.
      exact (chain_head _ _ e0 Hden Hposts Hkposts Hnd).
    - (* name: a dot call may follow *)
      inversion Hkprim as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (e0 & Hden).
      assert (Hhead : head_ok posts) by exact Hdots.
      inversion Hden; subst.
      destruct (posts_den_var (var_of x) posts Hposts Hkposts Hhead) as (e & Hposts').
      exists e. apply DC_head with (e0 := e_fvar_f (var_of x)); assumption.
    - (* parenthesised expression *)
      inversion Hkprim as [| ? ? _ Hrest]; subst.
      inversion Hrest as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (e0 & Hden).
      assert (Hnd : no_dot posts) by exact Hdots.
      destruct (posts_den posts Hposts Hkposts Hnd e0) as (e & Hchain).
      exists e. apply DC_paren with (e0 := e0); assumption.
  Qed.

  Lemma no_dot_app : forall a b, no_dot (a ++ b) -> no_dot a /\ no_dot b.
  Proof.
    induction a as [| t a IH]; intros b H; [ split; [ exact I | exact H ] | ].
    destruct t as [k | r c].
    - simpl in H |- *. exact (IH b H).
    - destruct r; simpl in H |- *; try exact (IH b H).
      destruct H as [Hnc Hrest]. destruct (IH b Hrest) as [Ha Hb].
      split; [ split | exact Hb ].
      + destruct a as [| x a']; [ intros [] | exact Hnc ].
      + exact Ha.
  Qed.

  Lemma no_dot_head_ok : forall ps, no_dot ps -> head_ok ps.
  Proof.
    intros ps H. unfold head_ok.
    destruct ps as [| t1 ps1]; [ exact H | ].
    destruct t1 as [k | r1 c1]; [ exact H | ].
    destruct r1; try exact H.
    destruct ps1 as [| t2 ps2]; [ exact H | ].
    destruct t2 as [k2 | r2 c2]; [ exact H | ].
    destruct r2; try exact H.
    exfalso. simpl in H. destruct H as [H _]. apply H. simpl. exact I.
  Qed.

  Lemma no_dot_dots_ok : forall cs, no_dot cs -> dots_ok cs.
  Proof.
    induction cs as [| t cs IH]; intros H; [ exact I | ].
    destruct t as [k | r c]; [ exact H | ].
    destruct r; try exact H;
      first [ exact (IH H) | exact (no_dot_head_ok cs H) ].
  Qed.

  Lemma no_dot_op : forall o c2, no_dot (op_tree o :: c2) -> no_dot c2.
  Proof. intros o c2 H. destruct o; exact H. Qed.

  Lemma math_den : forall cs,
    gen (E_seq (E_rule R__operand) (E_star (E_rule R__more_math))) cs ->
    Forall TotKind cs -> dots_ok cs -> ops_ok cs ->
    exists e, Den_math var_of tbl cs e.
  Proof.
    intros cs H Hkids Hdots Hops.
    split_seq H as (tso & tsm & -> & Hop & Hmore).
    pose proof (operand_term _ Hop) as Hterm.
    destruct (gen_star_inv Hmore) as [-> | (m1 & m2 & -> & Hm1 & Hm2)].
    - rewrite app_nil_r in *.
      destruct (chain_den tso Hterm Hkids Hdots) as (e & Hchain).
      exists e. apply DM_chain. exact Hchain.
    - destruct (more_math_shape _ Hm1) as (o & c2 & -> & Hc2).
      pose proof (operand_term _ Hc2) as Hterm2.
      assert (Hcount : count_ops (tso ++ (op_tree o :: c2) ++ m2) = 1 + count_ops m2).
      { rewrite !count_ops_app.
        change (op_tree o :: c2) with ([op_tree o] ++ c2).
        rewrite count_ops_app, count_ops_op, (term_ops _ Hterm), (term_ops _ Hterm2).
        lia. }
      assert (Hm2nil : m2 = []).
      { apply (star_more_math_zero _ Hm2).
        destruct Hops as [Hz | [Hone _]]; lia. }
      subst m2. rewrite app_nil_r in *.
      assert (Hnd : no_dot (tso ++ op_tree o :: c2)).
      { destruct Hops as [Hz | [_ Hnd]]; [ rewrite Hz in Hcount; simpl in Hcount; lia | exact Hnd ]. }
      destruct (no_dot_app _ _ Hnd) as [Hnd1 Hnd2].
      apply Forall_app in Hkids as [Hk1 Hk2].
      inversion Hk2 as [| ? ? _ Hk3]; subst.
      destruct (chain_den tso Hterm Hk1 (no_dot_dots_ok _ Hnd1)) as (e1 & Hc1).
      destruct (chain_den c2 Hterm2 Hk3 (no_dot_dots_ok _ (no_dot_op _ _ Hnd2))) as (e2 & Hc2').
      exists (e_bin e1 o e2). apply DM_bin; assumption.
  Qed.

  Lemma ops_ok_decls : forall ds ss,
    Forall (fun t => exists c, t = Node R_declaration c) ds ->
    ops_ok (ds ++ ss) -> ops_ok ss.
  Proof.
    intros ds ss Hds. induction Hds as [| d ds [c ->] _ IH]; intros Hops.
    - exact Hops.
    - apply IH. destruct Hops as [Hz | [Hone Hnd]].
      + left. exact Hz.
      + right. split; [ exact Hone | exact Hnd ].
  Qed.

  Lemma decls_block : forall ds,
    gen (E_star (E_rule R_declaration)) ds -> Forall TotKind ds ->
    forall ss e, Den_block var_of tbl ss e ->
    exists e', Den_block var_of tbl (ds ++ ss) e'.
  Proof.
    intros ds H.
    apply (gen_star_ind (E_rule R_declaration)
             (fun ds => Forall TotKind ds ->
                        forall ss e, Den_block var_of tbl ss e ->
                        exists e', Den_block var_of tbl (ds ++ ss) e'));
      [ | | exact H ].
    - (* no declaration *)
      intros _ ss e Hss. exists e. exact Hss.
    - intros ts1 ts2 Hdecl IH Hkids ss e Hss.
      apply Forall_app in Hkids as [Hkids1 Hkids2].
      destruct (gen_node_of Hdecl eq_refl) as (c & -> & _).
      inversion Hkids1 as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (x & v & Hd).
      destruct (IH Hkids2 ss e Hss) as (body & Hbody).
      exists (e_let v (close_exp (var_of x) body)).
      apply DB_decl with (x := x) (v := v); assumption.
  Qed.

  Lemma last_member : forall (l : list tree) a d,
    In (List.last (a :: l) d) (a :: l).
  Proof.
    intros l. induction l as [| b l IH]; intros a d.
    - left. reflexivity.
    - right. apply IH.
  Qed.

  Lemma plus_decls_last : forall ds,
    gen (E_plus (E_rule R_declaration)) ds -> last_is_decl ds.
  Proof.
    intros ds H.
    destruct (gen_seq_inv (gen_plus_inv H)) as (d1 & drest & -> & Hd1 & Hrest).
    destruct (gen_node_of Hd1 eq_refl) as (c & -> & _).
    assert (Hall : Forall (fun t => exists c, t = Node R_declaration c)
                          (Node R_declaration c :: drest)).
    { apply Forall_cons; [ eauto | exact (declaration_nodes drest Hrest) ]. }
    assert (Hin : In (List.last (Node R_declaration c :: drest) (Leaf TStr))
                     (Node R_declaration c :: drest))
      by apply last_member.
    rewrite Forall_forall in Hall.
    exact (Hall _ Hin).
  Qed.

  Lemma dots_ok_decls : forall ds ss,
    Forall (fun t => exists c, t = Node R_declaration c) ds ->
    dots_ok (ds ++ ss) -> dots_ok ss.
  Proof.
    intros ds ss Hds. induction Hds as [| d ds [c ->] _ IH]; intros Hdots.
    - exact Hdots.
    - exact (IH Hdots).
  Qed.

  Lemma block_den : forall cs,
    gen (E_rule R__part) cs -> Forall TotKind cs -> ~ last_is_decl cs ->
    dots_ok cs -> ops_ok cs -> exists e, Den_block var_of tbl cs e.
  Proof.
    intros cs H Hkids Hlast Hdots Hops.
    destruct (part_shape cs H) as [(ds & ss & -> & Hds & Hss) | Hstatement].
    - (* declarations, then perhaps a chain *)
      destruct Hss as [Hstatement | ->].
      + apply Forall_app in Hkids as [Hkds Hkss].
        destruct (gen_seq_inv (gen_plus_inv Hds)) as (d1 & drest & Hsplit & Hd1 & Hrest).
        assert (Hstar : gen (E_star (E_rule R_declaration)) ds).
        { rewrite Hsplit. apply G_star_cons; assumption. }
        assert (Hdots_ss : dots_ok ss).
        { apply (dots_ok_decls ds ss); [ | exact Hdots ].
          apply declaration_nodes. exact Hstar. }
        assert (Hops_ss : ops_ok ss).
        { apply (ops_ok_decls ds ss); [ | exact Hops ].
          apply declaration_nodes. exact Hstar. }
        destruct (math_den ss (statement_math _ Hstatement) Hkss Hdots_ss Hops_ss)
          as (e & Hmath).
        assert (Hss : Den_block var_of tbl ss e) by (apply DB_chain; exact Hmath).
        exact (decls_block ds Hstar Hkds ss e Hss).
      + exfalso. apply Hlast. rewrite app_nil_r. exact (plus_decls_last ds Hds).
    - (* a chain alone *)
      destruct (math_den cs (statement_math _ Hstatement) Hkids Hdots Hops)
        as (e & Hmath).
      exists e. apply DB_chain. exact Hmath.
  Qed.

  Lemma args_den : forall fin tail,
    (fin = [] \/ fin = [sym ","]) ->
    gen (E_star (E_seq (E_term (T_text ",")) (E_rule R_expr))) tail ->
    Forall TotKind tail ->
    forall t e, Den var_of tbl t e ->
    exists es, Den_args var_of tbl (t :: tail ++ fin) es.
  Proof.
    intros fin tail Hfin H.
    apply (gen_star_ind (E_seq (E_term (T_text ",")) (E_rule R_expr))
             (fun tail => Forall TotKind tail ->
                          forall t e, Den var_of tbl t e ->
                          exists es, Den_args var_of tbl (t :: tail ++ fin) es));
      [ | | exact H ].
    - (* last argument *)
      intros _ t e Hden. simpl.
      destruct Hfin as [-> | ->].
      + exists [e]. apply DA_last. exact Hden.
      + exists [e]. apply DA_trailing. exact Hden.
    - intros ts1 ts2 Hstep IH Hkids t e Hden.
      apply Forall_app in Hkids as [Hkids1 Hkids2].
      split_seq Hstep as (tscomma & tsarg & -> & Hcomma & Harg).
      apply gen_text_inv in Hcomma. subst.
      destruct (gen_node_of Harg eq_refl) as (c & -> & _).
      inversion Hkids1 as [| ? ? _ Hrest]; subst.
      inversion Hrest as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (e2 & Hden2).
      destruct (IH Hkids2 (Node R_expr c) e2 Hden2) as (es & Hargs).
      exists (e :: es). simpl. apply DA_more; assumption.
  Qed.

  Lemma arguments_den : forall cs,
    gen (body R_arguments) cs -> Forall TotKind cs ->
    exists es, Den_args var_of tbl cs es.
  Proof.
    intros cs H Hkids.
    destruct (shape_arguments cs H) as (c & tail & fin & -> & Htail & Hfin).
    inversion Hkids as [| ? ? Hk Hktail]; subst. simpl in Hk.
    destruct Hk as (e & Hden).
    apply Forall_app in Hktail as [Hktail _].
    exact (args_den fin tail Hfin Htail Hktail _ _ Hden).
  Qed.

  Lemma params_den : forall tail,
    gen (E_star (E_seq (E_term (T_text ",")) (E_rule R__param))) tail ->
    forall x, exists xs, Den_params var_of tbl (ident x :: tail) (x :: xs).
  Proof.
    intros tail H.
    apply (gen_star_ind (E_seq (E_term (T_text ",")) (E_rule R__param))
             (fun tail => forall x,
                exists xs, Den_params var_of tbl (ident x :: tail) (x :: xs)));
      [ | | exact H ].
    - intros x. exists []. apply DPa_one.
    - intros ts1 ts2 Hstep IH x.
      split_seq Hstep as (tscomma & tsparam & -> & Hcomma & Hparam).
      apply gen_text_inv in Hcomma. subst.
      destruct (shape_param _ Hparam) as (y & ->).
      destruct (IH y) as (ys & Hys).
      exists (y :: ys). simpl. apply DPa_more. exact Hys.
  Qed.

  Lemma sep_den : forall fin tail,
    (fin = [] \/ fin = [sym ","]) ->
    gen (E_star (E_seq (E_term (T_text ",")) (E_rule R__record_item))) tail ->
    Forall TotKind tail ->
    exists fs, Den_sep var_of tbl (tail ++ fin ++ [sym "}"]) fs.
  Proof.
    intros fin tail Hfin H.
    apply (gen_star_ind (E_seq (E_term (T_text ",")) (E_rule R__record_item))
             (fun tail => Forall TotKind tail ->
                exists fs, Den_sep var_of tbl (tail ++ fin ++ [sym "}"]) fs));
      [ | | exact H ].
    - (* the closing brace *)
      intros _. simpl.
      destruct Hfin as [-> | ->].
      + exists fs_nil. apply DS_end.
      + exists fs_nil. apply DS_more. apply DI_end.
    - intros ts1 ts2 Hstep IH Hkids.
      apply Forall_app in Hkids as [Hkids1 Hkids2].
      split_seq Hstep as (tscomma & tsitem & -> & Hcomma & Hitem).
      apply gen_text_inv in Hcomma. subst.
      destruct (shape_record_item _ Hitem) as (c & ->).
      inversion Hkids1 as [| ? ? _ Hrest]; subst.
      inversion Hrest as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (l & e & Hfield).
      destruct (IH Hkids2) as (fs & Hsep).
      exists (fs_cons (lab tbl l) e fs). simpl.
      apply DS_more. apply DI_field with (l := l) (e := e); assumption.
  Qed.

End Totality.

Section TreeInduction.

  Variable P : tree -> Prop.
  Hypothesis Hleaf : forall k, P (Leaf k).
  Hypothesis Hnode : forall r cs, Forall P cs -> P (Node r cs).

  Fixpoint tree_ind' (t : tree) : P t :=
    match t with
    | Leaf k => Hleaf k
    | Node r cs =>
        Hnode r cs
          ((fix go (l : list tree) : Forall P l :=
              match l with
              | [] => Forall_nil P
              | c :: l' => Forall_cons c (tree_ind' c) (go l')
              end) cs)
    end.

End TreeInduction.

Ltac in_list := simpl; repeat first [ left; reflexivity | right ].

Section Steps.

  Variable var_of : string -> termvar.
  Variable tbl : list string.

  Definition Step (r : rule) : Prop :=
    forall cs,
      gen (body r) cs -> complete_node r cs ->
      Forall (TotKind var_of tbl) cs -> TotKind var_of tbl (Node r cs).

  Lemma step_number : Step R_number.
  Proof.
    intros cs H _ _. destruct (shape_number cs H) as (n & ->).
    simpl. exists (e_num n). apply D_num.
  Qed.

  Lemma step_name : Step R_name.
  Proof.
    intros cs H _ _. destruct (shape_name cs H) as (x & ->).
    simpl. exists (e_fvar_f (var_of x)). apply D_name.
  Qed.

  Lemma step_boolean : Step R_boolean.
  Proof.
    intros cs H _ _. destruct (shape_boolean cs H) as [-> | ->]; simpl.
    - exists e_true. apply D_true.
    - exists e_false. apply D_false.
  Qed.

  Lemma step_expr : Step R_expr.
  Proof.
    intros cs H Hcomplete Hkids. simpl in Hcomplete.
    destruct Hcomplete as [Hlast [Hdots Hops]].
    destruct (block_den var_of tbl cs (expr_part cs H) Hkids Hlast Hdots Hops)
      as (e & Hblock).
    simpl. exists e. apply D_expr. exact Hblock.
  Qed.

  Lemma step_value : Step R_value.
  Proof.
    intros cs H Hcomplete Hkids. simpl in Hcomplete.
    destruct Hcomplete as [Hdots Hops].
    destruct (math_den var_of tbl cs (statement_math_value cs H) Hkids Hdots Hops)
      as (e & Hmath).
    simpl. exists e. apply D_value. exact Hmath.
  Qed.

  Lemma step_string : Step R_string.
  Proof.
    intros cs H _ _. pose proof (shape_string cs H) as ->.
    simpl. exists (e_str []). apply D_str.
  Qed.

  Lemma step_conditional : Step R_conditional.
  Proof.
    intros cs H Hcomplete Hkids. simpl in Hcomplete.
    destruct (shape_conditional cs H Hcomplete) as (a & b & c & ->).
    rewrite Forall_forall in Hkids.
    assert (Ha : TotKind var_of tbl (Node R_expr a)) by (apply Hkids; in_list).
    assert (Hb : TotKind var_of tbl (Node R_expr b)) by (apply Hkids; in_list).
    assert (Hc : TotKind var_of tbl (Node R_expr c)) by (apply Hkids; in_list).
    simpl in Ha, Hb, Hc.
    destruct Ha as (ea & Hda). destruct Hb as (eb & Hdb). destruct Hc as (ec & Hdc).
    simpl. exists (e_ite ea eb ec). apply D_cond; assumption.
  Qed.

  Lemma step_function : Step R_function.
  Proof.
    intros cs H Hcomplete Hkids. simpl in Hcomplete.
    destruct Hcomplete as [Hparams Hbody].
    destruct (shape_function cs H Hparams Hbody) as (kw & ps & b & ->).
    rewrite Forall_forall in Hkids.
    assert (Hps : TotKind var_of tbl (Node R_params ps)) by (apply Hkids; in_list).
    assert (Hb : TotKind var_of tbl (Node R_expr b)) by (apply Hkids; in_list).
    simpl in Hps, Hb. destruct Hps as (xs & Hxs). destruct Hb as (body & Hbody').
    simpl. exists (curry (List.map var_of xs) body).
    apply D_function; assumption.
  Qed.

  Lemma step_record : Step R_record.
  Proof.
    intros cs H _ Hkids.
    destruct (shape_record cs H) as (rest & -> & [-> | (c & tail & fin & -> & Htail & Hfin)]).
    - (* no fields *)
      simpl. exists (e_rec fs_nil). apply D_record. apply DI_end.
    - (* a first field and the rest *)
      inversion Hkids as [| ? ? _ Hrest]; subst.
      inversion Hrest as [| ? ? Hfield Hmore]; subst. simpl in Hfield.
      destruct Hfield as (l & e & Hf).
      apply Forall_app in Hmore as [Hktail Hkfin].
      destruct (sep_den var_of tbl fin tail Hfin Htail Hktail) as (fs & Hsep).
      simpl. exists (e_rec (fs_cons (lab tbl l) e fs)).
      apply D_record. apply DI_field with (l := l) (e := e); assumption.
  Qed.

  Lemma step_local : Step R_local.
  Proof.
    intros cs H Hcomplete Hkids. simpl in Hcomplete.
    destruct (shape_local cs H Hcomplete) as (d & b & ->).
    rewrite Forall_forall in Hkids.
    assert (Hd : TotKind var_of tbl (Node R_declaration d)) by (apply Hkids; in_list).
    assert (Hb : TotKind var_of tbl (Node R_expr b)) by (apply Hkids; in_list).
    simpl in Hd, Hb. destruct Hd as (x & v & Hdecl). destruct Hb as (body & Hbody).
    simpl. exists (e_let v (close_exp (var_of x) body)).
    apply D_local with (x := x); assumption.
  Qed.

  Lemma step_declaration : Step R_declaration.
  Proof.
    intros cs H _ Hkids.
    destruct (shape_declaration cs H) as (x & c & [-> | ->]);
      rewrite Forall_forall in Hkids;
      assert (Hv : TotKind var_of tbl (Node R_value c)) by (apply Hkids; in_list);
      simpl in Hv; destruct Hv as (v & Hden); simpl; exists x, v.
    - apply DD_plain. exact Hden.
    - apply DD_semi. exact Hden.
  Qed.

  Lemma step_field : Step R_field.
  Proof.
    intros cs H _ Hkids.
    destruct (shape_field cs H) as (l & c & ->).
    rewrite Forall_forall in Hkids.
    assert (Hv : TotKind var_of tbl (Node R_expr c)) by (apply Hkids; in_list).
    simpl in Hv. destruct Hv as (e & Hden).
    simpl. exists l, e. apply DF. exact Hden.
  Qed.

  Lemma step_access : Step R_access.
  Proof.
    intros cs H _ _. destruct (shape_access cs H) as (l & ->).
    simpl. exists l. reflexivity.
  Qed.

  Lemma step_take : Step R_take.
  Proof.
    intros cs H _ _. destruct (shape_take cs H) as (l & ->).
    simpl. exists l. reflexivity.
  Qed.

  Lemma step_call : Step R_call.
  Proof.
    intros cs H Hcomplete Hkids. simpl in Hcomplete.
    destruct (shape_call cs H Hcomplete) as (args & ->).
    rewrite Forall_forall in Hkids.
    assert (Ha : TotKind var_of tbl (Node R_arguments args)) by (apply Hkids; in_list).
    simpl in Ha. destruct Ha as (es & Hargs).
    simpl. exists args, es. split; [ reflexivity | exact Hargs ].
  Qed.

  Lemma step_arguments : Step R_arguments.
  Proof.
    intros cs H _ Hkids. simpl.
    exact (arguments_den var_of tbl cs H Hkids).
  Qed.

  Lemma step_params : Step R_params.
  Proof.
    intros cs H _ _.
    destruct (shape_params cs H) as (x & tail & -> & Htail).
    destruct (params_den var_of tbl tail Htail x) as (xs & Hxs).
    simpl. exists (x :: xs). exact Hxs.
  Qed.

  Lemma step_all : forall r, Step r.
  Proof.
    intros r. destruct r;
      first
        [ exact step_number | exact step_name | exact step_boolean
        | exact step_expr | exact step_value | exact step_function
        | exact step_string | exact step_conditional
        | exact step_record | exact step_local | exact step_declaration
        | exact step_field | exact step_access | exact step_take | exact step_call
        | exact step_arguments | exact step_params
        | (intros cs _ _ _; exact I) ].
  Qed.

  Theorem tot : forall t,
    valid t -> Complete t -> TotKind var_of tbl t.
  Proof.
    apply (tree_ind' (fun t => valid t -> Complete t -> TotKind var_of tbl t)).
    - intros k _ _. exact I.
    - intros r cs IH Hvalid Hcomplete.
      destruct (silent r) eqn:Hsilent.
      + (* a silent rule never labels a node *)
        destruct r; first [ exact I | discriminate Hsilent ].
      + destruct (gen_node_inv Hvalid Hsilent) as (cs' & Hcs & _ & Hbody).
        injection Hcs as <-.
        inversion Hcomplete as [| ? ? Hnode Hcomplete_kids]; subst.
        assert (Hvalid_kids : Forall valid cs) by exact (gen_valid _ _ Hbody).
        assert (Hkids : Forall (TotKind var_of tbl) cs).
        { rewrite Forall_forall in *. intros c Hc.
          exact (IH c Hc (Hvalid_kids c Hc) (Hcomplete_kids c Hc)). }
        exact (step_all r cs Hbody Hnode Hkids).
  Qed.

End Steps.
