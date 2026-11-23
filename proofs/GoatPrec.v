(* Operator runs (ADR 0030, ADR 0013). A statement is a flat run of operands and
   operators; lowering folds it into a tree with a stack of pending operators
   (checker/src/lower.rs, [lower_expr_chain]). [resolve] is that fold over the
   denotations of the operands, and the connectives are derived forms of the
   calculus: [a and b] is [if a then b else false], [a or b] is
   [if a then true else b], [not a] is [if a then false else true]. The
   calculus has no node for them, so the parser fragment widens without
   touching the typing rules. *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatMeta.

Inductive lop : Type :=
  | L_or
  | L_and
  | L_not
  | L_bin (o : bop).

(* One step of a run, after each operand has been read: a value, a prefix
   [not], or an infix operator. *)
Inductive item : Type :=
  | I_val (e : exp)
  | I_not
  | I_op (o : lop).

(* Binding strength, loosest first. The generated GoatPrecTable.v checks this
   against the behaviour of lowering. *)
Definition prec (o : lop) : nat :=
  match o with
  | L_or => 1
  | L_and => 2
  | L_not => 3
  | L_bin bop_eq | L_bin bop_ne => 4
  | L_bin bop_lt | L_bin bop_lte | L_bin bop_gt | L_bin bop_gte => 5
  | L_bin bop_add | L_bin bop_sub => 6
  | L_bin bop_mul | L_bin bop_div | L_bin bop_fdiv | L_bin bop_rem => 7
  end.

(* The calculus term of an infix operator applied to two operands. *)
Definition bin (o : lop) (a b : exp) : exp :=
  match o with
  | L_or => e_ite a e_true b
  | L_and => e_ite a b e_false
  | L_bin o' => e_bin a o' b
  | L_not => e_unit
  end.

Definition negate (a : exp) : exp := e_ite a e_false e_true.

(* Fold the operator on top of the stack into the operands beside it. The
   operand stack has the most recent operand first. *)
Definition combine (o : lop) (xs : list exp) : option (list exp) :=
  match o, xs with
  | L_not, a :: xs' => Some (negate a :: xs')
  | L_not, _ => None
  | _, b :: a :: xs' => Some (bin o a b :: xs')
  | _, _ => None
  end.

(* Fold while the operator on top binds at least as tightly as [p]. *)
Fixpoint pop_ge (p : nat) (xs : list exp) (ops : list lop) {struct ops}
  : option (list exp * list lop) :=
  match ops with
  | [] => Some (xs, [])
  | top :: ops' =>
      if Nat.leb p (prec top)
      then match combine top xs with
           | Some xs' => pop_ge p xs' ops'
           | None => None
           end
      else Some (xs, ops)
  end.

Definition state : Type := (list exp * list lop)%type.

Definition step (st : state) (it : item) : option state :=
  match it with
  | I_val e => Some (e :: fst st, snd st)
  | I_not => Some (fst st, L_not :: snd st)
  | I_op o =>
      match pop_ge (prec o) (fst st) (snd st) with
      | Some (xs, ops) => Some (xs, o :: ops)
      | None => None
      end
  end.

Fixpoint run (st : state) (is : list item) {struct is} : option state :=
  match is with
  | [] => Some st
  | it :: is' =>
      match step st it with
      | Some st' => run st' is'
      | None => None
      end
  end.

Definition resolve (is : list item) : option exp :=
  match run ([], []) is with
  | Some (xs, ops) =>
      match pop_ge 0 xs ops with
      | Some ([e], []) => Some e
      | _ => None
      end
  | None => None
  end.

(* ---- the readings the checker expects ---- *)

Lemma combine_bin : forall o b a xs,
  o <> L_not -> combine o (b :: a :: xs) = Some (bin o a b :: xs).
Proof. intros o b a xs Ho. destruct o; [ reflexivity | reflexivity | congruence | reflexivity ]. Qed.

Lemma prec_leb : forall p q, p <= q -> Nat.leb p q = true.
Proof. intros p q H. apply Nat.leb_le. exact H. Qed.

Lemma prec_ltb : forall p q, q < p -> Nat.leb p q = false.
Proof. intros p q H. apply Nat.leb_gt. exact H. Qed.

Theorem resolve_one : forall o a b,
  o <> L_not -> resolve [I_val a; I_op o; I_val b] = Some (bin o a b).
Proof.
  intros o a b Ho. unfold resolve. simpl.
  rewrite (combine_bin o b a [] Ho). reflexivity.
Qed.

Theorem resolve_not : forall a, resolve [I_not; I_val a] = Some (negate a).
Proof. intros a. reflexivity. Qed.

(* Equal or tighter on the left: the left operator folds first, so a run is
   left-associative within a level. *)
Theorem resolve_left : forall o1 o2 a b c,
  o1 <> L_not -> o2 <> L_not -> prec o2 <= prec o1 ->
  resolve [I_val a; I_op o1; I_val b; I_op o2; I_val c]
  = Some (bin o2 (bin o1 a b) c).
Proof.
  intros o1 o2 a b c H1 H2 Hp. unfold resolve. simpl.
  rewrite (prec_leb _ _ Hp), (combine_bin o1 b a [] H1). simpl.
  rewrite (combine_bin o2 c (bin o1 a b) [] H2). reflexivity.
Qed.

(* Looser on the left: the tighter operator on the right nests inside. *)
Theorem resolve_right : forall o1 o2 a b c,
  o1 <> L_not -> o2 <> L_not -> prec o1 < prec o2 ->
  resolve [I_val a; I_op o1; I_val b; I_op o2; I_val c]
  = Some (bin o1 a (bin o2 b c)).
Proof.
  intros o1 o2 a b c H1 H2 Hp. unfold resolve. simpl.
  rewrite (prec_ltb _ _ Hp). simpl.
  rewrite (combine_bin o2 c b [a] H2). simpl.
  rewrite (combine_bin o1 (bin o2 b c) a [] H1). reflexivity.
Qed.

(* [not] takes the operand after it, and an operator binds to it only when the
   operator is no tighter than [not]. *)
Theorem resolve_not_loose : forall o a b,
  o <> L_not -> prec o <= prec L_not ->
  resolve [I_not; I_val a; I_op o; I_val b] = Some (bin o (negate a) b).
Proof.
  intros o a b Ho Hp. unfold resolve. simpl.
  assert (Hb : Nat.leb (prec o) 3 = true) by (apply Nat.leb_le; exact Hp).
  rewrite Hb. simpl.
  rewrite (combine_bin o b (negate a) [] Ho). reflexivity.
Qed.

Theorem resolve_not_tight : forall o a b,
  o <> L_not -> prec L_not < prec o ->
  resolve [I_not; I_val a; I_op o; I_val b] = Some (negate (bin o a b)).
Proof.
  intros o a b Ho Hp. unfold resolve. simpl.
  assert (Hb : Nat.leb (prec o) 3 = false) by (apply Nat.leb_gt; exact Hp).
  rewrite Hb. simpl.
  rewrite (combine_bin o b a [] Ho). simpl. reflexivity.
Qed.

(* ---- a well-formed run never underflows ---- *)

(* An operand is any number of prefix [not]s and then a value; a run is
   operands joined by infix operators. *)
Inductive Opd : list item -> Prop :=
  | Opd_val : forall e, Opd [I_val e]
  | Opd_not : forall is, Opd is -> Opd (I_not :: is).

Inductive Run : list item -> Prop :=
  | Run_one : forall is, Opd is -> Run is
  | Run_more : forall is1 o is2,
      Opd is1 -> o <> L_not -> Run is2 -> Run (is1 ++ I_op o :: is2).

(* The binary operators waiting on the stack. *)
Fixpoint pending (ops : list lop) : nat :=
  match ops with
  | [] => 0
  | L_not :: ops' => pending ops'
  | _ :: ops' => S (pending ops')
  end.

Lemma combine_ok : forall o ops xs,
  length xs = S (pending (o :: ops)) ->
  exists xs', combine o xs = Some xs' /\ length xs' = S (pending ops).
Proof.
  intros o ops xs Hlen.
  destruct o; simpl in Hlen;
    destruct xs as [| x [| y xs']]; simpl in Hlen; try lia;
    simpl; eexists; split; try reflexivity; simpl; lia.
Qed.

Lemma pop_ge_ok : forall ops p xs,
  length xs = S (pending ops) ->
  exists xs' ops', pop_ge p xs ops = Some (xs', ops') /\ length xs' = S (pending ops').
Proof.
  induction ops as [| top ops IH]; intros p xs Hlen.
  - exists xs, []. split; [ reflexivity | exact Hlen ].
  - simpl. destruct (Nat.leb p (prec top)).
    + destruct (combine_ok top ops xs Hlen) as (xs' & Hc & Hl).
      rewrite Hc. exact (IH p xs' Hl).
    + exists xs, (top :: ops). split; [ reflexivity | exact Hlen ].
Qed.

Lemma pop_ge_zero : forall ops xs xs' ops',
  pop_ge 0 xs ops = Some (xs', ops') -> ops' = [].
Proof.
  induction ops as [| top ops IH]; intros xs xs' ops' H; simpl in H.
  - inversion H. reflexivity.
  - destruct (combine top xs) as [xs1 |]; [ | discriminate ].
    exact (IH _ _ _ H).
Qed.

Lemma run_app : forall is1 is2 st,
  run st (is1 ++ is2)
  = match run st is1 with Some st' => run st' is2 | None => None end.
Proof.
  induction is1 as [| it is1 IH]; intros is2 st; simpl.
  - reflexivity.
  - destruct (step st it); [ apply IH | reflexivity ].
Qed.

Lemma opd_ok : forall is, Opd is ->
  forall xs ops, length xs = pending ops ->
  exists xs' ops', run (xs, ops) is = Some (xs', ops') /\ length xs' = S (pending ops').
Proof.
  intros is H. induction H as [e | is H IH]; intros xs ops Hlen.
  - exists (e :: xs), ops. split; [ reflexivity | simpl; lia ].
  - simpl. exact (IH xs (L_not :: ops) Hlen).
Qed.

Lemma run_ok : forall is, Run is ->
  forall xs ops, length xs = pending ops ->
  exists xs' ops', run (xs, ops) is = Some (xs', ops') /\ length xs' = S (pending ops').
Proof.
  intros is H. induction H as [is Hopd | is1 o is2 Hopd Ho Hrun IH]; intros xs ops Hlen.
  - exact (opd_ok is Hopd xs ops Hlen).
  - rewrite run_app.
    destruct (opd_ok is1 Hopd xs ops Hlen) as (xs1 & ops1 & Hr1 & Hl1).
    rewrite Hr1.
    destruct (pop_ge_ok ops1 (prec o) xs1 Hl1) as (xs2 & ops2 & Hp & Hl2).
    simpl. rewrite Hp.
    apply IH. destruct o; simpl; [ lia | lia | congruence | lia ].
Qed.

(* A run of operands joined by operators has a reading. *)
Theorem resolve_total : forall is, Run is -> exists e, resolve is = Some e.
Proof.
  intros is H. unfold resolve.
  destruct (run_ok is H [] [] eq_refl) as (xs & ops & Hr & Hl).
  rewrite Hr.
  destruct (pop_ge_ok ops 0 xs Hl) as (xs' & ops' & Hp & Hl').
  rewrite Hp.
  pose proof (pop_ge_zero ops xs xs' ops' Hp) as ->.
  destruct xs' as [| e [| e' xs'']]; simpl in Hl'; try lia.
  exists e. reflexivity.
Qed.

(* ---- local closure ---- *)

Definition item_lc (it : item) : Prop :=
  match it with I_val e => lc e | _ => True end.

Lemma combine_lc : forall o xs xs',
  Forall lc xs -> combine o xs = Some xs' -> Forall lc xs'.
Proof.
  intros o xs xs' Hxs Hc.
  destruct o, xs as [| x [| y xs0]]; simpl in Hc; try discriminate;
    inversion Hc; subst; clear Hc;
    inversion Hxs as [| ? ? Hx Hrest]; subst;
    try (inversion Hrest as [| ? ? Hy Hrest']; subst);
    constructor; try assumption;
    unfold bin, negate, lc; simpl;
    first [ exact (conj Hx (conj I I)) | exact (conj Hx (conj Hy I))
          | exact (conj Hy (conj I Hx)) | exact (conj Hy (conj Hx I))
          | exact (conj Hy (conj I Hx)) | exact (conj Hy Hx) | exact I ].
Qed.

Lemma pop_ge_lc : forall ops p xs xs' ops',
  Forall lc xs -> pop_ge p xs ops = Some (xs', ops') -> Forall lc xs'.
Proof.
  induction ops as [| top ops IH]; intros p xs xs' ops' Hxs H; simpl in H.
  - inversion H; subst. exact Hxs.
  - destruct (Nat.leb p (prec top)).
    + destruct (combine top xs) as [xs1 |] eqn:Hc; [ | discriminate ].
      exact (IH p xs1 xs' ops' (combine_lc _ _ _ Hxs Hc) H).
    + inversion H; subst. exact Hxs.
Qed.

Lemma run_lc : forall is xs ops xs' ops',
  Forall item_lc is -> Forall lc xs ->
  run (xs, ops) is = Some (xs', ops') -> Forall lc xs'.
Proof.
  induction is as [| it is IH]; intros xs ops xs' ops' His Hxs H; simpl in H.
  - inversion H; subst. exact Hxs.
  - inversion His as [| ? ? Hit His']; subst.
    destruct it as [e | | o]; simpl in H.
    + exact (IH _ _ _ _ His' (Forall_cons e Hit Hxs) H).
    + exact (IH _ _ _ _ His' Hxs H).
    + destruct (pop_ge (prec o) xs ops) as [[xs1 ops1] |] eqn:Hp; [ | discriminate ].
      exact (IH _ _ _ _ His' (pop_ge_lc _ _ _ _ _ Hxs Hp) H).
Qed.

Theorem resolve_lc : forall is e,
  Forall item_lc is -> resolve is = Some e -> lc e.
Proof.
  intros is e His H. unfold resolve in H.
  destruct (run ([], []) is) as [[xs ops] |] eqn:Hr; [ | discriminate ].
  pose proof (run_lc is [] [] xs ops His (Forall_nil _) Hr) as Hxs.
  destruct (pop_ge 0 xs ops) as [[xs' ops'] |] eqn:Hp; [ | discriminate ].
  pose proof (pop_ge_lc ops 0 xs xs' ops' Hxs Hp) as Hxs'.
  destruct xs' as [| x [| y xs'']]; try discriminate.
  destruct ops'; try discriminate.
  inversion H; subst. inversion Hxs'; subst. assumption.
Qed.
