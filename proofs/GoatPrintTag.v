(* Tags in a printed term: a tag built from its payload is a name applied to the
   payload's slots as arguments, and a match is the scrutinee and its arms, each
   arm a pattern naming the slots and a body. Each parses by the rule that should
   take it. *)

From Stdlib Require Import String List Arith Lia.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatPegTac.
Require Import Goat.GoatDen.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintChain.
Require Import Goat.GoatPrintPrim.
Require Import Goat.GoatPrintBlock.
Require Import Goat.GoatPrintArm.
Open Scope string_scope.
Open Scope list_scope.

(* ---- a tag's payload: the arguments of a call ---- *)

Lemma stopE_slot_args : forall G P fs r,
  StopE (flats (slot_args G P fs) ++ TSym ")" :: r).
Proof. intros G P fs r. destruct fs; flat_simp; constructor. Qed.

Lemma slot_args_parse : forall fs G P r,
  AllExpr G P fs ->
  peg (E_star (E_seq (E_term (T_text ",")) (E_rule R_expr)))
      (flats (slot_args G P fs) ++ TSym ")" :: r)
      (Ok (slot_args G P fs) (TSym ")" :: r)).
Proof.
  induction fs as [| l e rest IH | l e rest IH]; intros G P r Hall.
  - pok nope.
  - destruct Hall as [He Hrest].
    cbn [slot_args]. flat_simp. rewrite <- ?app_assoc.
    pok ltac:(first
      [ exact (IH _ _ _ Hrest)
      | (eapply He; apply stopE_slot_args) ]).
  - destruct Hall as [He Hrest].
    cbn [slot_args]. flat_simp. rewrite <- ?app_assoc.
    pok ltac:(first
      [ exact (IH _ _ _ Hrest)
      | (eapply He; apply stopE_slot_args) ]).
Qed.

Definition con_call (G : Grp) (P : nat) (x : exp) (rest : Goat_ott.fields) : tree :=
  Node R_call [sym "("; Node R_arguments (Node R_expr (block G P x) :: slot_args G P rest);
               sym ")"].

Lemma post_con_call : forall G P x rest,
  ExprParses (block G P x) -> AllExpr G P rest -> PostOK (con_call G P x rest).
Proof.
  intros G P x rest Hx Hrest. unfold con_call. split.
  - intros r. flat_simp. simpl. discriminate.
  - intros r. flat_simp. rewrite <- ?app_assoc.
    pok ltac:(first
      [ exact (slot_args_parse _ _ _ _ Hrest)
      | (eapply Hx; apply stopE_slot_args) ]).
Qed.

(* ---- a match ---- *)

(* The body of an arm, printed after the arm's slots are named. *)
Definition arm_block (G : Grp) (P : nat) (w : gdecl) (tg : nat) (b : exp) : list tree :=
  match arm_arity w tg with
  | 0 => block G (S P) b
  | m => arm_body G (S P) m b
  end.

Lemma arm_block_eq : forall G P w tg b,
  arm_chain (arm_arity w tg) 0 b ->
  arm_block G P w tg b = block G (S P + arm_arity w tg) (arm_inner (arm_arity w tg) b).
Proof.
  intros G P w tg b Hc. unfold arm_block. destruct (arm_arity w tg) as [| m] eqn:E.
  - cbn [arm_inner]. rewrite Nat.add_0_r. reflexivity.
  - rewrite (arm_body_block (S m) 0 b G (S P) (ltac:(lia)) Hc). reflexivity.
Qed.

Definition arm_node (G : Grp) (P : nat) (w : gdecl) (tg : nat) (b : exp) : tree :=
  Node R_arm [Node R_pattern (arm_pattern w tg P); sym "then";
              Node R_expr (arm_block G P w tg b)].

Fixpoint ArmsOK (G : Grp) (P : nat) (w : gdecl) (ars : arms) {struct ars} : Prop :=
  match ars with
  | arms_nil => True
  | arms_else e => ExprParses (block G P e)
  | arms_cons tg b rest => ExprParses (arm_block G P w tg b) /\ ArmsOK G P w rest
  end.

Fixpoint arm_list (G : Grp) (P : nat) (w : gdecl) (ars : arms) {struct ars} : list tree :=
  match ars with
  | arms_cons tg b rest => arm_node G P w tg b :: arm_list G P w rest
  | _ => []
  end.

Fixpoint else_list (G : Grp) (P : nat) (ars : arms) {struct ars} : list tree :=
  match ars with
  | arms_nil => []
  | arms_else e => [sym "else"; Node R_expr (block G P e)]
  | arms_cons _ _ rest => else_list G P rest
  end.

Lemma arm_trees_split : forall ars G P w,
  arm_trees G P w ars = arm_list G P w ars ++ else_list G P ars.
Proof.
  induction ars as [| e | tg b rest IH]; intros G P w; [ reflexivity | reflexivity | ].
  cbn [arm_trees arm_list else_list app]. rewrite (IH G P w). reflexivity.
Qed.

Lemma else_list_cases : forall ars G P,
  else_list G P ars = [] \/ exists e, else_list G P ars = [sym "else"; Node R_expr (block G P e)].
Proof.
  induction ars as [| e | tg b rest IH]; intros G P.
  - left. reflexivity.
  - right. exists e. reflexivity.
  - cbn [else_list]. apply IH.
Qed.

Lemma names_star : forall m q r,
  peg (E_star (E_seq (E_term (T_text ",")) (E_rule R_name)))
      (flats (sym "," :: arm_names q (S m)) ++ TSym ")" :: r)
      (Ok (sym "," :: arm_names q (S m)) (TSym ")" :: r)).
Proof.
  induction m as [| m IH]; intros q r.
  - cbn [arm_names]. flat_simp. pok nope.
  - cbn [arm_names]. flat_simp. rewrite <- ?app_assoc.
    pok ltac:(first [ exact (IH _ _) ]).
Qed.

Lemma labels_parse : forall m q r,
  peg (E_rule R_labels) (flats (arm_names q (S m)) ++ TSym ")" :: r)
      (Ok [Node R_labels (arm_names q (S m))] (TSym ")" :: r)).
Proof.
  intros m q r. destruct m as [| m].
  - cbn [arm_names]. flat_simp. pok nope.
  - cbn [arm_names]. flat_simp. rewrite <- ?app_assoc.
    pok ltac:(first [ exact (names_star _ _ _) ]).
Qed.

Lemma pattern_parse : forall w tg P rest,
  peg (E_alt (E_rule R_list_pattern) (E_alt (E_rule R_literal_pattern) (E_rule R_pattern)))
      (flats (arm_pattern w tg P) ++ TSym "then" :: rest)
      (Ok [Node R_pattern (arm_pattern w tg P)] (TSym "then" :: rest)).
Proof.
  intros w tg P rest. unfold arm_pattern.
  destruct (arm_arity w tg) as [| m].
  - flat_simp. pok nope.
  - flat_simp. rewrite <- ?app_assoc.
    pok ltac:(first [ exact (labels_parse _ _ _) ]).
Qed.

Definition ArmEnd (r : list tok) : Prop :=
  (exists r', r = TSym "else" :: r') \/ (exists r', r = TSym "done" :: r').

Lemma stopE_arms : forall G P w ars r,
  ArmEnd r -> StopE (flats (arm_list G P w ars) ++ r).
Proof.
  intros G P w ars r Hr. destruct ars as [| e | tg b rest].
  - destruct Hr as [[r' ->] | [r' ->]]; cbn [arm_list flats flat_map app]; constructor.
  - destruct Hr as [[r' ->] | [r' ->]]; cbn [arm_list flats flat_map app]; constructor.
  - cbn [arm_list]. unfold arm_node, arm_pattern. destruct (arm_arity w tg); flat_simp; constructor.
Qed.

Lemma arm_parses : forall G P w tg b r,
  ExprParses (arm_block G P w tg b) -> StopE r ->
  peg (E_rule R_arm) (flat (arm_node G P w tg b) ++ r) (Ok [arm_node G P w tg b] r).
Proof.
  intros G P w tg b r Hb Hr. unfold arm_node. flat_simp. rewrite <- ?app_assoc.
  pok ltac:(first
    [ exact (pattern_parse _ _ _ _)
    | (eapply Hb; exact Hr) ]).
Qed.

Lemma arm_list_parse : forall ars G P w r,
  ArmsOK G P w ars -> ArmEnd r ->
  peg (E_star (E_rule R_arm)) (flats (arm_list G P w ars) ++ r)
      (Ok (arm_list G P w ars) r).
Proof.
  induction ars as [| e | tg b rest IH]; intros G P w r Hok Hend.
  - cbn [arm_list flats flat_map app].
    destruct Hend as [[r' ->] | [r' ->]]; pok nope.
  - cbn [arm_list flats flat_map app].
    destruct Hend as [[r' ->] | [r' ->]]; pok nope.
  - destruct Hok as [Hb Hrest]. cbn [arm_list]. rewrite flats_cons, <- app_assoc.
    pok ltac:(first
      [ exact (IH _ _ _ _ Hrest Hend)
      | exact (arm_parses _ _ _ _ _ _ Hb (stopE_arms _ _ _ _ _ Hend)) ]).
Qed.

Lemma else_expr_parses : forall ars G P w e,
  ArmsOK G P w ars ->
  else_list G P ars = [sym "else"; Node R_expr (block G P e)] ->
  ExprParses (block G P e).
Proof.
  induction ars as [| e' | tg b rest IH]; intros G P w e Hok E.
  - discriminate E.
  - cbn [else_list] in E. cbn in Hok.
    assert (Hb : block G P e' = block G P e) by congruence.
    rewrite <- Hb. exact Hok.
  - cbn [else_list] in E. destruct Hok as [_ Hrest]. exact (IH _ _ _ _ Hrest E).
Qed.

Lemma arms_parse : forall ars G P w r,
  ArmsOK G P w ars ->
  peg (E_seq (E_star (E_rule R_arm))
             (E_seq (E_opt (E_rule R__else_branch)) (E_expect (E_term (T_text "done")))))
      (flats (arm_trees G P w ars) ++ TSym "done" :: r)
      (Ok (arm_trees G P w ars ++ [sym "done"]) r).
Proof.
  intros ars G P w r Hok. rewrite arm_trees_split, flats_app, <- app_assoc.
  destruct (else_list_cases ars G P) as [E | (e & E)].
  - rewrite E. cbn [flats flat_map app].
    eapply peg_seq_ok;
      [ exact (arm_list_parse _ _ _ _ _ Hok (or_intror (ex_intro _ r eq_refl))) | | ].
    + pok nope.
    + cbn [app]. rewrite ?app_nil_r. rewrite <- ?app_assoc. reflexivity.
  - rewrite E. flat_simp.
    eapply peg_seq_ok;
      [ exact (arm_list_parse _ _ _ _ _ Hok (or_introl (ex_intro _ _ eq_refl))) | | ].
    + pok ltac:(eapply (else_expr_parses _ _ _ _ _ Hok E); constructor).
    + cbn [app]. rewrite ?app_nil_r. rewrite <- ?app_assoc. reflexivity.
Qed.

Lemma prim_match : forall G P w a ars,
  ExprParses (block G P a) -> ArmsOK G P w ars ->
  PrimOK [Node R_match_expr ([sym "match"; Node R_expr (block G P a); sym "do"]
                             ++ arm_trees G P w ars ++ [sym "done"])].
Proof.
  intros G P w a ars Ha Hars r Hne.
  refine (conj _ (conj _ _)).
  - flat_simp. plain_head.
  - exact I.
  - flat_simp. rewrite <- ?app_assoc. cbn [app]. rewrite <- ?app_assoc.
    pok ltac:(first
      [ exact (arms_parse _ _ _ _ _ Hars)
      | (eapply Ha; constructor) ]).
Qed.

