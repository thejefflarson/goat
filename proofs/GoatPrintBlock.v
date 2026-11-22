(* Records, bindings and blocks: the parts of a printed expression that nest.
   A block is the run of bindings and the final statement an expression node
   holds. *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatPegTac.
Require Import Goat.GoatDen.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintChain.
Require Import Goat.GoatPrintPrim.
Open Scope string_scope.
Open Scope list_scope.

(* ---- records ---- *)

(* Every field value of the record parses as an expression. *)
Fixpoint AllExpr (P : nat) (fs : Goat_ott.fields) : Prop :=
  match fs with
  | fs_nil => True
  | fs_cons _ e rest => ExprParses (block P e) /\ AllExpr P rest
  end.

Lemma stopE_more_fields : forall P fs r,
  StopE (flats (more_field_trees P fs) ++ TSym "}" :: r).
Proof. intros P fs r. destruct fs; flat_simp; constructor. Qed.

Lemma more_fields_parse : forall fs P r,
  AllExpr P fs ->
  peg (E_star (E_seq (E_term (T_text ",")) (E_rule R__record_item)))
      (flats (more_field_trees P fs) ++ TSym "}" :: r)
      (Ok (more_field_trees P fs) (TSym "}" :: r)).
Proof.
  induction fs as [| l e rest IH]; intros P r Hall.
  - pok nope.
  - destruct Hall as [He Hrest].
    cbn [more_field_trees]. unfold field_tree. flat_simp. rewrite <- ?app_assoc.
    pok ltac:(first
      [ exact (IH _ _ Hrest)
      | (eapply He; apply stopE_more_fields) ]).
Qed.

Lemma expr_of_prim : forall H, PrimOK H -> ExprParses H.
Proof.
  intros H Hprim r Hr.
  assert (Hc : Chain H) by (exists H, []; split; [ symmetry; apply app_nil_r | split; [ exact Hprim | constructor ] ]).
  assert (Hfin : Fin H) by (left; exact Hc).
  assert (Hstop : Stop r) by (apply stop_of_stopE; exact Hr).
  inversion Hr; subst.
  all: eapply peg_node; [ reflexivity | cbn [body] | pcat ].
  all: eapply peg_seq_ok; [ | | pcat ].
  all: first [ shelve | idtac ].
  Unshelve.
  all: try (eapply peg_splice; [ reflexivity | cbn [body] ]).
  all: try (eapply P_alt_right).
  all: try (pfail ltac:(first
         [ exact (fin_statement _ _ Hfin Hstop)
         | (eapply notdecl_fail; exact (fin_notdecl _ _ Hfin Hstop)) ])).
  all: try (pok ltac:(first
         [ exact (fin_statement _ _ Hfin Hstop)
         | (eapply notdecl_fail; exact (fin_notdecl _ _ Hfin Hstop)) ])).
Qed.

Lemma flats_paren : forall b, flats (paren_kids b) = TSym "(" :: flats b ++ [TSym ")"].
Proof. intros b. unfold paren_kids. flat_simp. reflexivity. Qed.

(* A record pattern reads [{...] and then needs a name; the printed base
   starts with a parenthesis. *)
Lemma destructure_fails_on_spread : forall b rest,
  peg (E_rule R_destructure) (TSym "{" :: TSym "..." :: flats (paren_kids b) ++ rest) Fail.
Proof. intros b rest. rewrite flats_paren. cbn [app]. pfail nope. Qed.

Lemma spread_item : forall b rest, ExprParses b ->
  peg (E_rule R__record_item) (TSym "..." :: flats (paren_kids b) ++ TSym "," :: rest)
      (Ok [spread_tree b] (TSym "," :: rest)).
Proof.
  intros b rest Hb.
  assert (Hbp : ExprParses (paren_kids b)) by exact (expr_of_prim _ (prim_paren _ Hb)).
  unfold spread_tree.
  pok ltac:(first [ (eapply Hbp; constructor) ]).
Qed.

Lemma field_item : forall l f rest, ExprParses f -> StopE rest ->
  peg (E_rule R__record_item) (TName (lname l) :: TSym ":" :: flats f ++ rest)
      (Ok [field_tree l f] rest).
Proof.
  intros l f rest Hf Hs.
  unfold field_tree.
  pok ltac:(first [ (eapply Hf; exact Hs) ]).
Qed.

Lemma prim_spread : forall b f l,
  ExprParses b -> ExprParses f ->
  PrimOK [Node R_record [sym "{"; spread_tree b; sym ","; field_tree l f; sym "}"]].
Proof.
  intros b f l Hb Hf r Hne.
  refine (conj _ (conj _ _)).
  - flat_simp. plain_head.
  - exact I.
  - unfold spread_tree, field_tree. flat_simp. rewrite <- ?app_assoc. cbn [app].
    rewrite <- ?app_assoc. cbn [app].
    pok ltac:(first
      [ exact (destructure_fails_on_spread _ _)
      | exact (spread_item _ _ Hb)
      | exact (field_item _ _ _ Hf (StopE_rbrace _)) ]).
Qed.

Lemma prim_record : forall P fs,
  AllExpr P fs ->
  PrimOK [Node R_record ((sym "{" :: field_trees P fs) ++ [sym "}"])].
Proof.
  intros P fs Hall r Hne.
  refine (conj _ (conj _ _)).
  - flat_simp. plain_head.
  - exact I.
  - destruct fs as [| l e rest]; cbn [field_trees].
    + flat_simp. pok nope.
    + destruct Hall as [He Hrest].
      unfold field_tree. flat_simp. rewrite <- ?app_assoc.
      pok ltac:(first
        [ exact (more_fields_parse _ _ _ Hrest)
        | (eapply He; apply stopE_more_fields) ]).
Qed.
