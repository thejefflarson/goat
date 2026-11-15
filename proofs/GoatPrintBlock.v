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
