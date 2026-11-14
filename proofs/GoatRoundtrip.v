(* T3 (ADR 0030): the core parses back to itself.

   Scope: the core fragment, over a trusted token stream, printed in the curried
   style of checker/tests/core_roundtrip.rs. The hypotheses:
   - [scoped 0 e]: [e] is closed (no free variable, every bound index has a
     binder);
   - [Interned e]: its labels are numbered as parsing numbers them, by first
     occurrence in the printed text;
   - [names_distinct var_of]: the names the printer gives binders stand for
     distinct variables.
   The side conditions of ADR 0030 (recursive function bindings, groups of
   functions, duplicate labels, repeated parameters) are conditions on how the
   Rust front end reads the text. They are not needed here: the printer names
   each binder by its depth, so no name repeats, and the model reads a binding
   as the non-recursive [let] of the Ott source. *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatParse.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintLabels.
Require Import Goat.GoatPrintParse.
Require Import Goat.GoatPrintDen.
Require Import Goat.GoatPrintTop.
Open Scope string_scope.
Open Scope list_scope.

(* T3 *)
Theorem print_parse_roundtrip : forall var_of e,
  names_distinct var_of ->
  scoped 0 e ->
  Interned e ->
  exists t,
    peg (E_rule R_goat) (print e) (Ok [t] []) /\
    Den_goat var_of t e.
Proof.
  intros var_of e Hdistinct Hscoped Hinterned.
  set (t := print_tree e).
  assert (Hparse : peg (E_rule R_goat) (print e) (Ok [t] []))
    by exact (goat_parses e Hscoped).
  assert (Htable : labels t = nub_from [] (List.map lname (lbls e)))
    by exact (labels_print e).
  assert (Hlabels : LabelsOK (labels t) (lbls e))
    by (rewrite Htable; exact Hinterned).
  assert (Hblock : Den_block var_of (labels t) (block 0 e) (inst var_of 0 e))
    by exact (proj1 (proj1 (print_den var_of (labels t) Hdistinct) e 0 Hscoped Hlabels)).
  assert (Hinst : inst var_of 0 e = e)
    by exact (proj1 (inst_closed var_of) e 0 Hscoped).
  assert (Hexpr : Den var_of (labels t) (Node R_expr (block 0 e)) e)
    by (rewrite <- Hinst at 2; apply D_expr; exact Hblock).
  assert (Hden : Den_goat var_of t e)
    by (exists (block 0 e); split; [ reflexivity | exact Hexpr ]).
  exists t. split; [ exact Hparse | exact Hden ].
Qed.
