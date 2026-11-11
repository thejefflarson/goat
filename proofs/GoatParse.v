(* T1 (ADR 0030): every parse of a core-fragment token stream denotes a locally
   closed term.

   Scope: the core fragment only, over a trusted token stream. The lexer, the
   rules outside the fragment (rule_map.rs lists them), and the Rust lowering
   are not covered. *)

From Coq Require Import String List.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatMeta.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatShape.
Open Scope string_scope.
Open Scope list_scope.

(* Field and access labels in source order, repeats included. *)
Fixpoint label_occurrences (t : tree) : list string :=
  match t with
  | Leaf _ => []
  | Node r cs =>
      match r, cs with
      | R_access, [_; Node _ [Leaf (TName l)]] => [l]
      | R_field, Node _ [Leaf (TName l)] :: _ => [l]
      | _, _ => []
      end
      ++ (fix go (l : list tree) : list string :=
            match l with
            | [] => []
            | c :: l' => label_occurrences c ++ go l'
            end) cs
  end.

Fixpoint nub_from (seen l : list string) : list string :=
  match l with
  | [] => []
  | x :: l' =>
      if existsb (String.eqb x) seen
      then nub_from seen l'
      else x :: nub_from (seen ++ [x]) l'
  end.

(* The label table: each distinct label once, in order of first occurrence, so
   a label's index is the number lowering gives it. *)
Definition labels (t : tree) : list string := nub_from [] (label_occurrences t).

(* The program is its single top-level expression. *)
Definition Den_goat (var_of : string -> termvar) (t : tree) (e : exp) : Prop :=
  exists b,
    t = Node R_goat [Node R_expr b]
    /\ Den var_of (labels t) (Node R_expr b) e.

(* T1 *)
Theorem parse_denotes_lc : forall var_of s ts s',
  peg (E_rule R_goat) s (Ok ts s') ->
  Forall core_tree ts ->
  Forall Complete ts ->
  exists t e, ts = [t] /\ Den_goat var_of t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of s ts s' Hparse Hcore Hcomplete.
  assert (Hgen : gen (E_rule R_goat) ts)
    by exact (peg_gen _ _ _ Hparse ts s' eq_refl Hcore).
  destruct (gen_node_of Hgen eq_refl) as (cs & Hts & Hbody). subst ts.
  assert (Hroot : Complete (Node R_goat cs)) by (inversion Hcomplete; assumption).
  inversion Hroot as [| ? ? Hhas Hkids_complete]; subst.
  simpl in Hhas.
  destruct (shape_goat cs Hbody Hhas) as (b & ->).
  assert (Hvalid_kids : Forall valid [Node R_expr b])
    by exact (gen_valid _ _ Hbody).
  assert (Hvalid_expr : valid (Node R_expr b))
    by (inversion Hvalid_kids; assumption).
  assert (Hcomplete_expr : Complete (Node R_expr b))
    by (inversion Hkids_complete; assumption).
  set (t := Node R_goat [Node R_expr b]).
  assert (Hkind : TotKind var_of (labels t) (Node R_expr b))
    by exact (tot var_of (labels t) _ Hvalid_expr Hcomplete_expr).
  simpl in Hkind. destruct Hkind as (e & Hden).
  assert (Hlc : lc e)
    by exact (proj1 (den_lc var_of (labels t)) _ _ Hden).
  assert (Hlc_exp : lc_exp e) by exact (lc_lc_exp e Hlc).
  assert (Hdenoted : Den_goat var_of t e) by (exists b; split; [ reflexivity | exact Hden ]).
  exists t, e. repeat split; assumption.
Qed.
