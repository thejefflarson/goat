(* T1 (ADR 0030): every parse of a core-fragment token stream denotes a locally
   closed term.

   Scope: the core fragment only, over a trusted token stream. The lexer, the
   rules outside the fragment (rule_map.rs lists them), and the Rust lowering
   are not covered. *)

From Stdlib Require Import String List.
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
      | R_take, [_; Node _ [Leaf (TName l)]] => [l]
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

(* The program is its tag declarations, read first into a table that follows the
   prelude's, and its single top-level expression, read with that table. *)
Definition Den_goat (var_of : string -> termvar) (ptbl : tagtab) (t : tree) (e : exp) : Prop :=
  exists decls b,
    t = Node R_goat (decls ++ [Node R_expr b])
    /\ Forall (fun d => exists c, d = Node R_tag_decl c) decls
    /\ @Den (mk_tags (ptbl ++ flat_map decl_entries decls)) var_of (labels t)
         (Node R_expr b) e.

(* The names the program resolves are in that table. *)
Definition goat_known (ptbl : tagtab) (t : tree) : Prop :=
  match t with
  | Node R_goat cs => Forall (Known (ptbl ++ flat_map decl_entries cs)) cs
  | _ => True
  end.

(* T1 *)
Theorem parse_denotes_lc : forall var_of ptbl s ts s',
  peg (E_rule R_goat) s (Ok ts s') ->
  Forall core_tree ts ->
  Forall Complete ts ->
  Forall (goat_known ptbl) ts ->
  exists t e, ts = [t] /\ Den_goat var_of ptbl t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of ptbl s ts s' Hparse Hcore Hcomplete Hknown.
  assert (Hgen : gen (E_rule R_goat) ts)
    by exact (peg_gen _ _ _ Hparse ts s' eq_refl Hcore).
  destruct (gen_node_of Hgen eq_refl) as (cs & Hts & Hbody). subst ts.
  assert (Hroot : Complete (Node R_goat cs)) by (inversion Hcomplete; assumption).
  inversion Hroot as [| ? ? Hhas Hkids_complete]; subst.
  simpl in Hhas.
  destruct (shape_goat cs Hbody Hhas) as (decls & b & -> & Hdecls).
  assert (Hvalid_kids : Forall valid (decls ++ [Node R_expr b]))
    by exact (gen_valid _ _ Hbody).
  apply Forall_app in Hvalid_kids as [_ Hvalid_expr'].
  assert (Hvalid_expr : valid (Node R_expr b))
    by (inversion Hvalid_expr'; assumption).
  apply Forall_app in Hkids_complete as [_ Hcomplete_expr'].
  assert (Hcomplete_expr : Complete (Node R_expr b))
    by (inversion Hcomplete_expr'; assumption).
  set (t := Node R_goat (decls ++ [Node R_expr b])).
  set (tt := ptbl ++ flat_map decl_entries decls).
  assert (Hknown_goat : goat_known ptbl t) by (inversion Hknown; assumption).
  unfold goat_known, t in Hknown_goat.
  assert (Htt : ptbl ++ flat_map decl_entries (decls ++ [Node R_expr b]) = tt)
    by (unfold tt; rewrite flat_map_app; simpl; rewrite app_nil_r; reflexivity).
  rewrite Htt in Hknown_goat.
  apply Forall_app in Hknown_goat as [_ Hknown_expr'].
  assert (Hknown_expr : Known tt (Node R_expr b))
    by (inversion Hknown_expr'; assumption).
  assert (Hkind : TotKind (TT := mk_tags tt) var_of (labels t) (Node R_expr b))
    by exact (@tot (mk_tags tt) var_of (labels t) _ Hvalid_expr Hcomplete_expr Hknown_expr).
  simpl in Hkind. destruct Hkind as (e & Hden).
  assert (Hlc : lc e)
    by exact (proj1 (@den_lc (mk_tags tt) var_of (labels t)) _ _ Hden).
  assert (Hlc_exp : lc_exp e) by exact (lc_lc_exp e Hlc).
  assert (Hdenoted : Den_goat var_of ptbl t e)
    by (exists decls, b; repeat split; [ exact Hdecls | exact Hden ]).
  exists t, e. repeat split; assumption.
Qed.
