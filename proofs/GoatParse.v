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
   prelude's, and its expression if it has one, read with that table: a program
   with none is the unit value. *)
Definition Den_goat (var_of : string -> termvar) (ptbl : tagtab) (t : tree) (e : exp) : Prop :=
  exists decls bs,
    t = Node R_goat (decls ++ bs)
    /\ Forall (fun d => exists c, d = Node R_tag_decl c) decls
    /\ @Den_body (mk_tags (ptbl ++ flat_map decl_entries decls)) var_of (labels t) bs e.

(* The names the program resolves are in that table. *)
Definition goat_known (ptbl : tagtab) (t : tree) : Prop :=
  match t with
  | Node R_goat cs => Forall (Known (ptbl ++ flat_map decl_entries cs)) cs
  | _ => True
  end.

(* T1, for a tree lowering accepts. *)
Theorem parse_denotes_accepted : forall var_of ptbl s ts s',
  peg (E_rule R_goat) s (Ok ts s') ->
  Forall core_tree ts ->
  Forall Complete ts ->
  Forall (goat_known ptbl) ts ->
  Forall Accepted ts ->
  exists t e, ts = [t] /\ Den_goat var_of ptbl t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of ptbl s ts s' Hparse Hcore Hcomplete Hknown Haccepted.
  assert (Hgen : gen (E_rule R_goat) ts)
    by exact (peg_gen _ _ _ Hparse ts s' eq_refl Hcore).
  destruct (gen_node_of Hgen eq_refl) as (cs & Hts & Hbody). subst ts.
  assert (Hroot : Complete (Node R_goat cs)) by (inversion Hcomplete; assumption).
  inversion Hroot as [| ? ? _ Hkids_complete]; subst.
  destruct (shape_goat cs Hbody) as (decls & bs & -> & Hdecls & Hbs).
  assert (Hvalid_kids : Forall valid (decls ++ bs))
    by exact (gen_valid _ _ Hbody).
  apply Forall_app in Hvalid_kids as [_ Hvalid_bs].
  apply Forall_app in Hkids_complete as [_ Hcomplete_bs].
  set (t := Node R_goat (decls ++ bs)).
  set (tt := ptbl ++ flat_map decl_entries decls).
  assert (Hknown_goat : goat_known ptbl t) by (inversion Hknown; assumption).
  unfold goat_known, t in Hknown_goat.
  assert (Haccepted_goat : Accepted t) by (inversion Haccepted; assumption).
  inversion Haccepted_goat as [| ? ? _ Haccepted_kids]; subst.
  apply Forall_app in Haccepted_kids as [_ Haccepted_bs].
  assert (Htt : ptbl ++ flat_map decl_entries (decls ++ bs) = tt).
  { unfold tt. rewrite flat_map_app.
    destruct Hbs as [-> | (cb & ->)]; simpl; rewrite ?app_nil_r; reflexivity. }
  rewrite Htt in Hknown_goat.
  apply Forall_app in Hknown_goat as [_ Hknown_bs].
  assert (Hden : exists e, @Den_body (mk_tags tt) var_of (labels t) bs e /\ lc e).
  { destruct Hbs as [-> | (cb & ->)].
    - exists e_unit. split; [ apply DBo_none | exact I ].
    - inversion Hvalid_bs as [| ? ? Hvalid_expr _]; subst.
      inversion Hcomplete_bs as [| ? ? Hcomplete_expr _]; subst.
      inversion Hknown_bs as [| ? ? Hknown_expr _]; subst.
      inversion Haccepted_bs as [| ? ? Haccepted_expr _]; subst.
      assert (Hkind : TotKind (TT := mk_tags tt) var_of (labels t) (Node R_expr cb))
        by exact (@tot (mk_tags tt) var_of (labels t) _ Hvalid_expr Hcomplete_expr
                    Hknown_expr Haccepted_expr).
      simpl in Hkind. destruct Hkind as (e & Hd).
      exists e. split; [ apply DBo_some; exact Hd | ].
      exact (proj1 (@den_lc (mk_tags tt) var_of (labels t)) _ _ Hd). }
  destruct Hden as (e & Hbody_den & Hlc).
  assert (Hlc_exp : lc_exp e) by exact (lc_lc_exp e Hlc).
  exists t, e. repeat split; try assumption.
  exists decls, bs. repeat split; assumption.
Qed.

(* T1: a parse tree is one lowering reports, or denotes a locally closed term. *)
Theorem parse_denotes_lc : forall var_of ptbl s ts s',
  peg (E_rule R_goat) s (Ok ts s') ->
  Forall core_tree ts ->
  Forall Complete ts ->
  Forall (goat_known ptbl) ts ->
  exists t, ts = [t]
    /\ (Reject t \/ exists e, Den_goat var_of ptbl t e /\ lc_exp e /\ lc e).
Proof.
  intros var_of ptbl s ts s' Hparse Hcore Hcomplete Hknown.
  assert (Hgen : gen (E_rule R_goat) ts)
    by exact (peg_gen _ _ _ Hparse ts s' eq_refl Hcore).
  destruct (gen_node_of Hgen eq_refl) as (cs & Hts & Hbody). subst ts.
  exists (Node R_goat cs). split; [ reflexivity | ].
  destruct (reject_or_accepted (Node R_goat cs)) as [Hrej | Hacc]; [ left; exact Hrej | right ].
  destruct (parse_denotes_accepted var_of ptbl s _ s' Hparse Hcore Hcomplete Hknown
              (Forall_cons _ Hacc (Forall_nil _))) as (t & e & Heq & Hden & Hlc).
  injection Heq as <-. exists e. split; [ exact Hden | exact Hlc ].
Qed.
