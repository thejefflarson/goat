(* Tags, `match` and lists, worked (phase 8, stage 4): the table a declaration
   builds is the group GoatPhase3.v types, a list literal denotes the term that
   file types as a list of Int, and T1 applies to a program that declares a
   tag and matches on it. *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMeta.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatShape.
Require Import Goat.GoatParse.
Require Import Goat.GoatExample.
Require Import Goat.GoatPhase3.
Open Scope string_scope.
Open Scope list_scope.

(* The prelude's `tag List = Empty | Link(_, List)`: `_` is parameter 0 (code 6)
   and the group's own name is code 0. *)
Definition list_decl : tree :=
  Node R_tag_decl
    [Node R_tag_kw [Leaf (TSym "tag")];
     Node R_group_name [ident "List"]; Leaf (TSym "=");
     Node R_tag_case [ident "Empty"];
     Leaf (TSym "|");
     Node R_tag_case
       [ident "Link"; Leaf (TSym "(");
        Node R_infer_type [Leaf (TSym "_")]; Leaf (TSym ",");
        Node R_type_name [Leaf (TName "List")]; Leaf (TSym ")")]].

Example list_decl_is_list_g :
  decl_entries list_decl = [("Empty", (list_g, 0)); ("Link", (list_g, 1))].
Proof. reflexivity. Qed.

(* tag Level = Low | Medium | High is GoatPhase3.v's `level`. *)
Definition level_decl : tree :=
  Node R_tag_decl
    [Node R_tag_kw [Leaf (TSym "tag")];
     Node R_group_name [ident "Level"]; Leaf (TSym "=");
     Node R_tag_case [ident "Low"]; Leaf (TSym "|");
     Node R_tag_case [ident "Medium"]; Leaf (TSym "|");
     Node R_tag_case [ident "High"]].

Example level_decl_is_level :
  decl_entries level_decl
  = [("Low", (level, 0)); ("Medium", (level, 1)); ("High", (level, 2))].
Proof. reflexivity. Qed.

(* tag Shot = Miss | Hit(Int) is `shot`. *)
Definition shot_decl : tree :=
  Node R_tag_decl
    [Node R_tag_kw [Leaf (TSym "tag")];
     Node R_group_name [ident "Shot"]; Leaf (TSym "=");
     Node R_tag_case [ident "Miss"]; Leaf (TSym "|");
     Node R_tag_case
       [ident "Hit"; Leaf (TSym "(");
        Node R_type_name [Leaf (TName "Int")]; Leaf (TSym ")")]].

Example shot_decl_is_shot :
  decl_entries shot_decl = [("Miss", (shot, 0)); ("Hit", (shot, 1))].
Proof. reflexivity. Qed.

(* A first declaration wins a name, as in lowering. *)
Example the_prelude_comes_first :
  tag_lookup (decl_entries list_decl ++ [("Link", (level, 2))]) "Link" = Some (list_g, 1).
Proof. reflexivity. Qed.

(* The list literal [1, 2] denotes Link(1, Link(2, Empty)), the term GoatPhase3.v
   types as a list of Int. *)
Example list_literal_denotes_one_two : forall var_of,
  @Den (mk_tags (decl_entries list_decl)) var_of []
    (Node R_list
       [sym "[";
        Node R_arguments
          [Node R_expr [Node R_number [Leaf (TNum 1)]]; sym ",";
           Node R_expr [Node R_number [Leaf (TNum 2)]]];
        sym "]"])
    one_two.
Proof.
  intros var_of.
  change one_two with (list_of list_g 0 list_g 1 [e_num 1; e_num 2]).
  eapply (D_list (TT := mk_tags (decl_entries list_decl)) var_of []
            _ [e_num 1; e_num 2] list_g 0 list_g 1);
    [ reflexivity | reflexivity | ].
  apply DA_more; [ | apply DA_last ].
  - apply D_expr. apply DB_chain. apply DM_chain.
    eapply DC_head; [ apply D_num | apply DP_nil ].
  - apply D_expr. apply DB_chain. apply DM_chain.
    eapply DC_head; [ apply D_num | apply DP_nil ].
Qed.

(* tag Shape = Circle(Number) | Dot
   match Circle(2) do Circle(r) then r  Dot then 0 done *)
Definition shapes : list tok :=
  [TSym "tag"; TName "Shape"; TSym "="; TName "Circle"; TSym "("; TName "Number";
   TSym ")"; TSym "|"; TName "Dot";
   TSym "match"; TName "Circle"; TSym "("; TNum 2; TSym ")"; TSym "do";
   TName "Circle"; TSym "("; TName "r"; TSym ")"; TSym "then"; TName "r";
   TName "Dot"; TSym "then"; TNum 0; TSym "done"].

Definition shapes_ts : list tree :=
  match run 600 (E_rule R_goat) shapes with Some (Ok ts _) => ts | _ => [] end.

Example shapes_parse : peg (E_rule R_goat) shapes (Ok shapes_ts []).
Proof. apply (run_sound 600). vm_compute. reflexivity. Qed.

Lemma shapes_core : Forall core_tree shapes_ts.
Proof.
  vm_compute.
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Core_leaf
    | (apply Core_node; [ reflexivity | ]) ].
Qed.

Lemma shapes_known : Forall (goat_known []) shapes_ts.
Proof.
  vm_compute.
  apply Forall_cons; [ | apply Forall_nil ].
  unfold goat_known. vm_compute.
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Kn_leaf
    | (apply Kn_node; [ first [ exact I | (vm_compute; intros H; discriminate H) ] | ]) ].
Qed.

Ltac comp_close :=
  first
  [ exact I
  | (match goal with |- has _ _ => unfold has; eexists; in_list end)
  | (right; left; reflexivity)
  | (intros [c Hlast]; simpl in Hlast; discriminate Hlast)
  | apply Forall_nil
  | (apply Forall_cons;
     [ first [ (intros H; discriminate H) | (intros _; reflexivity) ] | comp_close ])
  | (split; [ comp_close | comp_close ])
  | (intros Hall; first [ solve [ in_list ] | (exfalso; arm_of_another_kind Hall) ])
  | (left; comp_close) ].

Lemma shapes_complete : Forall Complete shapes_ts.
Proof.
  vm_compute.
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Cp_leaf | apply Cp_node ];
    simpl; try exact I.
  all: comp_close.
Qed.

Lemma shapes_accepted : Forall Accepted shapes_ts.
Proof. acc_all. Qed.

(* T1 applies to it, with the table the declaration builds. *)
Example shapes_denotes_lc : forall var_of,
  exists t e, shapes_ts = [t] /\ Den_goat var_of [] t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of.
  exact (parse_denotes_accepted var_of [] shapes shapes_ts [] shapes_parse
           shapes_core shapes_complete shapes_known shapes_accepted).
Qed.

(* `tag A = Ping` and `tag B = Pong` have one shape and are two groups. *)
Definition one_tag_decl (g c : string) : tree :=
  Node R_tag_decl
    [Node R_tag_kw [Leaf (TSym "tag")];
     Node R_group_name [ident g]; Leaf (TSym "=");
     Node R_tag_case [ident c]].

Example same_shape_decls_are_two_groups :
  tag_lookup (decl_entries (one_tag_decl "A" "Ping") ++ decl_entries (one_tag_decl "B" "Pong")) "Ping"
  <> tag_lookup (decl_entries (one_tag_decl "A" "Ping") ++ decl_entries (one_tag_decl "B" "Pong")) "Pong".
Proof. discriminate. Qed.
