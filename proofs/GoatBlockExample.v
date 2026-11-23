(* The block, worked (phase 8, stage 6): a program that is empty or ends in a
   binding, `a; b`, a function or call with no parameters, and a function
   written after a value it uses. Each tree denotes a locally closed term. *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatMeta.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatShape.
Require Import Goat.GoatParse.
Require Import Goat.GoatExample.
Require Import Goat.GoatLoopExample.
Open Scope string_scope.
Open Scope list_scope.

Definition value_of (c : tree) : tree := Node R_value [c].

Definition num_tree (n : nat) : tree := Node R_number [Leaf (TNum n)].

Definition bind_tree (x : string) (v : tree) : tree :=
  Node R_declaration [ident x; sym "="; value_of v].

Lemma den_lc_of : forall `{TT : TagTable} var_of tbl t e,
  Den var_of tbl t e -> lc e.
Proof. intros TT var_of tbl t e H. exact (proj1 (den_lc var_of tbl) _ _ H). Qed.

Lemma num_den : forall `{TT : TagTable} var_of tbl n,
  Den var_of tbl (value_of (num_tree n)) (e_num (z_of_nat n)).
Proof.
  intros TT var_of tbl n. apply D_value. apply DM_chain.
  eapply DC_head; [ apply D_num | apply DP_nil ].
Qed.

(* A program with no expression is the unit value. *)
Example empty_program_is_unit : forall var_of,
  Den_goat var_of [] (Node R_goat []) e_unit.
Proof.
  intros var_of. exists [], [].
  split; [ reflexivity | split; [ apply Forall_nil | apply DBo_none ] ].
Qed.

(* `x = 1` ends in a binding: the value is bound, and the block is that value. *)
Example trailing_binding : forall var_of,
  exists e,
    Den var_of [] (Node R_expr [bind_tree "x" (num_tree 1)]) e /\ lc e.
Proof.
  intros var_of.
  assert (H : Den var_of [] (Node R_expr [bind_tree "x" (num_tree 1)])
                (e_let (e_num (z_of_nat 1)) (close_exp (var_of "x") (e_fvar_f (var_of "x"))))).
  { apply D_expr. apply (DB_top var_of [] _ [] [] _).
    eapply DK_value; [ apply DD_plain; apply num_den | reflexivity | apply DK_end ]. }
  eexists. split; [ exact H | eapply den_lc_of; exact H ].
Qed.

(* `a; b` runs `a`, drops its value, and continues with `b`. *)
Example statement_then_value : forall var_of,
  exists e,
    Den var_of [] (Node R_expr [ident "a"; Node R_sequel [sym ";"]; ident "b"]) e /\ lc e.
Proof.
  intros var_of.
  assert (Ha : Den_math var_of [] [ident "a"] (e_fvar_f (var_of "a"))).
  { apply DM_chain. eapply DC_head; [ apply D_name; reflexivity | apply DP_nil ]. }
  assert (Hb : Den_math var_of [] [ident "b"] (e_fvar_f (var_of "b"))).
  { apply DM_chain. eapply DC_head; [ apply D_name; reflexivity | apply DP_nil ]. }
  assert (H : Den var_of [] (Node R_expr [ident "a"; Node R_sequel [sym ";"]; ident "b"])
                (e_let (e_fvar_f (var_of "a")) (e_fvar_f (var_of "b")))).
  { apply D_expr. apply (DB_top var_of [] _ [] [] _).
    apply (DK_seq var_of [] [] e_unit [ident "a"] _ [ident "b"]);
      [ exact Ha | apply DK_chain; exact Hb ]. }
  eexists. split; [ exact H | eapply den_lc_of; exact H ].
Qed.

(* `program() do done` takes one hidden parameter, pinned to the unit value, and
   returns the unit value. *)
Example function_without_parameters : forall var_of,
  exists e,
    Den var_of [] (Node R_function [Leaf (TSym "program"); sym "("; sym ")"; sym "do"; sym "done"]) e
    /\ lc e.
Proof.
  intros var_of.
  destruct (atom_fresh (fv_exp e_unit)) as [s Hs].
  exists (unit_arg s e_unit). split.
  - exact (D_function_unit var_of [] (TSym "program") [] e_unit s (DBo_none var_of []) Hs).
  - apply lc_unit_arg. exact I.
Qed.

(* `f()` applies `f` to the unit value. *)
Example call_without_arguments : forall var_of,
  Den_chain var_of [] [ident "f"; Node R_call [sym "("; sym ")"]]
    (e_app (e_fvar_f (var_of "f")) e_unit).
Proof.
  intros var_of.
  eapply DC_head; [ apply D_name; reflexivity | apply DP_call_unit; apply DP_nil ].
Qed.

(* `x = 1  g = program(y) do x done  g(2)`: [g] uses the value [x], so it stays
   where it is written, a plain binding after [x]; the group is not hoisted. *)
Example function_after_a_value : forall var_of,
  var_of "x" <> var_of "y" ->
  exists e,
    Den var_of []
      (Node R_expr
         [bind_tree "x" (num_tree 1);
          Node R_declaration
            [ident "g"; sym "=";
             value_of (Node R_function
                         [Leaf (TSym "program"); sym "("; Node R_params [ident "y"]; sym ")";
                          sym "do"; Node R_expr [ident "x"]; sym "done"])];
          ident "g"; Node R_call [sym "("; Node R_arguments [number_expr 2]; sym ")"]]) e
    /\ lc e.
Proof.
  intros var_of Hne.
  assert (Hx : Den var_of [] (Node R_expr [ident "x"]) (e_fvar_f (var_of "x"))).
  { apply D_expr_g. intros ctx fin. apply DK_chain. apply DM_chain.
    eapply DC_head; [ apply D_name; reflexivity | apply DP_nil ]. }
  assert (Hg : Den_decl var_of []
                 (Node R_declaration
                    [ident "g"; sym "=";
                     value_of (Node R_function
                                 [Leaf (TSym "program"); sym "("; Node R_params [ident "y"]; sym ")";
                                  sym "do"; Node R_expr [ident "x"]; sym "done"])])
                 "g" (curry [var_of "y"] (e_fvar_f (var_of "x")))).
  { apply DD_plain. apply D_value. apply DM_chain.
    eapply DC_head; [ | apply DP_nil ].
    apply (D_function var_of [] (TSym "program") [ident "y"] ["y"] [ident "x"]
             (e_fvar_f (var_of "x")));
      [ apply DPa_one | exact Hx ]. }
  assert (Hcaptures : mentions_any [var_of "x"] (curry [var_of "y"] (e_fvar_f (var_of "x"))) = true).
  { unfold mentions_any. simpl. rewrite orb_false_r. unfold mentions.
    apply AtomSetImpl.mem_1.
    unfold curry. simpl. unfold close_exp. simpl.
    destruct (var_of "x" == var_of "y") as [Heq | _]; [ exfalso; exact (Hne Heq) | ].
    simpl. fsetdec. }
  assert (Hcall : Den_blk var_of [] [var_of "g"; var_of "x"] (e_fvar_f (var_of "g"))
                    [ident "g"; Node R_call [sym "("; Node R_arguments [number_expr 2]; sym ")"]]
                    [] [] (e_app (e_fvar_f (var_of "g")) (e_num (z_of_nat 2)))).
  { apply DK_chain. apply DM_chain.
    eapply DC_head; [ apply D_name; reflexivity | ].
    eapply DP_call with (es := [e_num (z_of_nat 2)]); [ | apply DP_nil ].
    apply DA_last. apply number_expr_den. }
  assert (Hblk : Den_blk var_of [] [] e_unit
                   [bind_tree "x" (num_tree 1);
                    Node R_declaration
                      [ident "g"; sym "=";
                       value_of (Node R_function
                                   [Leaf (TSym "program"); sym "("; Node R_params [ident "y"]; sym ")";
                                    sym "do"; Node R_expr [ident "x"]; sym "done"])];
                    ident "g"; Node R_call [sym "("; Node R_arguments [number_expr 2]; sym ")"]]
                   [] []
                   (e_let (e_num (z_of_nat 1))
                      (close_exp (var_of "x")
                         (fn_place (var_of "g") (curry [var_of "y"] (e_fvar_f (var_of "x")))
                            (e_app (e_fvar_f (var_of "g")) (e_num (z_of_nat 2))))))).
  { eapply DK_value.
    - apply DD_plain. apply num_den.
    - reflexivity.
    - eapply DK_late; [ exact Hg | reflexivity | exact Hcaptures | reflexivity | exact Hcall ]. }
  eexists. split.
  - apply D_expr. apply (DB_top var_of [] _ [] [] _ Hblk).
  - eapply den_lc_of. apply D_expr. apply (DB_top var_of [] _ [] [] _ Hblk).
Qed.
