(* Loops, worked (phase 8, stage 5): `repeat`, `for ... from ... to` and
   `for ... in` each denote the tail-recursive term lowering builds, and T1
   applies to a program that runs each. *)

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
Require Import Goat.GoatTagExample.
Require Import Goat.GoatPhase3.
Open Scope string_scope.
Open Scope list_scope.

Definition number_expr (n : nat) : tree := Node R_expr [Node R_number [Leaf (TNum n)]].

Lemma number_expr_den : forall `{TT : TagTable} var_of tbl n,
  Den var_of tbl (number_expr n) (e_num (z_of_nat n)).
Proof.
  intros TT var_of tbl n. unfold number_expr.
  apply D_expr. apply DB_chain. apply DM_chain.
  eapply DC_head; [ apply D_num | apply DP_nil ].
Qed.

(* `repeat 2 times do done` counts from 0 below 2 and runs an empty body. *)
Example repeat_denotes : forall var_of,
  exists e,
    Den var_of [] (Node R_repeat_loop
                     [sym "repeat"; number_expr 2; sym "times"; sym "do"; sym "done"]) e
    /\ lc e.
Proof.
  intros var_of.
  destruct (atom_fresh (loop_atoms (e_num 0) (e_num (z_of_nat 2)) e_unit)) as [c Hc].
  destruct (exists_apart3 (loop_atoms (e_num 0) (e_num (z_of_nat 2)) e_unit) c)
    as (s & t & g & Happ).
  exists (counted s t g c (e_num 0) (e_num (z_of_nat 2)) bop_lt e_unit). split.
  - apply (D_repeat var_of [] _ _ [] e_unit s t g c); [ apply number_expr_den | apply DBo_none | exact Hc | exact Happ ].
  - apply lc_counted; exact I.
Qed.

(* `for i from 1 to 3 do i done` includes both ends (`<=`), and the body reads
   the counter, which is the function's parameter. *)
Example count_denotes : forall var_of,
  exists e,
    Den var_of [] (Node R_count_loop
                     [Node R_for_kw [sym "for"]; ident "i"; Node R_from_kw [Leaf (TName "from")];
                      number_expr 1; Node R_to_kw [Leaf (TName "to")]; number_expr 3;
                      sym "do"; Node R_expr [ident "i"]; sym "done"]) e
    /\ lc e.
Proof.
  intros var_of.
  assert (Hbody : Den_body var_of [] [Node R_expr [ident "i"]] (e_fvar_f (var_of "i"))).
  { apply DBo_some. apply D_expr. apply DB_chain. apply DM_chain.
    eapply DC_head; [ apply D_name; reflexivity | apply DP_nil ]. }
  destruct (exists_apart3 (loop_atoms (e_num (z_of_nat 1)) (e_num (z_of_nat 3)) (e_fvar_f (var_of "i")))
              (var_of "i")) as (s & t & g & Happ).
  exists (counted s t g (var_of "i") (e_num (z_of_nat 1)) (e_num (z_of_nat 3)) bop_lte
            (e_fvar_f (var_of "i"))). split.
  - apply (D_count var_of [] "i" (TName "from") (TName "to") _ _ _ _ [_] _ s t g);
      [ left; reflexivity | left; reflexivity | apply number_expr_den | apply number_expr_den
      | exact Hbody | exact Happ ].
  - apply lc_counted; exact I.
Qed.

(* `for x in xs do done` walks the list through the prelude's `Link` and `Empty`. *)
Example each_denotes : forall var_of,
  exists e,
    @Den (mk_tags (decl_entries list_decl)) var_of []
      (Node R_each_loop
         [Node R_for_kw [sym "for"]; ident "x"; Node R_in_kw [Leaf (TName "in")];
          Node R_expr [ident "xs"]; sym "do"; sym "done"]) e
    /\ lc e.
Proof.
  intros var_of.
  assert (Hlist : @Den (mk_tags (decl_entries list_decl)) var_of []
                    (Node R_expr [ident "xs"]) (e_fvar_f (var_of "xs"))).
  { apply D_expr. apply DB_chain. apply DM_chain.
    eapply DC_head; [ apply D_name; reflexivity | apply DP_nil ]. }
  destruct (exists_apart4 (fv_exp (e_fvar_f (var_of "xs")) `union` fv_exp e_unit) (var_of "x"))
    as (g & r & sp & tp & Happ).
  exists (each_term list_g 0 1 g r sp tp (var_of "x") (e_fvar_f (var_of "xs")) e_unit). split.
  - apply (D_each (TT := mk_tags (decl_entries list_decl)) var_of []
             "x" (TName "in") _ _ [] e_unit list_g 0 1 g r sp tp);
      [ left; reflexivity | reflexivity | reflexivity | exact Hlist | apply DBo_none | exact Happ ].
  - apply lc_each_term; exact I.
Qed.

(* T1 applies to programs that run each loop. *)
Definition repeat_program : list tok :=
  [TSym "repeat"; TNum 3; TSym "times"; TSym "do"; TSym "done"].

Definition count_program : list tok :=
  [TSym "for"; TName "i"; TName "from"; TNum 1; TName "to"; TNum 3; TSym "do";
   TName "i"; TSym "done"].

Definition each_program : list tok :=
  [TSym "tag"; TName "List"; TSym "="; TName "Empty"; TSym "|"; TName "Link"; TSym "(";
   TSym "_"; TSym ","; TName "List"; TSym ")";
   TSym "for"; TName "x"; TName "in"; TSym "["; TNum 1; TSym ","; TNum 2; TSym "]";
   TSym "do"; TName "x"; TSym "done"].

Definition repeat_ts : list tree :=
  match run 600 (E_rule R_goat) repeat_program with Some (Ok ts _) => ts | _ => [] end.

Definition count_ts : list tree :=
  match run 600 (E_rule R_goat) count_program with Some (Ok ts _) => ts | _ => [] end.

Definition each_ts : list tree :=
  match run 600 (E_rule R_goat) each_program with Some (Ok ts _) => ts | _ => [] end.

Example repeat_parses : peg (E_rule R_goat) repeat_program (Ok repeat_ts []).
Proof. apply (run_sound 600). reflexivity. Qed.

Example count_parses : peg (E_rule R_goat) count_program (Ok count_ts []).
Proof. apply (run_sound 600). reflexivity. Qed.

Example each_parses : peg (E_rule R_goat) each_program (Ok each_ts []).
Proof. apply (run_sound 600). reflexivity. Qed.

Ltac core_all :=
  cbv;
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Core_leaf
    | (apply Core_node; [ reflexivity | ]) ].

Lemma repeat_core : Forall core_tree repeat_ts. Proof. core_all. Qed.
Lemma count_core : Forall core_tree count_ts. Proof. core_all. Qed.
Lemma each_core : Forall core_tree each_ts. Proof. core_all. Qed.

(* GoatTagExample's closer, and a payload type that names the group. *)
Ltac comp_close' :=
  first
  [ exact I
  | (match goal with |- has _ _ => unfold has; eexists; in_list end)
  | (right; left; reflexivity)
  | (left; reflexivity)
  | (intros [c Hlast]; simpl in Hlast; discriminate Hlast)
  | apply Forall_nil
  | (apply Forall_cons;
     [ first [ (intros H; discriminate H) | (intros _; reflexivity) ] | comp_close' ])
  | (split; [ comp_close' | comp_close' ])
  | (intros Hall; first [ solve [ in_list ] | (exfalso; arm_of_another_kind Hall) ])
  | (left; comp_close') ].

Ltac comp_all :=
  cbv;
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Cp_leaf | apply Cp_node ];
  simpl; try exact I.

Lemma repeat_complete : Forall Complete repeat_ts.
Proof. comp_all. all: comp_close'. Qed.

Lemma repeat_accepted : Forall Accepted repeat_ts.
Proof. acc_all. Qed.

Lemma count_complete : Forall Complete count_ts.
Proof. comp_all. all: comp_close'. Qed.

Lemma count_accepted : Forall Accepted count_ts.
Proof. acc_all. Qed.

Lemma each_complete : Forall Complete each_ts.
Proof. comp_all. all: comp_close'. Qed.

Lemma each_accepted : Forall Accepted each_ts.
Proof. acc_all. Qed.

Ltac known_all :=
  cbv;
  apply Forall_cons; [ | apply Forall_nil ];
  unfold goat_known; cbv;
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Kn_leaf
    | (apply Kn_node;
       [ first [ exact I
               | (cbv; intros H; discriminate H)
               | (cbv; split; intros H; discriminate H)
               | (cbv; eexists; eexists; eexists; split; reflexivity) ]
       | ]) ].

Lemma repeat_known : Forall (goat_known []) repeat_ts. Proof. known_all. Qed.
Lemma count_known : Forall (goat_known []) count_ts. Proof. known_all. Qed.
Lemma each_known : Forall (goat_known []) each_ts. Proof. known_all. Qed.

Example repeat_denotes_lc : forall var_of,
  exists t e, repeat_ts = [t] /\ Den_goat var_of [] t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of.
  exact (parse_denotes_accepted var_of [] repeat_program repeat_ts []
           repeat_parses repeat_core repeat_complete repeat_known repeat_accepted).
Qed.

Example count_denotes_lc : forall var_of,
  exists t e, count_ts = [t] /\ Den_goat var_of [] t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of.
  exact (parse_denotes_accepted var_of [] count_program count_ts []
           count_parses count_core count_complete count_known count_accepted).
Qed.

Example each_denotes_lc : forall var_of,
  exists t e, each_ts = [t] /\ Den_goat var_of [] t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of.
  exact (parse_denotes_accepted var_of [] each_program each_ts []
           each_parses each_core each_complete each_known each_accepted).
Qed.
