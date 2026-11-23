(* List patterns, worked (phase 8, stage 8): a `match` of list arms, a
   destructuring from a value that is not a literal, one from a literal, and a
   function whose parameter is a pattern each parse, and T1 applies: the tree
   denotes the decision tree `GoatDen.v` builds (`lmatch`, `ltree_or_unit`,
   `lit_bind`, `lps_wrap`) and it is locally closed. *)

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
Require Import Goat.GoatLoopExample.
Open Scope string_scope.
Open Scope list_scope.

Definition list_prefix : list tok :=
  [TSym "tag"; TName "List"; TSym "="; TName "Empty"; TSym "|"; TName "Link"; TSym "(";
   TSym "_"; TSym ","; TName "List"; TSym ")"].

(* `match [1, 2] do [] then 0 [a, ...r] then a done` *)
Definition match_program : list tok :=
  list_prefix ++
  [TSym "match"; TSym "["; TNum 1; TSym ","; TNum 2; TSym "]"; TSym "do";
   TSym "["; TSym "]"; TSym "then"; TNum 0;
   TSym "["; TName "a"; TSym ","; TSym "..."; TName "r"; TSym "]"; TSym "then"; TName "a";
   TSym "done"].

(* `f = program(xs) do [a, b] = xs a done`: any other length stops the program. *)
Definition destructure_program : list tok :=
  list_prefix ++
  [TName "f"; TSym "="; TSym "program"; TSym "("; TName "xs"; TSym ")"; TSym "do";
   TSym "["; TName "a"; TSym ","; TName "b"; TSym "]"; TSym "="; TName "xs"; TName "a";
   TSym "done"].

(* `[a, ...r] = [1, 2] a`: a literal whose length fits binds each name directly. *)
Definition literal_program : list tok :=
  list_prefix ++
  [TSym "["; TName "a"; TSym ","; TSym "..."; TName "r"; TSym "]"; TSym "=";
   TSym "["; TNum 1; TSym ","; TNum 2; TSym "]"; TName "a"].

(* `f = program([a, ...r], n) do a done` *)
Definition param_program : list tok :=
  list_prefix ++
  [TName "f"; TSym "="; TSym "program"; TSym "("; TSym "["; TName "a"; TSym ",";
   TSym "..."; TName "r"; TSym "]"; TSym ","; TName "n"; TSym ")"; TSym "do"; TName "a";
   TSym "done"].

(* `match [1, 2] do [] then 0 5 then 1 else 2 done`: a list arm and a literal arm. *)
Definition mixed_program : list tok :=
  [TSym "match"; TSym "["; TNum 1; TSym ","; TNum 2; TSym "]"; TSym "do";
   TSym "["; TSym "]"; TSym "then"; TNum 0;
   TNum 5; TSym "then"; TNum 1;
   TSym "else"; TNum 2; TSym "done"].

Definition mixed_ts : list tree :=
  match run 900 (E_rule R_goat) mixed_program with Some (Ok ts _) => ts | _ => [] end.

Example mixed_parses : peg (E_rule R_goat) mixed_program (Ok mixed_ts []).
Proof. apply (run_sound 900). reflexivity. Qed.

(* Lowering reports a `match` that mixes list and literal patterns, so the tree
   denotes no term and T1's other branch holds. *)
Example mixed_rejected : Forall Reject mixed_ts.
Proof.
  unfold mixed_ts. cbv.
  apply Forall_cons; [ | apply Forall_nil ].
  find_reject.
Qed.

Definition match_ts : list tree :=
  match run 900 (E_rule R_goat) match_program with Some (Ok ts _) => ts | _ => [] end.
Definition destructure_ts : list tree :=
  match run 900 (E_rule R_goat) destructure_program with Some (Ok ts _) => ts | _ => [] end.
Definition literal_ts : list tree :=
  match run 900 (E_rule R_goat) literal_program with Some (Ok ts _) => ts | _ => [] end.
Definition param_ts : list tree :=
  match run 900 (E_rule R_goat) param_program with Some (Ok ts _) => ts | _ => [] end.

Example match_parses : peg (E_rule R_goat) match_program (Ok match_ts []).
Proof. apply (run_sound 900). reflexivity. Qed.
Example destructure_parses : peg (E_rule R_goat) destructure_program (Ok destructure_ts []).
Proof. apply (run_sound 900). reflexivity. Qed.
Example literal_parses : peg (E_rule R_goat) literal_program (Ok literal_ts []).
Proof. apply (run_sound 900). reflexivity. Qed.
Example param_parses : peg (E_rule R_goat) param_program (Ok param_ts []).
Proof. apply (run_sound 900). reflexivity. Qed.

Lemma match_core : Forall core_tree match_ts. Proof. core_all. Qed.
Lemma destructure_core : Forall core_tree destructure_ts. Proof. core_all. Qed.
Lemma literal_core : Forall core_tree literal_ts. Proof. core_all. Qed.
Lemma param_core : Forall core_tree param_ts. Proof. core_all. Qed.

Ltac match_list :=
  unfold match_read; split;
  [ unfold has; eexists; in_list
  | intros Hall; first [ solve [ in_list ] | (exfalso; arm_of_another_kind Hall) ] ].

Ltac comp_list := first [ match_list | (intros c Hc; discriminate Hc) | comp_close' ].

Lemma match_complete : Forall Complete match_ts.
Proof. comp_all. all: comp_list. Qed.
Lemma destructure_complete : Forall Complete destructure_ts.
Proof. comp_all. all: comp_list. Qed.
Lemma literal_complete : Forall Complete literal_ts.
Proof. comp_all. all: comp_list. Qed.
Lemma param_complete : Forall Complete param_ts.
Proof. comp_all. all: comp_list. Qed.

Lemma match_accepted : Forall Accepted match_ts. Proof. acc_all. Qed.
Lemma destructure_accepted : Forall Accepted destructure_ts. Proof. acc_all. Qed.
Lemma literal_accepted : Forall Accepted literal_ts. Proof. acc_all. Qed.
Lemma param_accepted : Forall Accepted param_ts. Proof. acc_all. Qed.

Lemma match_known : Forall (goat_known []) match_ts. Proof. known_all. Qed.
Lemma destructure_known : Forall (goat_known []) destructure_ts. Proof. known_all. Qed.
Lemma literal_known : Forall (goat_known []) literal_ts. Proof. known_all. Qed.
Lemma param_known : Forall (goat_known []) param_ts. Proof. known_all. Qed.

Example match_denotes_lc : forall var_of,
  exists t e, match_ts = [t] /\ Den_goat var_of [] t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of.
  exact (parse_denotes_accepted var_of [] match_program match_ts []
           match_parses match_core match_complete match_known match_accepted).
Qed.

Example destructure_denotes_lc : forall var_of,
  exists t e, destructure_ts = [t] /\ Den_goat var_of [] t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of.
  exact (parse_denotes_accepted var_of [] destructure_program destructure_ts []
           destructure_parses destructure_core destructure_complete destructure_known
           destructure_accepted).
Qed.

Example literal_denotes_lc : forall var_of,
  exists t e, literal_ts = [t] /\ Den_goat var_of [] t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of.
  exact (parse_denotes_accepted var_of [] literal_program literal_ts []
           literal_parses literal_core literal_complete literal_known literal_accepted).
Qed.

Example param_denotes_lc : forall var_of,
  exists t e, param_ts = [t] /\ Den_goat var_of [] t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of.
  exact (parse_denotes_accepted var_of [] param_program param_ts []
           param_parses param_core param_complete param_known param_accepted).
Qed.
