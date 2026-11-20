(* Evidence that the hypotheses of T1 are satisfiable: a fuel-bounded
   interpreter of the PEG relation, sound for it, parses small programs, and
   the trees it builds are in the core fragment. *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatLit.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMeta.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatShape.
Require Import Goat.GoatParse.
Require Import Goat.GoatPhase2.
Open Scope string_scope.
Open Scope list_scope.

Fixpoint run (fuel : nat) (e : pexpr) (s : list tok) {struct fuel} : option result :=
  match fuel with
  | 0 => None
  | S f =>
      match e with
      | E_term t => Some (term_step t s)
      | E_rule r =>
          match run f (body r) s with
          | Some res => Some (wrap r res)
          | None => None
          end
      | E_seq a b =>
          match run f a s with
          | Some (Ok ts s1) =>
              match run f b s1 with
              | Some res => Some (prepend ts res)
              | None => None
              end
          | Some Fail => Some Fail
          | None => None
          end
      | E_alt a b =>
          match run f a s with
          | Some (Ok ts s1) => Some (Ok ts s1)
          | Some Fail => run f b s
          | None => None
          end
      | E_star a =>
          match run f a s with
          | Some Fail => Some (Ok [] s)
          | Some (Ok ts s1) =>
              match run f (E_star a) s1 with
              | Some (Ok ts' s2) => Some (Ok (ts ++ ts') s2)
              | _ => None
              end
          | None => None
          end
      | E_plus a => run f (E_seq a (E_star a)) s
      | E_opt a =>
          match run f a s with
          | Some (Ok ts s1) => Some (Ok ts s1)
          | Some Fail => Some (Ok [] s)
          | None => None
          end
      | E_expect a => run f a s
      end
  end.

Lemma run_sound : forall fuel e s res, run fuel e s = Some res -> peg e s res.
Proof.
  induction fuel as [| f IH]; intros e s res Hrun; [ discriminate Hrun | ].
  destruct e as [t | r | a b | a b | a | a | a | a]; simpl in Hrun.
  - (* terminal *)
    injection Hrun as <-. apply P_term.
  - (* rule *)
    destruct (run f (body r) s) as [res0 |] eqn:Hbody; [ | discriminate Hrun ].
    injection Hrun as <-. apply P_rule. exact (IH _ _ _ Hbody).
  - (* sequence *)
    destruct (run f a s) as [[| ts s1] |] eqn:Ha; try discriminate Hrun.
    + injection Hrun as <-. apply P_seq_fail. exact (IH _ _ _ Ha).
    + destruct (run f b s1) as [res1 |] eqn:Hb; [ | discriminate Hrun ].
      injection Hrun as <-. apply P_seq with (s1 := s1).
      * exact (IH _ _ _ Ha).
      * exact (IH _ _ _ Hb).
  - (* choice *)
    destruct (run f a s) as [[| ts s1] |] eqn:Ha; try discriminate Hrun.
    + apply P_alt_right; [ exact (IH _ _ _ Ha) | exact (IH _ _ _ Hrun) ].
    + injection Hrun as <-. apply P_alt_left. exact (IH _ _ _ Ha).
  - (* star *)
    destruct (run f a s) as [[| ts s1] |] eqn:Ha; try discriminate Hrun.
    + injection Hrun as <-. apply P_star_stop. exact (IH _ _ _ Ha).
    + destruct (run f (E_star a) s1) as [[| ts' s2] |] eqn:Hstar; try discriminate Hrun.
      injection Hrun as <-. apply P_star_step with (s1 := s1).
      * exact (IH _ _ _ Ha).
      * exact (IH _ _ _ Hstar).
  - (* plus *)
    apply P_plus. exact (IH _ _ _ Hrun).
  - (* option *)
    destruct (run f a s) as [[| ts s1] |] eqn:Ha; try discriminate Hrun.
    + injection Hrun as <-. apply P_opt_none. exact (IH _ _ _ Ha).
    + injection Hrun as <-. apply P_opt_some. exact (IH _ _ _ Ha).
  - (* expect *)
    apply P_expect. exact (IH _ _ _ Hrun).
Qed.

(* 42 *)
Example number_parses :
  peg (E_rule R_goat) [TNum 42]
      (Ok [Node R_goat [Node R_expr [Node R_number [Leaf (TNum 42)]]]] []).
Proof. apply (run_sound 200). vm_compute. reflexivity. Qed.

(* f = program(y) do y done  f(1) *)
Definition application : list tok :=
  [TName "f"; TSym "="; TSym "program"; TSym "("; TName "y"; TSym ")";
   TSym "do"; TName "y"; TSym "done"; TName "f"; TSym "("; TNum 1; TSym ")"].

Definition application_tree : tree :=
  Node R_goat
    [Node R_expr
       [Node R_declaration
          [Node R_name [Leaf (TName "f")]; Leaf (TSym "=");
           Node R_value
             [Node R_function
                [Leaf (TSym "program"); Leaf (TSym "(");
                 Node R_params [Node R_name [Leaf (TName "y")]];
                 Leaf (TSym ")"); Leaf (TSym "do");
                 Node R_expr [Node R_name [Leaf (TName "y")]];
                 Leaf (TSym "done")]]];
        Node R_name [Leaf (TName "f")];
        Node R_call
          [Leaf (TSym "("); Node R_arguments [Node R_expr [Node R_number [Leaf (TNum 1)]]];
           Leaf (TSym ")")]]].

Example application_parses :
  peg (E_rule R_goat) application (Ok [application_tree] []).
Proof. apply (run_sound 400). vm_compute. reflexivity. Qed.

Lemma application_core : Forall core_tree [application_tree].
Proof.
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Core_leaf
    | (apply Core_node; [ reflexivity | ]) ].
Qed.

Lemma application_complete : Forall Complete [application_tree].
Proof.
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Cp_leaf | apply Cp_node ];
    simpl; try exact I.
  - (* the program has an expression *) eexists. in_list.
  - (* the block does not end in a binding, and has no dot call; its one
       function binding leads *)
    split; [ intros [c Hlast]; simpl in Hlast; discriminate Hlast
         | split; [ exact I | split; [ left; reflexivity | exact I ] ] ].
  - (* the bound value has no dot call and no operator *)
    split; [ exact I | left; reflexivity ].
  - (* the function has parameters and a body *)
    split; eexists; in_list.
  - (* the body is a single name *)
    split; [ intros [c Hlast]; simpl in Hlast; discriminate Hlast
         | split; [ exact I | split; [ left; reflexivity | exact I ] ] ].
  - (* the call has arguments *) eexists. in_list.
  - (* the argument is a single number *)
    split; [ intros [c Hlast]; simpl in Hlast; discriminate Hlast
         | split; [ exact I | split; [ left; reflexivity | exact I ] ] ].
Qed.

(* T1 applies to a concrete program: f = program(y) do y done  f(1). *)
Example application_denotes_lc : forall var_of,
  exists t e,
    [application_tree] = [t] /\ Den_goat var_of t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of.
  exact (parse_denotes_lc var_of application [application_tree] []
           application_parses application_core application_complete).
Qed.

(* A dot call on a variable passes the variable first: x.f(1) is (x.f)(x, 1). *)
Example dot_call_passes_the_receiver : forall var_of x,
  Den_posts var_of ["f"] (e_fvar_f x)
    [Node R_access [sym "."; ident "f"];
     Node R_call [sym "("; Node R_arguments [Node R_expr [Node R_number [Leaf (TNum 1)]]]; sym ")"]]
    (e_app (e_app (e_proj (e_fvar_f x) 0) (e_fvar_f x)) (e_num 1)).
Proof.
  intros var_of x.
  eapply DP_dot_call with (es := [e_num 1]).
  - apply DA_last. apply D_expr. apply DB_chain. apply DM_chain.
    eapply DC_head; [ apply D_num | apply DP_nil ].
  - apply DP_nil.
Qed.

(* A take passes nothing: x::f(1) is (x.f)(1). *)
Example take_calls_without_the_receiver : forall var_of x,
  Den_posts var_of ["f"] (e_fvar_f x)
    [Node R_take [sym "::"; ident "f"];
     Node R_call [sym "("; Node R_arguments [Node R_expr [Node R_number [Leaf (TNum 1)]]]; sym ")"]]
    (e_app (e_proj (e_fvar_f x) 0) (e_num 1)).
Proof.
  intros var_of x.
  apply DP_take.
  eapply DP_call with (es := [e_num 1]).
  - apply DA_last. apply D_expr. apply DB_chain. apply DM_chain.
    eapply DC_head; [ apply D_num | apply DP_nil ].
  - apply DP_nil.
Qed.

(* if 1 < 2 then "s" else 3 + 4 done: a conditional, a string and two operations. *)
Definition conditional_program : list tok :=
  [TSym "if"; TNum 1; TSym "<"; TNum 2; TSym "then"; TStr; TSym "else";
   TNum 3; TSym "+"; TNum 4; TSym "done"].

Definition conditional_tree : tree :=
  Node R_goat
    [Node R_expr
       [Node R_conditional
          [sym "if";
           Node R_expr
             [Node R_number [Leaf (TNum 1)]; Node R_lt [sym "<"];
              Node R_number [Leaf (TNum 2)]];
           sym "then"; Node R_expr [Node R_string [Leaf TStr]]; sym "else";
           Node R_expr
             [Node R_number [Leaf (TNum 3)]; Node R_plus [sym "+"];
              Node R_number [Leaf (TNum 4)]];
           sym "done"]]].

Example conditional_parses :
  peg (E_rule R_goat) conditional_program (Ok [conditional_tree] []).
Proof. apply (run_sound 600). vm_compute. reflexivity. Qed.

Lemma conditional_core : Forall core_tree [conditional_tree].
Proof.
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Core_leaf
    | (apply Core_node; [ reflexivity | ]) ].
Qed.

Lemma conditional_complete : Forall Complete [conditional_tree].
Proof.
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Cp_leaf | apply Cp_node ];
    simpl; try exact I.
  all: first
    [ solve [ eexists; in_list ]
    | solve [ split; [ intros [c Hlast]; simpl in Hlast; discriminate Hlast
                     | split; [ exact I | split;
                                  [ first [ left; reflexivity
                                          | (right; split; [ reflexivity | exact I ]) ]
                                  | exact I ] ] ] ]
    | solve [ in_list ] ].
Qed.

(* T1 applies to the conditional program. *)
Example conditional_denotes_lc : forall var_of,
  exists t e,
    [conditional_tree] = [t] /\ Den_goat var_of t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of.
  exact (parse_denotes_lc var_of conditional_program [conditional_tree] []
           conditional_parses conditional_core conditional_complete).
Qed.

(* The operation denotes the term with the operator the tree names. *)
Example operation_denotes_its_operator : forall var_of tbl,
  Den_math var_of tbl
    [Node R_number [Leaf (TNum 3)]; Node R_plus [sym "+"]; Node R_number [Leaf (TNum 4)]]
    (e_bin (e_num 3) bop_add (e_num 4)).
Proof.
  intros var_of tbl.
  apply (DM_bin var_of tbl [Node R_number [Leaf (TNum 3)]]
           [Node R_number [Leaf (TNum 4)]] bop_add (e_num 3) (e_num 4));
    (eapply DC_head; [ apply D_num | apply DP_nil ]).
Qed.

(* ---- a recursive group (ADR 0003, ADR 0037 phase 2) ---- *)

(* countdown = program(n) do if n < 1 then 0 else countdown(n - 1) done done
   countdown(2): the function binding leading the block is a one-member group,
   so the program denotes the recursive group of GoatPhase2.v, whose typing and
   unrolling are proved there. *)
Definition countdown_program : list tok :=
  [TName "countdown"; TSym "="; TSym "program"; TSym "("; TName "n"; TSym ")";
   TSym "do"; TSym "if"; TName "n"; TSym "<"; TNum 1; TSym "then"; TNum 0;
   TSym "else"; TName "countdown"; TSym "("; TName "n"; TSym "-"; TNum 1; TSym ")";
   TSym "done"; TSym "done"; TName "countdown"; TSym "("; TNum 2; TSym ")"].

Definition countdown_body : list tree :=
  [Node R_conditional
     [sym "if";
      Node R_expr [ident "n"; Node R_lt [sym "<"]; Node R_number [Leaf (TNum 1)]];
      sym "then"; Node R_expr [Node R_number [Leaf (TNum 0)]]; sym "else";
      Node R_expr
        [ident "countdown";
         Node R_call
           [sym "("; Node R_arguments
              [Node R_expr [ident "n"; Node R_minus [sym "-"]; Node R_number [Leaf (TNum 1)]]];
            sym ")"]];
      sym "done"]].

Definition countdown_decl : tree :=
  Node R_declaration
    [ident "countdown"; sym "=";
     Node R_value
       [Node R_function
          [sym "program"; sym "("; Node R_params [ident "n"]; sym ")"; sym "do";
           Node R_expr countdown_body; sym "done"]]].

Definition countdown_rest : list tree :=
  [ident "countdown";
   Node R_call [sym "("; Node R_arguments [Node R_expr [Node R_number [Leaf (TNum 2)]]]; sym ")"]].

Definition countdown_tree : tree :=
  Node R_goat [Node R_expr (countdown_decl :: countdown_rest)].

Example countdown_parses :
  peg (E_rule R_goat) countdown_program (Ok [countdown_tree] []).
Proof. apply (run_sound 1200). vm_compute. reflexivity. Qed.

Lemma countdown_core : Forall core_tree [countdown_tree].
Proof.
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Core_leaf
    | (apply Core_node; [ reflexivity | ]) ].
Qed.

Lemma countdown_complete : Forall Complete [countdown_tree].
Proof.
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Cp_leaf | apply Cp_node ];
    simpl; try exact I.
  all: first
    [ solve [ eexists; in_list ]
    | solve [ split; [ intros [c Hlast]; simpl in Hlast; discriminate Hlast
                     | split; [ exact I | split;
                                  [ first [ left; reflexivity
                                          | (right; split; [ reflexivity | exact I ]) ]
                                  | exact I ] ] ] ]
    | solve [ split; [ exact I | left; reflexivity ] ]
    | solve [ split; eexists; in_list ]
    | solve [ in_list ] ].
Qed.

Example countdown_denotes_lc : forall var_of,
  exists t e,
    [countdown_tree] = [t] /\ Den_goat var_of t e /\ lc_exp e /\ lc e.
Proof.
  intros var_of.
  exact (parse_denotes_lc var_of countdown_program [countdown_tree] []
           countdown_parses countdown_core countdown_complete).
Qed.

Section CountdownDenotation.

  Variable var_of : string -> termvar.
  Hypothesis Hne : var_of "n" <> var_of "countdown".
  Let n := var_of "n".
  Let c := var_of "countdown".

  Let chain1 (t : tree) (e : exp) (H : Den var_of [] t e) : Den_chain var_of [] [t] e :=
    DC_head var_of [] t [] e e H (DP_nil var_of [] e).

  Let expr_of (cs : list tree) (e : exp) (H : Den_math var_of [] cs e) :
    Den var_of [] (Node R_expr cs) e :=
    D_expr var_of [] cs e (DB_chain var_of [] cs e H).

  Let expr_of_block (cs : list tree) (e : exp) (H : Den_block var_of [] cs e) :
    Den var_of [] (Node R_expr cs) e := D_expr var_of [] cs e H.

  Let name_of (x : string) : Den var_of [] (ident x) (e_fvar_f (var_of x)) := D_name var_of [] x.

  Let number_of (k : nat) : Den var_of [] (Node R_number [Leaf (TNum k)]) (e_num (z_of_nat k)) :=
    D_num var_of [] k.

  Let inner : exp :=
    e_ite (e_bin (e_fvar_f n) bop_lt (e_num 1)) (e_num 0)
          (e_app (e_fvar_f c) (e_bin (e_fvar_f n) bop_sub (e_num 1))).

  Lemma countdown_inner : Den var_of [] (Node R_expr countdown_body) inner.
  Proof.
    unfold countdown_body, inner.
    apply expr_of. apply DM_chain. apply chain1.
    apply (D_cond var_of [] _ _ _ (e_bin (e_fvar_f n) bop_lt (e_num 1)) (e_num 0)
             (e_app (e_fvar_f c) (e_bin (e_fvar_f n) bop_sub (e_num 1)))).
    - apply expr_of.
      apply (DM_bin var_of [] [ident "n"] [Node R_number [Leaf (TNum 1)]] bop_lt
               (e_fvar_f n) (e_num 1));
        apply chain1; [ apply name_of | apply (number_of 1) ].
    - apply expr_of. apply DM_chain. apply chain1. apply (number_of 0).
    - apply expr_of. apply DM_chain.
      eapply DC_head; [ apply name_of | ].
      eapply DP_call with (es := [e_bin (e_fvar_f n) bop_sub (e_num 1)]);
        [ | apply DP_nil ].
      apply DA_last. apply expr_of.
      apply (DM_bin var_of [] [ident "n"] [Node R_number [Leaf (TNum 1)]] bop_sub
               (e_fvar_f n) (e_num 1));
        apply chain1; [ apply name_of | apply (number_of 1) ].
  Qed.

  Lemma countdown_member_den :
    Den_decl var_of [] countdown_decl "countdown" (curry [n] inner).
  Proof.
    unfold countdown_decl. apply DD_plain. apply D_value. apply DM_chain. apply chain1.
    apply (D_function var_of [] (TSym "program") [ident "n"] ["n"] countdown_body inner).
    - apply DPa_one.
    - exact countdown_inner.
  Qed.

  Lemma countdown_group_den :
    Den var_of [] (Node R_expr (countdown_decl :: countdown_rest))
      (e_letrec (group_fields [c] [curry [n] inner])
                (bind_group [c] (e_app (e_fvar_f c) (e_num 2)))).
  Proof.
    apply expr_of_block.
    change (countdown_decl :: countdown_rest) with ([countdown_decl] ++ countdown_rest).
    apply (DB_group var_of [] [countdown_decl] ["countdown"] [curry [n] inner]
             countdown_rest (e_app (e_fvar_f c) (e_num 2))).
    - apply DDs_cons with (x := "countdown") (v := curry [n] inner).
      + exact countdown_member_den.
      + reflexivity.
      + apply DDs_nil.
    - discriminate.
    - unfold countdown_rest. apply DB_chain. apply DM_chain.
      eapply DC_head; [ apply name_of | ].
      eapply DP_call with (es := [e_num 2]); [ | apply DP_nil ].
      apply DA_last. apply expr_of. apply DM_chain. apply chain1. apply (number_of 2).
  Qed.

  Lemma countdown_group_is_the_phase_2_term :
    e_letrec (group_fields [c] [curry [n] inner])
             (bind_group [c] (e_app (e_fvar_f c) (e_num 2))) = countdown.
  Proof.
    unfold countdown, countdown_member, inner, group_fields, group_fields_from, bind_group.
    unfold n, c in *. simpl.
    repeat match goal with |- context [ ?a == ?b ] => destruct (a == b) end;
      simpl.
    all: first
      [ congruence | reflexivity
      | (destruct (var_of "countdown" == var_of "countdown") as [_ | Hx];
         [ simpl; reflexivity | exfalso; apply Hx; reflexivity ]) ].
  Qed.

End CountdownDenotation.

Example countdown_denotes_the_group : forall var_of,
  var_of "n" <> var_of "countdown" ->
  Den_goat var_of countdown_tree countdown.
Proof.
  intros var_of Hne. unfold Den_goat.
  exists (countdown_decl :: countdown_rest). split; [ reflexivity | ].
  assert (Hlabels : labels countdown_tree = []) by (vm_compute; reflexivity).
  rewrite Hlabels.
  rewrite <- (countdown_group_is_the_phase_2_term var_of Hne).
  exact (countdown_group_den var_of).
Qed.

(* The program that parses is the term GoatPhase2.v types as an Int. *)
Example countdown_source_types : forall var_of,
  var_of "n" <> var_of "countdown" ->
  Den_goat var_of countdown_tree countdown /\ typing d_any nil countdown typ_Int.
Proof.
  intros var_of Hne.
  exact (conj (countdown_denotes_the_group var_of Hne) recursive_group_types).
Qed.
