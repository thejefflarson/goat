(* Evidence that the hypotheses of T1 are satisfiable: a fuel-bounded
   interpreter of the PEG relation, sound for it, parses two small programs, and
   the trees it builds are in the core fragment. *)

From Coq Require Import String List.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatMeta.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatShape.
Require Import Goat.GoatParse.
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
  - (* the block does not end in a binding, and has no dot call *)
    split; [ intros [c Hlast]; simpl in Hlast; discriminate Hlast | exact I ].
  - (* the function has parameters and a body *)
    split; eexists; in_list.
  - (* the body is a single name *)
    split; [ intros [c Hlast]; simpl in Hlast; discriminate Hlast | exact I ].
  - (* the call has arguments *) eexists. in_list.
  - (* the argument is a single number *)
    split; [ intros [c Hlast]; simpl in Hlast; discriminate Hlast | exact I ].
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
  - apply DA_last. apply D_expr. apply DB_chain.
    eapply DC_head; [ apply D_num | apply DP_nil ].
  - apply DP_nil.
Qed.
