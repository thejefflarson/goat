(* The printer of the core fragment (ADR 0030, T3): a closed core term to the
   token stream, mirroring the printer in checker/tests/core_roundtrip.rs (the
   curried style). It is defined through the parse tree it should produce, so
   the token stream is the tree's leaves.

   Names: the binder introduced at depth [P] (P enclosing binders) is [nm P];
   a bound index [i] at depth [P] prints as [nm (P - 1 - i)]; the label [n]
   prints as [lname n]. *)

From Stdlib Require Import String List Decimal DecimalString.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Export Goat.GoatLit.
Require Import Goat.GoatNum.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatParse.
Open Scope string_scope.
Open Scope list_scope.

Definition digits (n : nat) : string := NilZero.string_of_uint (Nat.to_uint n).
Definition nm (d : nat) : string := "v" ++ digits d.
Definition lname (n : nat) : string := "lab" ++ digits n.

(* ---- the printer, as a parse tree ---- *)

Definition paren_kids (b : list tree) : list tree := [sym "("; Node R_expr b; sym ")"].

(* A callee or a base is parenthesised when it is a binding (which would take
   the rest of the text as its scope), a number (which would read a following
   "." as a decimal point) or an operation (which would take the call or the
   field as the operand of its own right-hand side). *)
Definition as_operand (e : exp) (b : list tree) : list tree :=
  match e with
  | e_let _ _ | e_num _ | e_bin _ _ _ => paren_kids b
  | _ => b
  end.

(* An operand of an operator is a chain, so a binding or another operation is
   parenthesised: a run of operators is flat and its precedence is not part of
   the fragment. *)
Definition as_binop (e : exp) (b : list tree) : list tree :=
  match e with
  | e_let _ _ | e_bin _ _ _ => paren_kids b
  | _ => b
  end.

(* A projection callee is also parenthesised: [r.f(x)] is a dot call, which
   passes [r] first. *)
Definition as_callee (e : exp) (b : list tree) : list tree :=
  match e with
  | e_proj _ _ => paren_kids b
  | _ => as_operand e b
  end.

(* A binding's value is one operand: a nested binding is parenthesised. *)
Definition as_value (e : exp) (b : list tree) : list tree :=
  match e with
  | e_let _ _ => paren_kids b
  | _ => b
  end.

Definition decl_tree (P : nat) (v : list tree) : tree :=
  Node R_declaration [ident (nm P); sym "="; Node R_value v; sym ";"].

Definition call_tree (b : list tree) : tree :=
  Node R_call [sym "("; Node R_arguments [Node R_expr b]; sym ")"].

Definition access_tree (l : label) : tree := Node R_access [sym "."; ident (lname l)].

Definition field_tree (l : label) (b : list tree) : tree :=
  Node R_field [ident (lname l); sym ":"; Node R_expr b].

Definition cond_tree (c t e : list tree) : tree :=
  Node R_conditional [sym "if"; Node R_expr c; sym "then"; Node R_expr t;
                      sym "else"; Node R_expr e; sym "done"].

Definition function_tree (P : nat) (b : list tree) : tree :=
  Node R_function [sym "program"; sym "("; Node R_params [ident (nm P)];
                   sym ")"; sym "do"; Node R_expr b; sym "done"].

(* [block P e]: the children of the expression node holding [e] at depth [P].
   [field_trees P fs]: a record's fields, each after the first behind a comma. *)
Fixpoint block (P : nat) (e : exp) {struct e} : list tree :=
  match e with
  | e_fvar_b i => [ident (nm (P - 1 - i))]
  | e_fvar_f _ => []
  | e_num n => [Node R_number [Leaf (TNum (nat_of_z n))]]
  | e_dec _ => []
  | e_true => [Node R_boolean [Node R_true_lit [sym "true"]]]
  | e_false => [Node R_boolean [Node R_false_lit [sym "false"]]]
  | e_abs b => [function_tree P (block (S P) b)]
  | e_app f a => as_callee f (block P f) ++ [call_tree (block P a)]
  | e_let v b => decl_tree P (as_value v (block P v)) :: block (S P) b
  | e_rec fs => [Node R_record ((sym "{" :: field_trees P fs) ++ [sym "}"])]
  | e_proj f l => as_operand f (block P f) ++ [access_tree l]
  | e_unit | e_tofloat _ => []
  | e_str _ => [Node R_string [Leaf TStr]]
  | e_ite c a b => [cond_tree (block P c) (block P a) (block P b)]
  | e_bin a o b => as_binop a (block P a) ++ op_tree o :: as_binop b (block P b)
  end
with field_trees (P : nat) (fs : Goat_ott.fields) {struct fs} : list tree :=
  match fs with
  | fs_nil => []
  | fs_cons l e rest => field_tree l (block P e) :: more_field_trees P rest
  end
with more_field_trees (P : nat) (fs : Goat_ott.fields) {struct fs} : list tree :=
  match fs with
  | fs_nil => []
  | fs_cons l e rest => sym "," :: field_tree l (block P e) :: more_field_trees P rest
  end.

Fixpoint flat (t : tree) : list tok :=
  match t with
  | Leaf k => [k]
  | Node _ cs => (fix go (l : list tree) : list tok :=
                    match l with
                    | [] => []
                    | c :: l' => flat c ++ go l'
                    end) cs
  end.

Definition flats (ts : list tree) : list tok := flat_map flat ts.

Lemma flat_node : forall r cs, flat (Node r cs) = flats cs.
Proof.
  intros r cs. unfold flats. induction cs as [| c cs IH]; [ reflexivity | ].
  simpl. rewrite <- IH. reflexivity.
Qed.

Lemma flat_leaf : forall k, flat (Leaf k) = [k].
Proof. reflexivity. Qed.

Arguments flat : simpl never.

Lemma flats_app : forall a b, flats (a ++ b) = flats a ++ flats b.
Proof. intros a b. unfold flats. apply flat_map_app. Qed.

Lemma flats_nil : flats [] = [].
Proof. reflexivity. Qed.

Lemma flats_cons : forall t ts, flats (t :: ts) = flat t ++ flats ts.
Proof. reflexivity. Qed.

Arguments flats : simpl never.

(* Unfold the tokens of a tree built from literal nodes, leaving the tokens of a
   variable subtree as [flats b]. *)
Ltac flat_simp :=
  (try unfold ident, sym);
  repeat (progress rewrite ?flat_node, ?flat_leaf, ?flats_nil, ?flats_cons, ?flats_app);
  cbn [app];
  (try rewrite !List.app_nil_l); (try rewrite !List.app_nil_r);
  repeat rewrite <- List.app_assoc.

Definition print_tree (e : exp) : tree := Node R_goat [Node R_expr (block 0 e)].

Definition print (e : exp) : list tok := flats (block 0 e).

(* ---- what the printer is defined on, and what it needs ---- *)

(* A closed term whose bound indices are below [n]. *)
Fixpoint scoped (n : nat) (e : exp) {struct e} : Prop :=
  match e with
  | e_fvar_b i => i < n
  | e_fvar_f _ => False
  | e_num z => z_nonneg z = true
  | e_true | e_false | e_str _ => True
  | e_dec _ | e_unit | e_tofloat _ => False
  | e_ite c a b => scoped n c /\ scoped n a /\ scoped n b
  | e_bin a _ b => scoped n a /\ scoped n b
  | e_abs b => scoped (S n) b
  | e_app f a => scoped n f /\ scoped n a
  | e_let v b => scoped n v /\ scoped (S n) b
  | e_rec fs => scoped_fields n fs
  | e_proj f _ => scoped n f
  end
with scoped_fields (n : nat) (fs : Goat_ott.fields) {struct fs} : Prop :=
  match fs with
  | fs_nil => True
  | fs_cons _ e rest => scoped n e /\ scoped_fields n rest
  end.

(* Labels in the order the printer writes them. *)
Fixpoint lbls (e : exp) {struct e} : list nat :=
  match e with
  | e_abs b => lbls b
  | e_app f a => lbls f ++ lbls a
  | e_let v b => lbls v ++ lbls b
  | e_rec fs => lbls_fields fs
  | e_proj f l => lbls f ++ [l]
  | e_ite c a b => lbls c ++ lbls a ++ lbls b
  | e_bin a _ b => lbls a ++ lbls b
  | _ => []
  end
with lbls_fields (fs : Goat_ott.fields) {struct fs} : list nat :=
  match fs with
  | fs_nil => []
  | fs_cons l e rest => l :: lbls e ++ lbls_fields rest
  end.

(* The labels are already numbered as parsing numbers them: by first
   occurrence in the printed text. *)
Definition Interned (e : exp) : Prop :=
  forall n, List.In n (lbls e) ->
    index_of (lname n) (nub_from [] (List.map lname (lbls e))) = n.

(* The variables the parser reads as [nm 0], [nm 1], ... stand for distinct
   atoms. *)
Definition names_distinct (var_of : string -> termvar) : Prop :=
  forall m n, var_of (nm m) = var_of (nm n) -> m = n.
