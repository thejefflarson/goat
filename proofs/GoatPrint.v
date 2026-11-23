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

Lemma nm_not_foreign : forall d, nm d <> "foreign".
Proof. intros d H. unfold nm in H. discriminate H. Qed.

(* Member [i] of the recursive group bound at depth [d]. *)
Definition gm (d i : nat) : string := "g" ++ digits d ++ "_" ++ digits i.

Lemma gm_not_foreign : forall d i, gm d i <> "foreign".
Proof. intros d i H. unfold gm in H. discriminate H. Qed.

(* The recursive groups in scope: the depth of each group's binder and its
   number of members. *)
Definition Grp := list (nat * nat).

Fixpoint grp_size (G : Grp) (L : nat) : option nat :=
  match G with
  | [] => None
  | (l, n) :: rest => if Nat.eqb l L then Some n else grp_size rest L
  end.

Fixpoint flen (fs : Goat_ott.fields) : nat :=
  match fs with
  | fs_nil => 0
  | fs_cons _ _ rest => S (flen rest)
  | fs_meth _ _ rest => S (flen rest)
  end.

(* The depth of the group a projection's base is the binder of, if it is one. *)
Definition proj_level (G : Grp) (P : nat) (f : exp) : option nat :=
  match f with
  | e_fvar_b i => match grp_size G (P - 1 - i) with Some _ => Some (P - 1 - i) | None => None end
  | _ => None
  end.

Definition is_abs (e : exp) : Prop :=
  match e with e_abs _ => True | _ => False end.

(* ---- the printer, as a parse tree ---- *)

Definition paren_kids (b : list tree) : list tree := [sym "("; Node R_expr b; sym ")"].

(* A callee or a base is parenthesised when it is a binding (which would take
   the rest of the text as its scope), a number (which would read a following
   "." as a decimal point) or an operation (which would take the call or the
   field as the operand of its own right-hand side). *)
Definition as_operand (e : exp) (b : list tree) : list tree :=
  match e with
  | e_let _ _ | e_letrec _ _ | e_num _ | e_dec _ | e_bin _ _ _ => paren_kids b
  | _ => b
  end.

(* An operand of an operator is a chain, so a binding or another operation is
   parenthesised: a run of operators is flat and its precedence is not part of
   the fragment. *)
Definition as_binop (e : exp) (b : list tree) : list tree :=
  match e with
  | e_let _ _ | e_letrec _ _ | e_bin _ _ _ => paren_kids b
  | _ => b
  end.

(* A projection callee is also parenthesised: [r.f(x)] is a dot call, which
   passes [r] first. *)
Definition as_callee (e : exp) (b : list tree) : list tree :=
  match e with
  | e_proj _ _ => paren_kids b
  | _ => as_operand e b
  end.

(* A binding's value is one operand: a nested binding is parenthesised, and so
   is a function, because a binding whose value is a bare function literal is a
   member of the block's recursive group (ADR 0003) rather than a plain let. *)
Definition as_value (e : exp) (b : list tree) : list tree :=
  match e with
  | e_let _ _ | e_letrec _ _ | e_abs _ => paren_kids b
  | _ => b
  end.

Definition decl_named (x : string) (v : list tree) : tree :=
  Node R_declaration [ident x; sym "="; Node R_value v; sym ";"].

Definition decl_tree (P : nat) (v : list tree) : tree := decl_named (nm P) v.

Definition call_tree (b : list tree) : tree :=
  Node R_call [sym "("; Node R_arguments [Node R_expr b]; sym ")"].

Definition call_unit_tree : tree := Node R_call [sym "("; sym ")"].

Definition access_tree (l : label) : tree := Node R_access [sym "."; ident (lname l)].

Definition field_tree (l : label) (b : list tree) : tree :=
  Node R_field [ident (lname l); sym ":"; Node R_expr b].

(* The base of a spread is parenthesised: a bare name there would read as the
   rest binding of a record pattern. *)
Definition spread_tree (b : list tree) : tree :=
  Node R_spread [sym "..."; Node R_expr (paren_kids b)].

Definition cond_tree (c t e : list tree) : tree :=
  Node R_conditional [sym "if"; Node R_expr c; sym "then"; Node R_expr t;
                      sym "else"; Node R_expr e; sym "done"].

Definition cond_tree_noelse (c t : list tree) : tree :=
  Node R_conditional [sym "if"; Node R_expr c; sym "then"; Node R_expr t; sym "done"].

Definition function_tree (P : nat) (b : list tree) : tree :=
  Node R_function [sym "program"; sym "("; Node R_params [ident (nm P)];
                   sym ")"; sym "do"; Node R_expr b; sym "done"].

Definition function_empty_tree (P : nat) : tree :=
  Node R_function [sym "program"; sym "("; Node R_params [ident (nm P)];
                   sym ")"; sym "do"; sym "done"].

(* [block G P e]: the children of the expression node holding [e] at depth [P].
   [G] lists the recursive groups in scope, each as the depth of its binder and
   its number of members: a projection of member [l] from the group bound at
   depth [L] is the name [gm L l] (ADR 0003), and the group's members are the
   function bindings that open the block holding the group.
   [field_trees G P fs]: a record's fields, each after the first behind a comma.
   [member_trees G P i fs]: a group's member bindings, from member [i]. *)
Fixpoint block (G : Grp) (P : nat) (e : exp) {struct e} : list tree :=
  match e with
  | e_fvar_b i => [ident (nm (P - 1 - i))]
  | e_fvar_f _ => []
  | e_num n => [Node R_number [Leaf (TNum (nat_of_z n))]]
  | e_dec d => [Node R_number [Leaf (TDec d)]]
  | e_true => [Node R_boolean [Node R_true_lit [sym "true"]]]
  | e_false => [Node R_boolean [Node R_false_lit [sym "false"]]]
  | e_abs e_unit => [function_empty_tree P]
  | e_abs b => [function_tree P (block G (S P) b)]
  | e_app f e_unit => as_callee f (block G P f) ++ [call_unit_tree]
  | e_app f a => as_callee f (block G P f) ++ [call_tree (block G P a)]
  | e_let v b => decl_tree P (as_value v (block G P v)) :: block G (S P) b
  | e_rec fs => [Node R_record ((sym "{" :: field_trees G P fs) ++ [sym "}"])]
  | e_proj f l =>
      match proj_level G P f with
      | Some L => [ident (gm L l)]
      | None => as_operand f (block G P f) ++ [access_tree l]
      end
  | e_spread a l b =>
      [Node R_record [sym "{"; spread_tree (block G P a); sym ",";
                      field_tree l (block G P b); sym "}"]]
  | e_unit | e_tofloat _ | e_con _ _ _ | e_match _ _ _ | e_fold _ | e_unfold _
  | e_restrict _ _ => []
  | e_letrec fs b =>
      member_trees ((P, flen fs) :: G) P 0 fs ++ block ((P, flen fs) :: G) (S P) b
  | e_str _ => [Node R_string [Leaf TStr]]
  | e_ite c a e_unit => [cond_tree_noelse (block G P c) (block G P a)]
  | e_ite c a b => [cond_tree (block G P c) (block G P a) (block G P b)]
  | e_bin a o b => as_binop a (block G P a) ++ op_tree o :: as_binop b (block G P b)
  end
with field_trees (G : Grp) (P : nat) (fs : Goat_ott.fields) {struct fs} : list tree :=
  match fs with
  | fs_nil => []
  | fs_cons l e rest => field_tree l (block G P e) :: more_field_trees G P rest
  | fs_meth l e rest => field_tree l (block G P e) :: more_field_trees G P rest
  end
with more_field_trees (G : Grp) (P : nat) (fs : Goat_ott.fields) {struct fs} : list tree :=
  match fs with
  | fs_nil => []
  | fs_cons l e rest => sym "," :: field_tree l (block G P e) :: more_field_trees G P rest
  | fs_meth l e rest => sym "," :: field_tree l (block G P e) :: more_field_trees G P rest
  end
with member_trees (G : Grp) (P i : nat) (fs : Goat_ott.fields) {struct fs} : list tree :=
  match fs with
  | fs_nil => []
  | fs_cons _ v rest => decl_named (gm P i) (block G (S P) v) :: member_trees G P (S i) rest
  | fs_meth _ v rest => decl_named (gm P i) (block G (S P) v) :: member_trees G P (S i) rest
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

Definition print_tree (e : exp) : tree := Node R_goat [Node R_expr (block [] 0 e)].

Definition print (e : exp) : list tok := flats (block [] 0 e).

(* ---- what the printer is defined on, and what it needs ---- *)

(* A term that is not a recursive group: a group is first in its block, so
   nothing that continues a block (the body of a binding or of a group) can be
   one, or the group's members would join the earlier group. *)
Definition NonRec (e : exp) : Prop :=
  match e with e_letrec _ _ => False | _ => True end.

(* A closed term whose bound indices are below [n], among them the groups of
   [G]. A group's binder is used only to project a member, and a group is a
   nonempty run of one-parameter functions labelled by position. *)
Fixpoint scoped (G : Grp) (n : nat) (e : exp) {struct e} : Prop :=
  match e with
  | e_fvar_b i => i < n /\ grp_size G (n - 1 - i) = None
  | e_fvar_f _ => False
  | e_num z => z_nonneg z = true
  | e_true | e_false | e_str _ | e_dec _ => True
  | e_unit | e_tofloat _ | e_con _ _ _ | e_match _ _ _ | e_fold _ | e_unfold _
  | e_restrict _ _ => False
  | e_letrec fs b =>
      0 < flen fs /\ scoped_group ((n, flen fs) :: G) (S n) 0 fs /\
      scoped ((n, flen fs) :: G) (S n) b /\ NonRec b
  | e_spread a _ b => scoped G n a /\ scoped G n b
  | e_ite c a b => scoped G n c /\ scoped G n a /\ (b = e_unit \/ scoped G n b)
  | e_bin a _ b => scoped G n a /\ scoped G n b
  | e_abs b => b = e_unit \/ scoped G (S n) b
  | e_app f a => scoped G n f /\ (a = e_unit \/ scoped G n a)
  | e_let v b => scoped G n v /\ scoped G (S n) b /\ NonRec b
  | e_rec fs => scoped_fields G n fs
  | e_proj f l =>
      match f with
      | e_fvar_b i => i < n /\ forall m, grp_size G (n - 1 - i) = Some m -> l < m
      | _ => scoped G n f
      end
  end
with scoped_fields (G : Grp) (n : nat) (fs : Goat_ott.fields) {struct fs} : Prop :=
  match fs with
  | fs_nil => True
  | fs_cons _ e rest => scoped G n e /\ scoped_fields G n rest
  | fs_meth _ _ _ => False
  end
with scoped_group (G : Grp) (n i : nat) (fs : Goat_ott.fields) {struct fs} : Prop :=
  match fs with
  | fs_nil => True
  | fs_cons l v rest => l = i /\ is_abs v /\ scoped G n v /\ scoped_group G n (S i) rest
  | fs_meth _ _ _ => False
  end.

Lemma block_ite_else : forall G P c a b,
  scoped G P b -> block G P (e_ite c a b) = [cond_tree (block G P c) (block G P a) (block G P b)].
Proof. intros G P c a b H. destruct b; try reflexivity; destruct H. Qed.

Lemma block_ite_cases : forall G P c a b,
  (b = e_unit /\ block G P (e_ite c a b) = [cond_tree_noelse (block G P c) (block G P a)])
  \/ (b <> e_unit /\ block G P (e_ite c a b) = [cond_tree (block G P c) (block G P a) (block G P b)]).
Proof.
  intros G P c a b. destruct b;
    first [ (left; split; reflexivity) | (right; split; [ discriminate | reflexivity ]) ].
Qed.

Lemma block_abs_cases : forall G P b,
  (b = e_unit /\ block G P (e_abs b) = [function_empty_tree P])
  \/ (b <> e_unit /\ block G P (e_abs b) = [function_tree P (block G (S P) b)]).
Proof.
  intros G P b. destruct b;
    first [ (left; split; reflexivity) | (right; split; [ discriminate | reflexivity ]) ].
Qed.

Lemma block_app_cases : forall G P f a,
  (a = e_unit /\ block G P (e_app f a) = as_callee f (block G P f) ++ [call_unit_tree])
  \/ (a <> e_unit /\
      block G P (e_app f a) = as_callee f (block G P f) ++ [call_tree (block G P a)]).
Proof.
  intros G P f a. destruct a;
    first [ (left; split; reflexivity) | (right; split; [ discriminate | reflexivity ]) ].
Qed.

Lemma block_ite_unit : forall G P c a,
  block G P (e_ite c a e_unit) = [cond_tree_noelse (block G P c) (block G P a)].
Proof. reflexivity. Qed.

Lemma block_proj_group : forall G P f l L,
  proj_level G P f = Some L -> block G P (e_proj f l) = [ident (gm L l)].
Proof. intros G P f l L H. cbn [block]. rewrite H. reflexivity. Qed.

Lemma block_proj_plain : forall G P f l,
  proj_level G P f = None ->
  block G P (e_proj f l) = as_operand f (block G P f) ++ [access_tree l].
Proof. intros G P f l H. cbn [block]. rewrite H. reflexivity. Qed.

(* Labels in the order the printer writes them; a group's member is not a label
   in the text. *)
Fixpoint lbls (G : Grp) (P : nat) (e : exp) {struct e} : list nat :=
  match e with
  | e_abs b => lbls G (S P) b
  | e_app f a => lbls G P f ++ lbls G P a
  | e_let v b => lbls G P v ++ lbls G (S P) b
  | e_rec fs => lbls_fields G P fs
  | e_proj f l =>
      match proj_level G P f with
      | Some _ => []
      | None => lbls G P f ++ [l]
      end
  | e_spread a l b => lbls G P a ++ l :: lbls G P b
  | e_ite c a b => lbls G P c ++ lbls G P a ++ lbls G P b
  | e_bin a _ b => lbls G P a ++ lbls G P b
  | e_letrec fs b =>
      lbls_members ((P, flen fs) :: G) P fs ++ lbls ((P, flen fs) :: G) (S P) b
  | _ => []
  end
with lbls_fields (G : Grp) (P : nat) (fs : Goat_ott.fields) {struct fs} : list nat :=
  match fs with
  | fs_nil => []
  | fs_cons l e rest => l :: lbls G P e ++ lbls_fields G P rest
  | fs_meth l e rest => l :: lbls G P e ++ lbls_fields G P rest
  end
with lbls_members (G : Grp) (P : nat) (fs : Goat_ott.fields) {struct fs} : list nat :=
  match fs with
  | fs_nil => []
  | fs_cons _ e rest => lbls G (S P) e ++ lbls_members G P rest
  | fs_meth _ e rest => lbls G (S P) e ++ lbls_members G P rest
  end.

(* The labels are already numbered as parsing numbers them: by first
   occurrence in the printed text. *)
Definition Interned (e : exp) : Prop :=
  forall n, List.In n (lbls [] 0 e) ->
    index_of (lname n) (nub_from [] (List.map lname (lbls [] 0 e))) = n.

(* The variables the parser reads as [nm 0], [nm 1], ... and as the members of
   the groups stand for distinct atoms. *)
Definition names_distinct (var_of : string -> termvar) : Prop :=
  (forall m n, var_of (nm m) = var_of (nm n) -> m = n) /\
  (forall d i e j, var_of (gm d i) = var_of (gm e j) -> d = e /\ i = j) /\
  (forall m d i, var_of (nm m) <> var_of (gm d i)).
