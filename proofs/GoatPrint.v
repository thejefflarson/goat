(* The printer of the core fragment (ADR 0030, T3): a closed core term to the
   token stream, mirroring the printer in checker/tests/core_roundtrip.rs (the
   curried style). It is defined through the parse tree it should produce, so
   the token stream is the tree's leaves.

   Names: the binder introduced at depth [P] (P enclosing binders) is [nm P];
   a bound index [i] at depth [P] prints as [nm (P - 1 - i)]; the label [n]
   prints as [lname n]. *)

From Stdlib Require Import String Ascii List Decimal DecimalString.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
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

(* ---- tag declarations ---- *)

(* A group's name as the text the declaration spells. *)
Definition gname (w : gdecl) : string :=
  string_of_list_ascii (List.map Ascii.ascii_of_nat (fst w)).

Fixpoint ticks (n : nat) : string :=
  match n with
  | 0 => ""
  | S n' => String "i" (ticks n')
  end.

(* The name of tag [tg] of the group [w]: the position as that many ticks, then
   the group's name, so both are recovered from the name, and groups of
   different names share no tag name. *)
Definition cn (w : gdecl) (tg : nat) : string := "k" ++ ticks tg ++ "_" ++ gname w.

Lemma ticks_split : forall (a b : nat) (g h : string),
  (ticks a ++ "_" ++ g)%string = (ticks b ++ "_" ++ h)%string -> a = b /\ g = h.
Proof.
  induction a as [| a IH]; intros [| b] g h H; cbn [ticks append] in H.
  - split; [ reflexivity | injection H as H; exact H ].
  - discriminate H.
  - discriminate H.
  - injection H as H. destruct (IH b g h H) as [-> ->]. split; reflexivity.
Qed.

Lemma cn_inj : forall w tg w' tg', cn w tg = cn w' tg' -> tg = tg' /\ gname w = gname w'.
Proof.
  intros w tg w' tg' H. unfold cn in H. cbn [append] in H. injection H as H.
  exact (ticks_split _ _ _ _ H).
Qed.

Lemma cn_not_foreign : forall w tg, cn w tg <> "foreign".
Proof. intros w tg H. unfold cn in H. discriminate H. Qed.

Definition slot_name (w : gdecl) (c : nat) : option string :=
  match c with
  | 0 => Some (gname w)
  | 1 => Some "Int"
  | 2 => Some "Number"
  | 3 => Some "Bool"
  | 4 => Some "Unit"
  | 5 => Some "String"
  | _ => None
  end.

Definition slot_tree (w : gdecl) (c : nat) : tree :=
  match slot_name w c with
  | Some n => Node R_type_name [Leaf (TName n)]
  | None => Node R_infer_type [sym "_"]
  end.

Fixpoint slot_trees (w : gdecl) (cs : list nat) {struct cs} : list tree :=
  match cs with
  | [] => []
  | [c] => [slot_tree w c]
  | c :: rest => slot_tree w c :: sym "," :: slot_trees w rest
  end.

Definition case_kids (w : gdecl) (tg : nat) (cs : list nat) : list tree :=
  ident (cn w tg)
    :: match cs with
       | [] => []
       | _ => sym "(" :: slot_trees w cs ++ [sym ")"]
       end.

Definition case_tree (w : gdecl) (tg : nat) (cs : list nat) : tree :=
  Node R_tag_case (case_kids w tg cs).

Fixpoint more_case_trees (w : gdecl) (tg : nat) (css : list (list nat)) {struct css} : list tree :=
  match css with
  | [] => []
  | cs :: rest => sym "|" :: case_tree w tg cs :: more_case_trees w (S tg) rest
  end.

Definition tag_decl_tree (w : gdecl) : tree :=
  Node R_tag_decl
    ([Node R_tag_kw [sym "tag"];
      Node R_group_name [ident (gname w)];
      sym "="]
     ++ match snd w with
        | [] => []
        | cs :: rest => case_tree w 0 cs :: more_case_trees w 1 rest
        end).

(* What the printer can write of a group: the name is bytes, spelled apart from
   the words that stand for the base slots; the slot codes are the base codes and
   the parameters [6], [7], ... in the order they are written; a declaration has
   a case. *)
Definition reserved_name (s : string) : bool :=
  existsb (String.eqb s) ["Int"; "Number"; "Bool"; "Unit"; "String"]%string.

Definition params_of (cs : list (list nat)) : list nat :=
  List.filter (Nat.leb 6) (List.concat cs).

Definition WfGroup (w : gdecl) : Prop :=
  Forall (fun b => b < 256) (fst w) /\ reserved_name (gname w) = false /\
  snd w <> [] /\ params_of (snd w) = List.seq 6 (List.length (params_of (snd w))).

Definition WfTable (D : list gdecl) : Prop :=
  Forall WfGroup D /\ NoDup (List.map fst D).

(* A match arm [Tag(x0, ..., xm) then body] binds the payload and then each name
   to its slot: the arm term is [m] bindings of the slots of the payload, then
   the body. The payload is the arm's own binder, so after [j] slot bindings it
   is the index [j]. *)
Definition arm_arity (w : gdecl) (tg : nat) : nat := List.length (List.nth tg (snd w) []).

Fixpoint arm_chain (m j : nat) (b : exp) {struct m} : Prop :=
  match m with
  | 0 => True
  | S m' =>
      match b with
      | e_let (e_proj (e_fvar_b i) l) b' => i = j /\ l = j /\ arm_chain m' (S j) b'
      | _ => False
      end
  end.

Fixpoint arm_inner (m : nat) (b : exp) {struct m} : exp :=
  match m with
  | 0 => b
  | S m' => match b with e_let _ b' => arm_inner m' b' | _ => b end
  end.

(* The names of an arm's slots, from depth [q]. *)
Fixpoint arm_names (q m : nat) {struct m} : list tree :=
  match m with
  | 0 => []
  | S m' =>
      match m' with
      | 0 => [ident (nm q)]
      | _ => ident (nm q) :: sym "," :: arm_names (S q) m'
      end
  end.

Definition arm_pattern (w : gdecl) (tg P : nat) : list tree :=
  match arm_arity w tg with
  | 0 => [ident (cn w tg)]
  | m => [ident (cn w tg); sym "(";
          Node R_labels (arm_names (S P) m); sym ")"]
  end.

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

(* Whether a callee is a projection of a group's member, which is printed as
   the member's name. *)
Definition is_group_proj (G : Grp) (P : nat) (f : exp) : bool :=
  match f with
  | e_proj g _ => match proj_level G P g with Some _ => true | None => false end
  | _ => false
  end.

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

(* A callee is parenthesised as [as_callee] says, unless it is a member's name. *)
Definition callee_of (G : Grp) (P : nat) (f : exp) (b : list tree) : list tree :=
  if is_group_proj G P f then b else as_callee f b.

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
  | e_app f e_unit => callee_of G P f (block G P f) ++ [call_unit_tree]
  | e_app f a => callee_of G P f (block G P f) ++ [call_tree (block G P a)]
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
  | e_unit | e_tofloat _ | e_fold _ | e_unfold _ | e_restrict _ _ => []
  | e_con w tg a =>
      match a with
      | e_rec (fs_cons _ x rest) =>
          [ident (cn w tg);
           Node R_call [sym "("; Node R_arguments (Node R_expr (block G P x) :: slot_args G P rest);
                        sym ")"]]
      | _ => [ident (cn w tg); call_unit_tree]
      end
  | e_match w a ars =>
      [Node R_match_expr ([sym "match"; Node R_expr (block G P a); sym "do"]
                          ++ arm_trees G P w ars ++ [sym "done"])]
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
  end
with slot_args (G : Grp) (P : nat) (fs : Goat_ott.fields) {struct fs} : list tree :=
  match fs with
  | fs_nil => []
  | fs_cons _ x rest => sym "," :: Node R_expr (block G P x) :: slot_args G P rest
  | fs_meth _ x rest => sym "," :: Node R_expr (block G P x) :: slot_args G P rest
  end
with arm_trees (G : Grp) (P : nat) (w : gdecl) (ars : arms) {struct ars} : list tree :=
  match ars with
  | arms_nil => []
  | arms_else e => [sym "else"; Node R_expr (block G P e)]
  | arms_cons tg b rest =>
      Node R_arm [Node R_pattern (arm_pattern w tg P); sym "then";
                  Node R_expr (match arm_arity w tg with
                               | 0 => block G (S P) b
                               | m => arm_body G (S P) m b
                               end)]
        :: arm_trees G P w rest
  end
with arm_body (G : Grp) (Q m : nat) (b : exp) {struct b} : list tree :=
  match b with
  | e_let _ b' =>
      match m with
      | S (S m') => arm_body G (S Q) (S m') b'
      | _ => block G (S Q) b'
      end
  | _ => []
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

(* A program: the tag declarations of the table [D], then the expression. *)
Definition print_decls (D : list gdecl) : list tree := List.map tag_decl_tree D.

Definition print_tree (D : list gdecl) (e : exp) : tree :=
  Node R_goat (print_decls D ++ [Node R_expr (block [] 0 e)]).

Definition print (D : list gdecl) (e : exp) : list tok :=
  flats (print_decls D) ++ flats (block [] 0 e).

(* ---- what the printer is defined on, and what it needs ---- *)

(* A term that is not a recursive group: a group is first in its block, so
   nothing that continues a block (the body of a binding or of a group) can be
   one, or the group's members would join the earlier group. *)
Definition NonRec (e : exp) : Prop :=
  match e with e_letrec _ _ => False | _ => True end.

(* The bound index [k] does not occur: the binder it names is not used. *)
Fixpoint unused (k : nat) (e : exp) {struct e} : Prop :=
  match e with
  | e_fvar_b i => i <> k
  | e_fvar_f _ | e_num _ | e_dec _ | e_true | e_false | e_unit | e_str _ => True
  | e_abs b => unused (S k) b
  | e_app a b | e_bin a _ b | e_spread a _ b => unused k a /\ unused k b
  | e_let a b => unused k a /\ unused (S k) b
  | e_letrec fs b => unused_fields (S k) fs /\ unused (S k) b
  | e_rec fs => unused_fields k fs
  | e_proj a _ | e_tofloat a | e_con _ _ a | e_restrict a _ | e_fold a | e_unfold a => unused k a
  | e_ite a b c => unused k a /\ unused k b /\ unused k c
  | e_match _ a ars => unused k a /\ unused_arms k ars
  end
with unused_fields (k : nat) (fs : Goat_ott.fields) {struct fs} : Prop :=
  match fs with
  | fs_nil => True
  | fs_cons _ e rest => unused k e /\ unused_fields k rest
  | fs_meth _ e rest => unused k e /\ unused_fields k rest
  end
with unused_arms (k : nat) (ars : arms) {struct ars} : Prop :=
  match ars with
  | arms_nil => True
  | arms_else e => unused k e
  | arms_cons _ b rest => unused (S k) b /\ unused_arms k rest
  end.

(* A closed term whose bound indices are below [n], among them the groups of
   [G]. A group's binder is used only to project a member, and a group is a
   nonempty run of one-parameter functions labelled by position. *)
Fixpoint scoped (G : Grp) (n : nat) (e : exp) {struct e} : Prop :=
  match e with
  | e_fvar_b i => i < n /\ grp_size G (n - 1 - i) = None
  | e_fvar_f _ => False
  | e_num z => z_nonneg z = true
  | e_true | e_false | e_str _ | e_dec _ => True
  | e_unit | e_tofloat _ | e_fold _ | e_unfold _ | e_restrict _ _ => False
  | e_con w tg a =>
      tg < List.length (snd w) /\
      match a with
      | e_unit => True
      | e_rec (fs_cons i x rest) => i = 0 /\ scoped G n x /\ scoped_slots G n 1 rest
      | _ => False
      end
  | e_match w a ars =>
      scoped G n a /\
      match ars with
      | arms_cons _ _ _ => scoped_arms G n w ars
      | _ => False
      end
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
  end
(* A tag's payload: slots labelled by position, as the denotation builds it. *)
with scoped_slots (G : Grp) (n i : nat) (fs : Goat_ott.fields) {struct fs} : Prop :=
  match fs with
  | fs_nil => True
  | fs_cons l e rest => l = i /\ scoped G n e /\ scoped_slots G n (S i) rest
  | fs_meth _ _ _ => False
  end
(* The arms of a match: each tag arm is the slots bound from the payload and a
   body that does not use the payload itself; the arms end with the arms
   missing or an [else]. *)
with scoped_arms (G : Grp) (n : nat) (w : gdecl) (ars : arms) {struct ars} : Prop :=
  match ars with
  | arms_nil => True
  | arms_else e => scoped G n e
  | arms_cons tg b rest =>
      tg < List.length (snd w) /\ scoped G (S n) b /\
      arm_chain (arm_arity w tg) 0 b /\ unused (arm_arity w tg) (arm_inner (arm_arity w tg) b) /\
      scoped_arms G n w rest
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
  (a = e_unit /\ block G P (e_app f a) = callee_of G P f (block G P f) ++ [call_unit_tree])
  \/ (a <> e_unit /\
      block G P (e_app f a) = callee_of G P f (block G P f) ++ [call_tree (block G P a)]).
Proof.
  intros G P f a. destruct a;
    first [ (left; split; reflexivity) | (right; split; [ discriminate | reflexivity ]) ].
Qed.

Lemma block_ite_unit : forall G P c a,
  block G P (e_ite c a e_unit) = [cond_tree_noelse (block G P c) (block G P a)].
Proof. reflexivity. Qed.

Lemma is_group_proj_true : forall G P f,
  is_group_proj G P f = true ->
  exists g l L, f = e_proj g l /\ proj_level G P g = Some L.
Proof.
  intros G P f H. destruct f; try discriminate H.
  unfold is_group_proj in H.
  match type of H with context [proj_level _ _ ?g] =>
    destruct (proj_level G P g) eqn:E; [ | discriminate H ];
    do 3 eexists; split; [ reflexivity | exact E ] end.
Qed.

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
  | e_con _ _ a =>
      match a with
      | e_rec (fs_cons _ x rest) => lbls G P x ++ lbls_slots G P rest
      | _ => []
      end
  | e_match w a ars => lbls G P a ++ lbls_arms G P w ars
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
  end
with lbls_slots (G : Grp) (P : nat) (fs : Goat_ott.fields) {struct fs} : list nat :=
  match fs with
  | fs_nil => []
  | fs_cons _ e rest => lbls G P e ++ lbls_slots G P rest
  | fs_meth _ e rest => lbls G P e ++ lbls_slots G P rest
  end
with lbls_arms (G : Grp) (P : nat) (w : gdecl) (ars : arms) {struct ars} : list nat :=
  match ars with
  | arms_nil => []
  | arms_else e => lbls G P e
  | arms_cons tg b rest =>
      match arm_arity w tg with
      | 0 => lbls G (S P) b
      | m => lbls_body G (S P) m b
      end ++ lbls_arms G P w rest
  end
with lbls_body (G : Grp) (Q m : nat) (b : exp) {struct b} : list nat :=
  match b with
  | e_let _ b' =>
      match m with
      | S (S m') => lbls_body G (S Q) (S m') b'
      | _ => lbls G (S Q) b'
      end
  | _ => []
  end.

(* The tags the term builds and matches are groups of the table. *)
Fixpoint tags_in (D : list gdecl) (e : exp) {struct e} : Prop :=
  match e with
  | e_abs b | e_proj b _ | e_tofloat b | e_restrict b _ | e_fold b | e_unfold b => tags_in D b
  | e_app a b | e_bin a _ b | e_spread a _ b | e_let a b => tags_in D a /\ tags_in D b
  | e_letrec fs b => tags_in_fields D fs /\ tags_in D b
  | e_rec fs => tags_in_fields D fs
  | e_ite a b c => tags_in D a /\ tags_in D b /\ tags_in D c
  | e_con w _ a => List.In w D /\ tags_in D a
  | e_match w a ars => List.In w D /\ tags_in D a /\ tags_in_arms D ars
  | _ => True
  end
with tags_in_fields (D : list gdecl) (fs : Goat_ott.fields) {struct fs} : Prop :=
  match fs with
  | fs_nil => True
  | fs_cons _ e rest => tags_in D e /\ tags_in_fields D rest
  | fs_meth _ e rest => tags_in D e /\ tags_in_fields D rest
  end
with tags_in_arms (D : list gdecl) (ars : arms) {struct ars} : Prop :=
  match ars with
  | arms_nil => True
  | arms_else e => tags_in D e
  | arms_cons _ b rest => tags_in D b /\ tags_in_arms D rest
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
