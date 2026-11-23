(* The denotation of a core-fragment parse tree as an Ott term, and its local
   closure (the denotation half of T1, ADR 0030). *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatMeta.
From Stdlib Require Import Lia.
Require Export Goat.GoatLit.
Require Import Goat.GoatNum.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatPrec.
Open Scope string_scope.

(* ---- closing a variable, and the n-ary forms curried ---- *)

Fixpoint close_exp_rec (k : nat) (x : termvar) (e : exp) {struct e} : exp :=
  match e with
  | e_fvar_b i => e_fvar_b i
  | e_fvar_f y => if y == x then e_fvar_b k else e_fvar_f y
  | e_num n => e_num n
  | e_dec d => e_dec d
  | e_true => e_true
  | e_false => e_false
  | e_abs b => e_abs (close_exp_rec (S k) x b)
  | e_app a b => e_app (close_exp_rec k x a) (close_exp_rec k x b)
  | e_let a b => e_let (close_exp_rec k x a) (close_exp_rec (S k) x b)
  | e_letrec fs b => e_letrec (close_fields_rec (S k) x fs) (close_exp_rec (S k) x b)
  | e_rec fs => e_rec (close_fields_rec k x fs)
  | e_proj a l => e_proj (close_exp_rec k x a) l
  | e_unit => e_unit
  | e_str q => e_str q
  | e_ite a b c => e_ite (close_exp_rec k x a) (close_exp_rec k x b) (close_exp_rec k x c)
  | e_bin a o b => e_bin (close_exp_rec k x a) o (close_exp_rec k x b)
  | e_tofloat a => e_tofloat (close_exp_rec k x a)
  | e_con w tg a => e_con w tg (close_exp_rec k x a)
  | e_match w a ars => e_match w (close_exp_rec k x a) (close_arms_rec k x ars)
  | e_spread a l b => e_spread (close_exp_rec k x a) l (close_exp_rec k x b)
  | e_restrict a l => e_restrict (close_exp_rec k x a) l
  | e_fold a => e_fold (close_exp_rec k x a)
  | e_unfold a => e_unfold (close_exp_rec k x a)
  end
with close_fields_rec (k : nat) (x : termvar) (fs : fields) {struct fs} : fields :=
  match fs with
  | fs_nil => fs_nil
  | fs_cons l e fs' => fs_cons l (close_exp_rec k x e) (close_fields_rec k x fs')
  | fs_meth l e fs' => fs_meth l (close_exp_rec k x e) (close_fields_rec k x fs')
  end
with close_arms_rec (k : nat) (x : termvar) (ars : arms) {struct ars} : arms :=
  match ars with
  | arms_nil => arms_nil
  | arms_else e => arms_else (close_exp_rec k x e)
  | arms_cons tg e ars' => arms_cons tg (close_exp_rec (S k) x e) (close_arms_rec k x ars')
  end.

Definition close_exp (x : termvar) (e : exp) : exp := close_exp_rec 0 x e.

(* program(x1, ..., xk) do b done *)
Definition curry (xs : list termvar) (b : exp) : exp :=
  fold_right (fun x acc => e_abs (close_exp x acc)) b xs.

(* f(a1, ..., ak) *)
Definition apps (f : exp) (args : list exp) : exp := fold_left e_app args f.

(* A recursive group's name is one binder over its members and its body: each
   free occurrence of a member's name becomes the projection of that member
   from the group (ADR 0003). A member's label is its position in the group. *)
Fixpoint index_in (y : termvar) (names : list termvar) : option nat :=
  match names with
  | [] => None
  | n :: rest => if y == n then Some 0 else option_map S (index_in y rest)
  end.

Fixpoint bind_group_rec (k : nat) (names : list termvar) (e : exp) {struct e} : exp :=
  match e with
  | e_fvar_b i => e_fvar_b i
  | e_fvar_f y =>
      match index_in y names with
      | Some i => e_proj (e_fvar_b k) i
      | None => e_fvar_f y
      end
  | e_num n => e_num n
  | e_dec d => e_dec d
  | e_true => e_true
  | e_false => e_false
  | e_abs b => e_abs (bind_group_rec (S k) names b)
  | e_app a b => e_app (bind_group_rec k names a) (bind_group_rec k names b)
  | e_let a b => e_let (bind_group_rec k names a) (bind_group_rec (S k) names b)
  | e_letrec fs b => e_letrec (bind_group_fields (S k) names fs) (bind_group_rec (S k) names b)
  | e_rec fs => e_rec (bind_group_fields k names fs)
  | e_proj a l => e_proj (bind_group_rec k names a) l
  | e_unit => e_unit
  | e_str q => e_str q
  | e_ite a b c =>
      e_ite (bind_group_rec k names a) (bind_group_rec k names b) (bind_group_rec k names c)
  | e_bin a o b => e_bin (bind_group_rec k names a) o (bind_group_rec k names b)
  | e_tofloat a => e_tofloat (bind_group_rec k names a)
  | e_con w tg a => e_con w tg (bind_group_rec k names a)
  | e_match w a ars => e_match w (bind_group_rec k names a) (bind_group_arms k names ars)
  | e_spread a l b => e_spread (bind_group_rec k names a) l (bind_group_rec k names b)
  | e_restrict a l => e_restrict (bind_group_rec k names a) l
  | e_fold a => e_fold (bind_group_rec k names a)
  | e_unfold a => e_unfold (bind_group_rec k names a)
  end
with bind_group_fields (k : nat) (names : list termvar) (fs : fields) {struct fs} : fields :=
  match fs with
  | fs_nil => fs_nil
  | fs_cons l e fs' => fs_cons l (bind_group_rec k names e) (bind_group_fields k names fs')
  | fs_meth l e fs' => fs_meth l (bind_group_rec k names e) (bind_group_fields k names fs')
  end
with bind_group_arms (k : nat) (names : list termvar) (ars : arms) {struct ars} : arms :=
  match ars with
  | arms_nil => arms_nil
  | arms_else e => arms_else (bind_group_rec k names e)
  | arms_cons tg e ars' => arms_cons tg (bind_group_rec (S k) names e) (bind_group_arms k names ars')
  end.

Definition bind_group (names : list termvar) (e : exp) : exp := bind_group_rec 0 names e.

(* The record of a group's members, labelled by position. *)
Fixpoint group_fields_from (names : list termvar) (i : nat) (vs : list exp) : fields :=
  match vs with
  | [] => fs_nil
  | v :: rest => fs_cons i (bind_group names v) (group_fields_from names (S i) rest)
  end.

Definition group_fields (names : list termvar) (vs : list exp) : fields :=
  group_fields_from names 0 vs.

(* ---- closing preserves local closure ---- *)

Lemma lc_close_mut :
  (forall e k x, lc_at k e -> lc_at (S k) (close_exp_rec k x e)) /\
  (forall fs k x, lcf_at k fs -> lcf_at (S k) (close_fields_rec k x fs)) /\
  (forall ars k x, lca_at k ars -> lca_at (S k) (close_arms_rec k x ars)).
Proof.
  apply exp_fields_mutind.
  - (* bound index: below k, so below S k *)
    intros i k x Hi. simpl in *. lia.
  - (* free variable: x becomes index k, below S k; any other stays *)
    intros y k x _. simpl. destruct (y == x); simpl; [ lia | exact I ].
  - intros n k x _. exact I.
  - intros d k x _. exact I.
  - intros k x _. exact I.
  - intros k x _. exact I.
  - (* abs: the body is one level deeper *)
    intros b IH k x Hb. simpl in *. exact (IH (S k) x Hb).
  - (* app *)
    intros a IHa b IHb k x [Ha Hb]. simpl.
    split; [ exact (IHa k x Ha) | exact (IHb k x Hb) ].
  - (* let: the body is one level deeper, the value is not *)
    intros a IHa b IHb k x [Ha Hb]. simpl.
    split; [ exact (IHa k x Ha) | exact (IHb (S k) x Hb) ].
  - (* letrec: the group and the body are one level deeper *)
    intros fs IHfs b IHb k x [Hfs Hb]. simpl.
    split; [ exact (IHfs (S k) x Hfs) | exact (IHb (S k) x Hb) ].
  - (* record *)
    intros fs IH k x Hfs. simpl in *. exact (IH k x Hfs).
  - (* projection *)
    intros a IH l k x Ha. simpl in *. exact (IH k x Ha).
  - intros k x _. exact I.
  - intros q k x _. exact I.
  - (* conditional *)
    intros a IHa b IHb c IHc k x [Ha [Hb Hc]]. simpl.
    split; [ exact (IHa k x Ha) | split; [ exact (IHb k x Hb) | exact (IHc k x Hc) ] ].
  - (* binary operation *)
    intros a IHa o b IHb k x [Ha Hb]. simpl.
    split; [ exact (IHa k x Ha) | exact (IHb k x Hb) ].
  - (* coercion *)
    intros a IH k x Ha. simpl in *. exact (IH k x Ha).
  - (* tag construction *)
    intros w tg a IH k x Ha. simpl in *. exact (IH k x Ha).
  - (* match: each arm is one level deeper *)
    intros w a IHa ars IHars k x [Ha Hars]. simpl.
    split; [ exact (IHa k x Ha) | exact (IHars k x Hars) ].
  - (* spread *)
    intros a IHa l b IHb k x [Ha Hb]. simpl.
    split; [ exact (IHa k x Ha) | exact (IHb k x Hb) ].
  - (* restrict *)
    intros a IH l k x Ha. simpl in *. exact (IH k x Ha).
  - intros a IH k x Ha. simpl in *. exact (IH k x Ha).
  - intros a IH k x Ha. simpl in *. exact (IH k x Ha).
  - intros k x _. exact I.
  - (* field list *)
    intros l e IHe fs IHfs k x [He Hfs]. simpl.
    split; [ exact (IHe k x He) | exact (IHfs k x Hfs) ].
  - (* method field *)
    intros l e IHe fs IHfs k x [He Hfs]. simpl.
    split; [ exact (IHe k x He) | exact (IHfs k x Hfs) ].
  - intros k x _. exact I.
  - (* else *)
    intros e IH k x He. simpl in *. exact (IH k x He).
  - (* arm *)
    intros tg e IHe ars IHars k x [He Hars]. simpl.
    split; [ exact (IHe (S k) x He) | exact (IHars k x Hars) ].
Qed.

Lemma lc_bind_group_mut :
  (forall e k names, lc_at k e -> lc_at (S k) (bind_group_rec k names e)) /\
  (forall fs k names, lcf_at k fs -> lcf_at (S k) (bind_group_fields k names fs)) /\
  (forall ars k names, lca_at k ars -> lca_at (S k) (bind_group_arms k names ars)).
Proof.
  apply exp_fields_mutind.
  - intros i k names Hi. simpl in *. lia.
  - intros y k names _. simpl. destruct (index_in y names); simpl; [ lia | exact I ].
  - intros n k names _. exact I.
  - intros d k names _. exact I.
  - intros k names _. exact I.
  - intros k names _. exact I.
  - intros b IH k names Hb. simpl in *. exact (IH (S k) names Hb).
  - intros a IHa b IHb k names [Ha Hb]. simpl.
    split; [ exact (IHa k names Ha) | exact (IHb k names Hb) ].
  - intros a IHa b IHb k names [Ha Hb]. simpl.
    split; [ exact (IHa k names Ha) | exact (IHb (S k) names Hb) ].
  - intros fs IHfs b IHb k names [Hfs Hb]. simpl.
    split; [ exact (IHfs (S k) names Hfs) | exact (IHb (S k) names Hb) ].
  - intros fs IH k names Hfs. simpl in *. exact (IH k names Hfs).
  - intros a IH l k names Ha. simpl in *. exact (IH k names Ha).
  - intros k names _. exact I.
  - intros q k names _. exact I.
  - intros a IHa b IHb c IHc k names [Ha [Hb Hc]]. simpl.
    split; [ exact (IHa k names Ha) | split; [ exact (IHb k names Hb) | exact (IHc k names Hc) ] ].
  - intros a IHa o b IHb k names [Ha Hb]. simpl.
    split; [ exact (IHa k names Ha) | exact (IHb k names Hb) ].
  - intros a IH k names Ha. simpl in *. exact (IH k names Ha).
  - intros w tg a IH k names Ha. simpl in *. exact (IH k names Ha).
  - intros w a IHa ars IHars k names [Ha Hars]. simpl.
    split; [ exact (IHa k names Ha) | exact (IHars k names Hars) ].
  - intros a IHa l b IHb k names [Ha Hb]. simpl.
    split; [ exact (IHa k names Ha) | exact (IHb k names Hb) ].
  - intros a IH l k names Ha. simpl in *. exact (IH k names Ha).
  - intros a IH k names Ha. simpl in *. exact (IH k names Ha).
  - intros a IH k names Ha. simpl in *. exact (IH k names Ha).
  - intros k names _. exact I.
  - intros l e IHe fs IHfs k names [He Hfs]. simpl.
    split; [ exact (IHe k names He) | exact (IHfs k names Hfs) ].
  - intros l e IHe fs IHfs k names [He Hfs]. simpl.
    split; [ exact (IHe k names He) | exact (IHfs k names Hfs) ].
  - intros k names _. exact I.
  - intros e IH k names He. simpl in *. exact (IH k names He).
  - intros tg e IHe ars IHars k names [He Hars]. simpl.
    split; [ exact (IHe (S k) names He) | exact (IHars k names Hars) ].
Qed.

Lemma lcf_group_fields_from : forall names vs i,
  Forall lc vs -> lcf_at 1 (group_fields_from names i vs).
Proof.
  intros names vs i Hvs. revert i.
  induction Hvs as [| v vs Hv Hvs IH]; intros i; simpl; [ exact I | ].
  split.
  - exact (proj1 lc_bind_group_mut v 0 names Hv).
  - exact (IH (S i)).
Qed.

Lemma lcf_group_fields : forall names vs,
  Forall lc vs -> lcf_at 1 (group_fields names vs).
Proof. intros names vs Hvs. exact (lcf_group_fields_from names vs 0 Hvs). Qed.

Lemma lc_curry : forall xs b, lc b -> lc (curry xs b).
Proof.
  intros xs b Hb. induction xs as [| x xs IH]; simpl.
  - exact Hb.
  - assert (Hclose : lc_at 1 (close_exp x (curry xs b)))
      by (apply (proj1 lc_close_mut); exact IH).
    exact Hclose.
Qed.

Lemma lc_apps : forall args f, lc f -> Forall lc args -> lc (apps f args).
Proof.
  intros args. induction args as [| a args IH]; intros f Hf Hargs; simpl.
  - exact Hf.
  - inversion Hargs as [| ? ? Ha Hrest]; subst.
    apply IH; [ split; assumption | assumption ].
Qed.

(* ---- the denotation ---- *)

Definition starts_call (ts : list tree) : Prop :=
  match ts with Node R_call _ :: _ => True | _ => False end.

(* A receiver that is a name or a path of field accesses is repeated by a dot
   call; any other receiver is bound once to a hidden name (ADR 0031). *)
Fixpoint is_path (e : exp) : bool :=
  match e with
  | e_fvar_f _ => true
  | e_proj a _ => is_path a
  | _ => false
  end.

Fixpoint index_of (l : string) (tbl : list string) : nat :=
  match tbl with
  | [] => 0
  | l' :: tbl' => if String.eqb l l' then 0 else S (index_of l tbl')
  end.

Definition op_rule (o : bop) : rule :=
  match o with
  | bop_add => R_plus
  | bop_sub => R_minus
  | bop_mul => R_multiply
  | bop_div => R_divide
  | bop_fdiv => R_floor_divide
  | bop_rem => R_remainder
  | bop_lt => R_lt
  | bop_lte => R_lte
  | bop_gt => R_gt
  | bop_gte => R_gte
  | bop_eq => R_equal
  | bop_ne => R_not_equal
  end.

Definition op_text (o : bop) : string :=
  match o with
  | bop_add => "+"
  | bop_sub => "-"
  | bop_mul => "*"
  | bop_div => "/"
  | bop_fdiv => "//"
  | bop_rem => "%"
  | bop_lt => "<"
  | bop_lte => "<="
  | bop_gt => ">"
  | bop_gte => ">="
  | bop_eq => "=="
  | bop_ne => "!="
  end.

Definition op_tree (o : bop) : tree := Node (op_rule o) [Leaf (TSym (op_text o))].

Definition not_tree : tree := Node R_not_op [Leaf (TSym "not")].

(* The tree an operator of a run makes. *)
Definition lop_tree (o : lop) : tree :=
  match o with
  | L_or => Node R_or_op [Leaf (TSym "or")]
  | L_and => Node R_and_op [Leaf (TSym "and")]
  | L_bin o' => op_tree o'
  | L_not => not_tree
  end.

(* [-3] is one literal, as in lowering; any other [-x] is [0 - x]. *)
Definition bare_number (cs : list tree) : Prop :=
  exists c, cs = [Node R_number c].

(* A declaration whose value is exactly a function literal is a member of the
   block's recursive group (ADR 0003); a parenthesised function is a value. *)
Definition fn_value (cs : list tree) : bool :=
  match cs with Node R_function _ :: [] => true | _ => false end.

Definition is_fn_decl (d : tree) : bool :=
  match d with
  | Node R_declaration (_ :: _ :: Node R_value v :: _) => fn_value v
  | _ => false
  end.

(* A multi-field spread is the nest of single ones, and a rest pattern with k
   labels is k restricts (ADR 0033). *)
Fixpoint spread_nest (b : exp) (fs : fields) {struct fs} : exp :=
  match fs with
  | fs_nil => b
  | fs_cons l e rest => spread_nest (e_spread b l e) rest
  | fs_meth l e rest => spread_nest (e_spread b l e) rest
  end.

Definition restricts (b : exp) (ls : list label) : exp := fold_left e_restrict ls b.

Lemma lc_spread_nest : forall fs b, lc b -> lcf fs -> lc (spread_nest b fs).
Proof.
  induction fs as [| l e rest IH | l e rest IH]; intros b Hb Hfs; simpl.
  - exact Hb.
  - destruct Hfs as [He Hrest].
    apply IH; [ exact (conj Hb He) | exact Hrest ].
  - destruct Hfs as [He Hrest].
    apply IH; [ exact (conj Hb He) | exact Hrest ].
Qed.

Lemma lc_restricts : forall ls b, lc b -> lc (restricts b ls).
Proof.
  induction ls as [| l ls IH]; intros b Hb; unfold restricts in *; simpl.
  - exact Hb.
  - apply IH. exact Hb.
Qed.

(* ---- the tag table: declarations read first, tags resolved by name ---- *)

(* A tag name to the group it belongs to (its slot codes, GoatDefs.v) and its
   position there. The first entry for a name wins, as in lowering, so the
   prelude's tags precede the program's. *)
Definition tagtab := list (string * (gdecl * nat)).

Fixpoint tag_lookup (tt : tagtab) (x : string) : option (gdecl * nat) :=
  match tt with
  | [] => None
  | (y, v) :: rest => if String.eqb x y then Some v else tag_lookup rest x
  end.

Class TagTable := { tags : tagtab }.

#[global] Instance no_tags : TagTable := {| tags := [] |}.

Definition mk_tags (tt : tagtab) : TagTable := {| tags := tt |}.

(* The slot code of a payload type: 0 the group, 1 to 5 Int, Float (`Number`),
   Bool, Unit, String, and 6 + j the j-th `_` of the declaration. *)
Definition slot_of (g : option string) (name : string) : nat :=
  if match g with Some n => String.eqb n name | None => false end then 0
  else if String.eqb name "Int" then 1
  else if String.eqb name "Number" then 2
  else if String.eqb name "Bool" then 3
  else if String.eqb name "Unit" then 4
  else if String.eqb name "String" then 5
  else 0.

Definition type_slot (g : option string) (j : nat) (t : tree) : nat * nat :=
  match t with
  | Node R_infer_type _ => (6 + j, S j)
  | Node R_type_name [Leaf (TName n)] => (slot_of g n, j)
  | _ => (0, j)
  end.

Definition is_type_node (t : tree) : bool :=
  match t with
  | Node R_infer_type _ | Node R_type_name _ => true
  | _ => false
  end.

Fixpoint type_slots (g : option string) (j : nat) (ts : list tree) {struct ts} : list nat * nat :=
  match ts with
  | [] => ([], j)
  | t :: rest =>
      let (c, j1) := type_slot g j t in
      let (cs, j2) := type_slots g j1 rest in
      (c :: cs, j2)
  end.

Definition case_name (cs : list tree) : string :=
  match cs with Node R_name [Leaf (TName n)] :: _ => n | _ => "" end.

Fixpoint decl_cases (cs : list tree) : list (list tree) :=
  match cs with
  | [] => []
  | Node R_tag_case c :: rest => c :: decl_cases rest
  | _ :: rest => decl_cases rest
  end.

Definition decl_group (cs : list tree) : option string :=
  match cs with
  | _ :: Node R_group_name [Node R_name [Leaf (TName g)]] :: _ => Some g
  | _ => None
  end.

Fixpoint cases_slots (g : option string) (j : nat) (cases : list (list tree)) {struct cases}
  : list (string * list nat) :=
  match cases with
  | [] => []
  | c :: rest =>
      let (cs, j1) := type_slots g j (List.filter is_type_node c) in
      (case_name c, cs) :: cases_slots g j1 rest
  end.

(* A group's name as bytes: the declared group name, else the first case's name,
   so each declaration is its own group (a tag belongs to exactly one). *)
Definition decl_name (cs : list tree) (cases : list (string * list nat)) : list nat :=
  let n := match decl_group cs with
           | Some g => g
           | None => match cases with (c, _) :: _ => c | [] => ""%string end
           end in
  List.map Ascii.nat_of_ascii (String.list_ascii_of_string n).

(* What one `tag` declaration adds to the table. *)
Definition decl_entries (d : tree) : tagtab :=
  match d with
  | Node R_tag_decl cs =>
      let cases := cases_slots (decl_group cs) 0 (decl_cases cs) in
      let w : gdecl := (decl_name cs cases, List.map snd cases) in
      List.map (fun ic => (fst (snd ic), (w, fst ic)))
               (List.combine (List.seq 0 (List.length cases)) cases)
  | _ => []
  end.

Definition is_tag_decl (t : tree) : bool :=
  match t with Node R_tag_decl _ => true | _ => false end.

(* A tag's payload is the record of its slots, labelled by position. *)
Fixpoint slot_fields (i : nat) (es : list exp) : fields :=
  match es with
  | [] => fs_nil
  | e :: rest => fs_cons i e (slot_fields (S i) rest)
  end.

Definition payload (es : list exp) : exp := e_rec (slot_fields 0 es).

(* `[a, b]` is `Link(a, Link(b, Empty))`. *)
Fixpoint list_of (we : gdecl) (tge : nat) (wl : gdecl) (tgl : nat) (es : list exp) : exp :=
  match es with
  | [] => e_con we tge e_unit
  | e :: rest =>
      e_con wl tgl (e_rec (fs_cons 0 e (fs_cons 1 (list_of we tge wl tgl rest) fs_nil)))
  end.

(* An arm `Tag(a, b) then body` binds the payload to one variable and each name
   to its slot. *)
Fixpoint slot_lets (var_of : string -> termvar) (s : termvar) (i : nat) (xs : list string)
  (body : exp) {struct xs} : exp :=
  match xs with
  | [] => body
  | x :: rest =>
      e_let (e_proj (e_fvar_f s) i)
            (close_exp (var_of x) (slot_lets var_of s (S i) rest body))
  end.

(* A match on literals is a chain of equality tests on the scrutinee. *)
Definition lit_chain (subject : exp) (rows : list (exp * exp)) (els : exp) : exp :=
  fold_right (fun r tail => e_ite (e_bin subject bop_eq (fst r)) (snd r) tail) els rows.

Fixpoint fv_rows (rows : list (exp * exp)) : atoms :=
  match rows with
  | [] => AtomSetImpl.empty
  | r :: rest => fv_exp (fst r) `union` fv_exp (snd r) `union` fv_rows rest
  end.

Lemma lc_slot_fields : forall es i, Forall lc es -> lcf (slot_fields i es).
Proof.
  intros es i H. revert i.
  induction H as [| e es He Hes IH]; intros i; simpl; [ exact I | ].
  exact (conj He (IH (S i))).
Qed.

Lemma lc_payload : forall es, Forall lc es -> lc (payload es).
Proof. intros es H. exact (lc_slot_fields es 0 H). Qed.

Lemma lc_list_of : forall we tge wl tgl es,
  Forall lc es -> lc (list_of we tge wl tgl es).
Proof.
  intros we tge wl tgl es H.
  induction H as [| e es He Hes IH]; simpl; [ exact I | ].
  exact (conj He (conj IH I)).
Qed.

Lemma lc_slot_lets : forall var_of xs s i body,
  lc body -> lc (slot_lets var_of s i xs body).
Proof.
  intros var_of xs. induction xs as [| x xs IH]; intros s i body Hbody; simpl.
  - exact Hbody.
  - assert (Hclose : lc_at 1 (close_exp (var_of x) (slot_lets var_of s (S i) xs body)))
      by (apply (proj1 lc_close_mut); exact (IH s (S i) body Hbody)).
    exact (conj I Hclose).
Qed.

Lemma lc_lit_chain : forall subject rows els,
  lc subject -> Forall (fun r => lc (fst r) /\ lc (snd r)) rows -> lc els ->
  lc (lit_chain subject rows els).
Proof.
  intros subject rows els Hs Hrows Hels.
  induction Hrows as [| r rows [Hl Hb] Hrows IH]; simpl; [ exact Hels | ].
  exact (conj (conj Hs Hl) (conj Hb IH)).
Qed.

Section Denotation.

  Context {TT : TagTable}.

  Variable var_of : string -> termvar.
  Variable tbl : list string.

  Definition lab (l : string) : label := index_of l tbl.

  Definition sym (s : string) : tree := Leaf (TSym s).
  Definition ident (x : string) : tree := Node R_name [Leaf (TName x)].

  Definition rest_node (r : string) : tree := Node R_rest_binding [sym "..."; ident r].

  (* The children of a record pattern after its brace: the names, then an
     optional rest binding, then an optional trailing comma. *)
  Inductive Den_pat_start : list tree -> list string -> option string -> Prop :=
    | DPS_rest : forall r fin,
        (fin = [] \/ fin = [sym ","]) ->
        Den_pat_start (rest_node r :: fin ++ [sym "}"]) [] (Some r)
    | DPS_name : forall x ts xs ro,
        Den_pat_more ts xs ro ->
        Den_pat_start (ident x :: ts) (x :: xs) ro
  with Den_pat_more : list tree -> list string -> option string -> Prop :=
    | DPM_end :
        Den_pat_more [sym "}"] [] None
    | DPM_trail :
        Den_pat_more [sym ","; sym "}"] [] None
    | DPM_rest : forall r fin,
        (fin = [] \/ fin = [sym ","]) ->
        Den_pat_more (sym "," :: rest_node r :: fin ++ [sym "}"]) [] (Some r)
    | DPM_name : forall x ts xs ro,
        Den_pat_more ts xs ro ->
        Den_pat_more (sym "," :: ident x :: ts) (x :: xs) ro.

  (* [{x, y, ...r} = v body] reads [v] once, as the variable [s], then binds each
     name to its field and the rest to [s] without those fields. *)
  Definition rest_let (s : termvar) (xs : list string) (ro : option string) (body : exp) : exp :=
    match ro with
    | None => body
    | Some r =>
        e_let (restricts (e_fvar_f s) (List.map lab xs)) (close_exp (var_of r) body)
    end.

  Definition unpack (s : termvar) (xs : list string) (ro : option string) (body : exp) : exp :=
    fold_right
      (fun x acc => e_let (e_proj (e_fvar_f s) (lab x)) (close_exp (var_of x) acc))
      (rest_let s xs ro body) xs.

  Lemma lc_unpack : forall s xs ro body, lc body -> lc (unpack s xs ro body).
  Proof.
    intros s xs ro body Hbody. unfold unpack.
    assert (Hrest : lc (rest_let s xs ro body)).
    { unfold rest_let. destruct ro as [r | ]; [ | exact Hbody ].
      assert (Hclose : lc_at 1 (close_exp (var_of r) body))
        by (apply (proj1 lc_close_mut); exact Hbody).
      exact (conj (lc_restricts (List.map lab xs) (e_fvar_f s) I) Hclose). }
    revert Hrest. generalize (rest_let s xs ro body) as tl. clear Hbody.
    induction xs as [| x ys IH]; intros tl Hrest; simpl.
    - exact Hrest.
    - assert (Hclose : lc_at 1 (close_exp (var_of x)
                (fold_right (fun x acc => e_let (e_proj (e_fvar_f s) (lab x))
                                             (close_exp (var_of x) acc)) tl ys)))
        by (apply (proj1 lc_close_mut); exact (IH tl Hrest)).
      exact (conj I Hclose).
  Qed.

  Inductive Den_labels : list tree -> list string -> Prop :=
    | DLb_one : forall x, Den_labels [ident x] [x]
    | DLb_more : forall x rest xs,
        Den_labels rest xs ->
        Den_labels (ident x :: sym "," :: rest) (x :: xs).

  (* The children of a tag pattern: the tag, then the names it binds. *)
  Inductive Den_tpat : list tree -> string -> list string -> Prop :=
    | DTP_bare : forall t, Den_tpat [ident t] t []
    | DTP_empty : forall t, Den_tpat [ident t; sym "("; sym ")"] t []
    | DTP_labels : forall t ls xs,
        Den_labels ls xs ->
        Den_tpat [ident t; sym "("; Node R_labels ls; sym ")"] t xs.

  Inductive Den : tree -> exp -> Prop :=
    | D_num : forall n,
        Den (Node R_number [Leaf (TNum n)]) (e_num (z_of_nat n))
    | D_dec : forall d,
        Den (Node R_number [Leaf (TDec d)]) (e_dec d)
    | D_true :
        Den (Node R_boolean [Node R_true_lit [sym "true"]]) e_true
    | D_false :
        Den (Node R_boolean [Node R_false_lit [sym "false"]]) e_false
    | D_name : forall x,
        tag_lookup tags x = None ->
        Den (ident x) (e_fvar_f (var_of x))
    | D_expr : forall cs e,
        Den_block cs e ->
        Den (Node R_expr cs) e
    | D_value : forall cs e,
        Den_math cs e ->
        Den (Node R_value cs) e
    | D_function : forall kw ps xs cs body,
        Den_params ps xs ->
        Den (Node R_expr cs) body ->
        Den (Node R_function [Leaf kw; sym "("; Node R_params ps; sym ")";
                              sym "do"; Node R_expr cs; sym "done"])
            (curry (List.map var_of xs) body)
    | D_record : forall items fs,
        Den_items items fs ->
        Den (Node R_record (sym "{" :: items)) (e_rec fs)
    | D_spread_record : forall cs base rest fs,
        Den (Node R_expr cs) base ->
        Den_sep rest fs ->
        Den (Node R_record
               (sym "{" :: Node R_spread [sym "..."; Node R_expr cs] :: rest))
            (spread_nest base fs)
    | D_destructure : forall ps xs ro vs semi cs v body s,
        Den_pat_start ps xs ro ->
        (semi = [] \/ semi = [sym ";"]) ->
        Den (Node R_value vs) v ->
        Den (Node R_expr cs) body ->
        ~ AtomSetImpl.In s (fv_exp body) ->
        (forall x, List.In x (xs ++ match ro with Some r => [r] | None => [] end) ->
                   s <> var_of x) ->
        Den (Node R_destructure
               ([Node R_record_pattern (sym "{" :: ps); sym "="; Node R_value vs]
                  ++ semi ++ [Node R_expr cs]))
            (e_let v (close_exp s (unpack s xs ro body)))
    | D_local : forall d x v cs body,
        Den_decl d x v ->
        is_fn_decl d = false ->
        Den (Node R_expr cs) body ->
        Den (Node R_local [d; Node R_expr cs])
            (e_let v (close_exp (var_of x) body))
    | D_str : forall q,
        Den (Node R_string [Leaf TStr]) (e_str q)
    | D_cond : forall cs1 cs2 cs3 e1 e2 e3,
        Den (Node R_expr cs1) e1 ->
        Den (Node R_expr cs2) e2 ->
        Den (Node R_expr cs3) e3 ->
        Den (Node R_conditional [sym "if"; Node R_expr cs1; sym "then";
                                 Node R_expr cs2; sym "else"; Node R_expr cs3; sym "done"])
            (e_ite e1 e2 e3)
    | D_cond_noelse : forall cs1 cs2 e1 e2,
        Den (Node R_expr cs1) e1 ->
        Den (Node R_expr cs2) e2 ->
        Den (Node R_conditional [sym "if"; Node R_expr cs1; sym "then";
                                 Node R_expr cs2; sym "done"])
            (e_ite e1 e2 e_unit)
    | D_neg_int : forall n,
        Den (Node R_negation [op_tree bop_sub; Node R_number [Leaf (TNum n)]])
            (e_num (Stdlib.ZArith.BinInt.Z.opp (z_of_nat n)))
    | D_neg_dec : forall d,
        Den (Node R_negation [op_tree bop_sub; Node R_number [Leaf (TDec d)]])
            (e_dec d)
    | D_neg_chain : forall cs e,
        Den_chain cs e ->
        ~ bare_number cs ->
        Den (Node R_negation (op_tree bop_sub :: cs)) (e_bin (e_num 0) bop_sub e)
    | D_neg_neg : forall cs e,
        Den (Node R_negation cs) e ->
        Den (Node R_negation [op_tree bop_sub; Node R_negation cs])
            (e_bin (e_num 0) bop_sub e)
    | D_list_nil : forall we tge,
        tag_lookup tags "Empty" = Some (we, tge) ->
        Den (Node R_list [sym "["; sym "]"]) (e_con we tge e_unit)
    | D_list : forall args es we tge wl tgl,
        tag_lookup tags "Empty" = Some (we, tge) ->
        tag_lookup tags "Link" = Some (wl, tgl) ->
        Den_args args es ->
        Den (Node R_list [sym "["; Node R_arguments args; sym "]"])
            (list_of we tge wl tgl es)
    | D_match_tags : forall cs1 a rest e w tg b ars,
        Den (Node R_expr cs1) e ->
        Den_arm a w tg b ->
        Den_arms rest ars ->
        Den (Node R_match_expr
               ([sym "match"; Node R_expr cs1; sym "do"] ++ a :: rest ++ [sym "done"]))
            (e_match w e (arms_cons tg b ars))
    | D_match_lit_var : forall cs1 x a rest rows els,
        Den (Node R_expr cs1) (e_fvar_f x) ->
        Den_lit_arms (a :: rest) rows els ->
        Den (Node R_match_expr
               ([sym "match"; Node R_expr cs1; sym "do"] ++ a :: rest ++ [sym "done"]))
            (lit_chain (e_fvar_f x) rows els)
    | D_match_lit_let : forall cs1 e s a rest rows els,
        Den (Node R_expr cs1) e ->
        (forall x, e <> e_fvar_f x) ->
        Den_lit_arms (a :: rest) rows els ->
        ~ AtomSetImpl.In s (fv_rows rows `union` fv_exp els) ->
        Den (Node R_match_expr
               ([sym "match"; Node R_expr cs1; sym "do"] ++ a :: rest ++ [sym "done"]))
            (e_let e (close_exp s (lit_chain (e_fvar_f s) rows els)))
  with Den_decl : tree -> string -> exp -> Prop :=
    | DD_plain : forall x cs v,
        Den (Node R_value cs) v ->
        Den_decl (Node R_declaration [ident x; sym "="; Node R_value cs]) x v
    | DD_semi : forall x cs v,
        Den (Node R_value cs) v ->
        Den_decl (Node R_declaration [ident x; sym "="; Node R_value cs; sym ";"]) x v
  with Den_block : list tree -> exp -> Prop :=
    | DB_chain : forall cs e,
        Den_math cs e ->
        Den_block cs e
    | DB_decl : forall d rest x v body,
        Den_decl d x v ->
        is_fn_decl d = false ->
        Den_block rest body ->
        Den_block (d :: rest) (e_let v (close_exp (var_of x) body))
    | DB_group : forall ds xs vs rest body,
        Den_decls ds xs vs ->
        ds <> [] ->
        Den_block rest body ->
        Den_block (ds ++ rest)
          (e_letrec (group_fields (List.map var_of xs) vs)
                    (bind_group (List.map var_of xs) body))
  with Den_decls : list tree -> list string -> list exp -> Prop :=
    | DDs_nil :
        Den_decls [] [] []
    | DDs_cons : forall d x v ds xs vs,
        Den_decl d x v ->
        is_fn_decl d = true ->
        Den_decls ds xs vs ->
        Den_decls (d :: ds) (x :: xs) (v :: vs)
  with Den_math : list tree -> exp -> Prop :=
    | DM_run : forall cs is e,
        Den_run cs is ->
        resolve is = Some e ->
        Den_math cs e
  with Den_opd : list tree -> list item -> Prop :=
    | DO_val : forall cs e,
        Den_chain cs e ->
        Den_opd cs [I_val e]
    | DO_not : forall cs is,
        Den_opd cs is ->
        Den_opd (not_tree :: cs) (I_not :: is)
  with Den_run : list tree -> list item -> Prop :=
    | DR_one : forall cs is,
        Den_opd cs is ->
        Den_run cs is
    | DR_more : forall c1 is1 o c2 is2,
        Den_opd c1 is1 ->
        o <> L_not ->
        Den_run c2 is2 ->
        Den_run (c1 ++ lop_tree o :: c2) (is1 ++ I_op o :: is2)
  with Den_chain : list tree -> exp -> Prop :=
    | DC_head : forall t rest e0 e,
        Den t e0 ->
        Den_posts e0 rest e ->
        Den_chain (t :: rest) e
    | DC_paren : forall cs rest e0 e,
        Den (Node R_expr cs) e0 ->
        Den_posts e0 rest e ->
        Den_chain (sym "(" :: Node R_expr cs :: sym ")" :: rest) e
    | DC_tag : forall x w tg rest e,
        tag_lookup tags x = Some (w, tg) ->
        ~ starts_call rest ->
        Den_posts (e_con w tg e_unit) rest e ->
        Den_chain (ident x :: rest) e
    | DC_tag_call : forall x w tg args es rest e,
        tag_lookup tags x = Some (w, tg) ->
        Den_args args es ->
        Den_posts (e_con w tg (payload es)) rest e ->
        Den_chain (ident x :: Node R_call [sym "("; Node R_arguments args; sym ")"] :: rest) e
  with Den_posts : exp -> list tree -> exp -> Prop :=
    | DP_nil : forall e,
        Den_posts e [] e
    | DP_access : forall e l rest e',
        ~ starts_call rest ->
        Den_posts (e_proj e (lab l)) rest e' ->
        Den_posts e (Node R_access [sym "."; ident l] :: rest) e'
    | DP_take : forall e l rest e',
        Den_posts (e_proj e (lab l)) rest e' ->
        Den_posts e (Node R_take [sym "::"; ident l] :: rest) e'
    | DP_dot_path : forall e l args es rest e',
        is_path e = true ->
        Den_args args es ->
        Den_posts (apps (e_proj e (lab l)) (e :: es)) rest e' ->
        Den_posts e
          (Node R_access [sym "."; ident l]
             :: Node R_call [sym "("; Node R_arguments args; sym ")"] :: rest) e'
    | DP_dot_bind : forall e s l args es rest e',
        is_path e = false ->
        Forall (fun a => ~ AtomSetImpl.In s (fv_exp a)) es ->
        Den_args args es ->
        Den_posts (e_let e (close_exp s (apps (e_proj (e_fvar_f s) (lab l))
                                             (e_fvar_f s :: es)))) rest e' ->
        Den_posts e
          (Node R_access [sym "."; ident l]
             :: Node R_call [sym "("; Node R_arguments args; sym ")"] :: rest) e'
    | DP_call : forall e args es rest e',
        Den_args args es ->
        Den_posts (apps e es) rest e' ->
        Den_posts e (Node R_call [sym "("; Node R_arguments args; sym ")"] :: rest) e'
  with Den_args : list tree -> list exp -> Prop :=
    | DA_last : forall t e,
        Den t e ->
        Den_args [t] [e]
    | DA_trailing : forall t e,
        Den t e ->
        Den_args [t; sym ","] [e]
    | DA_more : forall t e rest es,
        Den t e ->
        Den_args rest es ->
        Den_args (t :: sym "," :: rest) (e :: es)
  with Den_params : list tree -> list string -> Prop :=
    | DPa_one : forall x,
        Den_params [ident x] [x]
    | DPa_more : forall x rest xs,
        Den_params rest xs ->
        Den_params (ident x :: sym "," :: rest) (x :: xs)
  with Den_items : list tree -> fields -> Prop :=
    | DI_end :
        Den_items [sym "}"] fs_nil
    | DI_field : forall f l e rest fs,
        Den_field f l e ->
        Den_sep rest fs ->
        Den_items (f :: rest) (fs_cons (lab l) e fs)
  with Den_sep : list tree -> fields -> Prop :=
    | DS_end :
        Den_sep [sym "}"] fs_nil
    | DS_more : forall rest fs,
        Den_items rest fs ->
        Den_sep (sym "," :: rest) fs
  with Den_field : tree -> string -> exp -> Prop :=
    | DF : forall l cs e,
        Den (Node R_expr cs) e ->
        Den_field (Node R_field [ident l; sym ":"; Node R_expr cs]) l e
  with Den_arm : tree -> gdecl -> nat -> exp -> Prop :=
    | DArm : forall pcs t xs cs body w tg s,
        Den_tpat pcs t xs ->
        tag_lookup tags t = Some (w, tg) ->
        Den (Node R_expr cs) body ->
        ~ AtomSetImpl.In s (fv_exp body) ->
        (forall x, List.In x xs -> s <> var_of x) ->
        Den_arm (Node R_arm [Node R_pattern pcs; sym "then"; Node R_expr cs])
                w tg (close_exp s (slot_lets var_of s 0 xs body))
  with Den_arms : list tree -> arms -> Prop :=
    | DAr_nil : Den_arms [] arms_nil
    | DAr_else : forall cs e,
        Den (Node R_expr cs) e ->
        Den_arms [sym "else"; Node R_expr cs] (arms_else e)
    | DAr_cons : forall a w tg b rest ars,
        Den_arm a w tg b ->
        Den_arms rest ars ->
        Den_arms (a :: rest) (arms_cons tg b ars)
  with Den_lit_arm : tree -> exp -> exp -> Prop :=
    | DLA : forall c cs l b,
        Den c l ->
        Den (Node R_expr cs) b ->
        Den_lit_arm (Node R_arm [Node R_literal_pattern [c]; sym "then"; Node R_expr cs]) l b
  with Den_lit_arms : list tree -> list (exp * exp) -> exp -> Prop :=
    | DLs_else : forall cs e,
        Den (Node R_expr cs) e ->
        Den_lit_arms [sym "else"; Node R_expr cs] [] e
    | DLs_cons : forall a l b rest rows els,
        Den_lit_arm a l b ->
        Den_lit_arms rest rows els ->
        Den_lit_arms (a :: rest) ((l, b) :: rows) els.

End Denotation.

(* A chain, and one infix operator between two chains, read as before. *)
Lemma DM_chain : forall `{TT : TagTable} var_of tbl cs e,
  Den_chain var_of tbl cs e -> Den_math var_of tbl cs e.
Proof.
  intros TT var_of tbl cs e H.
  apply (DM_run var_of tbl cs [I_val e] e); [ | reflexivity ].
  apply DR_one. apply DO_val. exact H.
Qed.

Lemma DM_bin : forall `{TT : TagTable} var_of tbl c1 c2 o e1 e2,
  Den_chain var_of tbl c1 e1 ->
  Den_chain var_of tbl c2 e2 ->
  Den_math var_of tbl (c1 ++ op_tree o :: c2) (e_bin e1 o e2).
Proof.
  intros TT var_of tbl c1 c2 o e1 e2 H1 H2.
  apply (DM_run var_of tbl _ [I_val e1; I_op (L_bin o); I_val e2]);
    [ | reflexivity ].
  change (op_tree o) with (lop_tree (L_bin o)).
  apply (DR_more var_of tbl c1 [I_val e1] (L_bin o) c2 [I_val e2]);
    [ apply DO_val; exact H1 | discriminate | apply DR_one; apply DO_val; exact H2 ].
Qed.

Scheme Den_ind' := Induction for Den Sort Prop
with Den_decl_ind' := Induction for Den_decl Sort Prop
with Den_block_ind' := Induction for Den_block Sort Prop
with Den_decls_ind' := Induction for Den_decls Sort Prop
with Den_math_ind' := Induction for Den_math Sort Prop
with Den_opd_ind' := Induction for Den_opd Sort Prop
with Den_run_ind' := Induction for Den_run Sort Prop
with Den_chain_ind' := Induction for Den_chain Sort Prop
with Den_posts_ind' := Induction for Den_posts Sort Prop
with Den_args_ind' := Induction for Den_args Sort Prop
with Den_params_ind' := Induction for Den_params Sort Prop
with Den_items_ind' := Induction for Den_items Sort Prop
with Den_sep_ind' := Induction for Den_sep Sort Prop
with Den_field_ind' := Induction for Den_field Sort Prop
with Den_arm_ind' := Induction for Den_arm Sort Prop
with Den_arms_ind' := Induction for Den_arms Sort Prop
with Den_lit_arm_ind' := Induction for Den_lit_arm Sort Prop
with Den_lit_arms_ind' := Induction for Den_lit_arms Sort Prop.
Combined Scheme Den_mutind from Den_ind', Den_decl_ind', Den_block_ind',
  Den_decls_ind', Den_math_ind', Den_opd_ind', Den_run_ind', Den_chain_ind', Den_posts_ind', Den_args_ind', Den_params_ind',
  Den_items_ind', Den_sep_ind', Den_field_ind', Den_arm_ind', Den_arms_ind',
  Den_lit_arm_ind', Den_lit_arms_ind'.

(* ---- T1, the denotation half: whatever a derivation denotes is locally closed ---- *)

Lemma den_lc : forall `{TT : TagTable} var_of tbl,
  (forall t e, Den var_of tbl t e -> lc e) /\
  (forall d x v, Den_decl var_of tbl d x v -> lc v) /\
  (forall cs e, Den_block var_of tbl cs e -> lc e) /\
  (forall cs xs vs, Den_decls var_of tbl cs xs vs -> Forall lc vs) /\
  (forall cs e, Den_math var_of tbl cs e -> lc e) /\
  (forall cs is, Den_opd var_of tbl cs is -> Forall item_lc is) /\
  (forall cs is, Den_run var_of tbl cs is -> Forall item_lc is) /\
  (forall cs e, Den_chain var_of tbl cs e -> lc e) /\
  (forall e0 cs e, Den_posts var_of tbl e0 cs e -> lc e0 -> lc e) /\
  (forall cs es, Den_args var_of tbl cs es -> Forall lc es) /\
  (forall ps xs, Den_params var_of tbl ps xs -> True) /\
  (forall cs fs, Den_items var_of tbl cs fs -> lcf fs) /\
  (forall cs fs, Den_sep var_of tbl cs fs -> lcf fs) /\
  (forall f l e, Den_field var_of tbl f l e -> lc e) /\
  (forall a w tg b, Den_arm var_of tbl a w tg b -> lc_at 1 b) /\
  (forall cs ars, Den_arms var_of tbl cs ars -> lca ars) /\
  (forall a l b, Den_lit_arm var_of tbl a l b -> lc l /\ lc b) /\
  (forall cs rows els, Den_lit_arms var_of tbl cs rows els ->
     Forall (fun r => lc (fst r) /\ lc (snd r)) rows /\ lc els).
Proof.
  intros TT var_of tbl.
  apply Den_mutind.
  - (* num *) intros n. exact I.
  - (* dec *) intros d. exact I.
  - (* true *) exact I.
  - (* false *) exact I.
  - (* name *) intros x _. exact I.
  - (* expr *) intros cs e Hblock IH. exact IH.
  - (* value *) intros cs e Hchain IH. exact IH.
  - (* function *)
    intros kw ps xs cs body Hps _ Hbody IHbody.
    assert (Hcurry : lc (curry (List.map var_of xs) body))
      by (apply lc_curry; exact IHbody).
    exact Hcurry.
  - (* record *) intros items fs Hitems IH. exact IH.
  - (* record with a spread: the nest of single spreads *)
    intros cs base rest fs Hbase IHbase Hsep IHsep.
    exact (lc_spread_nest fs base IHbase IHsep).
  - (* destructuring *)
    intros ps xs ro vs semi cs v body s Hpat Hsemi Hv IHv Hbody IHbody Hfresh Hdistinct.
    assert (Hclose : lc_at 1 (close_exp s (unpack var_of tbl s xs ro body)))
      by (apply (proj1 lc_close_mut); exact (lc_unpack var_of tbl s xs ro body IHbody)).
    exact (conj IHv Hclose).
  - (* local *)
    intros d x v cs body Hd IHd _ Hbody IHbody.
    assert (Hclose : lc_at 1 (close_exp (var_of x) body))
      by (apply (proj1 lc_close_mut); exact IHbody).
    exact (conj IHd Hclose).
  - (* string *) intros q. exact I.
  - (* conditional *)
    intros cs1 cs2 cs3 e1 e2 e3 H1 IH1 H2 IH2 H3 IH3. exact (conj IH1 (conj IH2 IH3)).
  - (* conditional, no else: the missing branch is the unit value *)
    intros cs1 cs2 e1 e2 H1 IH1 H2 IH2. exact (conj IH1 (conj IH2 I)).
  - (* negation of a whole number *) intros n. exact I.
  - (* negation of a decimal *) intros d. exact I.
  - (* negation: 0 - x *)
    intros cs e Hchain IH Hbare. exact (conj I IH).
  - (* negation of a negation *)
    intros cs e Hneg IH. exact (conj I IH).
  - (* empty list *) intros we tge _. exact I.
  - (* list literal *)
    intros args es we tge wl tgl _ _ Hargs IH. exact (lc_list_of we tge wl tgl es IH).
  - (* match on tags *)
    intros cs1 a rest e w tg b ars He IHe Ha IHa Hrest IHrest.
    exact (conj IHe (conj IHa IHrest)).
  - (* match on literals, scrutinee a variable *)
    intros cs1 x a rest rows els Hs IHs Harms [IHrows IHels].
    exact (lc_lit_chain (e_fvar_f x) rows els I IHrows IHels).
  - (* match on literals, scrutinee bound once *)
    intros cs1 e s a rest rows els He IHe Hnotvar Harms [IHrows IHels] Hfresh.
    assert (Hchain : lc (lit_chain (e_fvar_f s) rows els))
      by exact (lc_lit_chain (e_fvar_f s) rows els I IHrows IHels).
    assert (Hclose : lc_at 1 (close_exp s (lit_chain (e_fvar_f s) rows els)))
      by (apply (proj1 lc_close_mut); exact Hchain).
    exact (conj IHe Hclose).
  - (* decl, plain *) intros x cs v Hv IH. exact IH.
  - (* decl, with semicolon *) intros x cs v Hv IH. exact IH.
  - (* block, chain *) intros cs e Hmath IH. exact IH.
  - (* block, declaration *)
    intros d rest x v body Hd IHd _ Hrest IHrest.
    assert (Hclose : lc_at 1 (close_exp (var_of x) body))
      by (apply (proj1 lc_close_mut); exact IHrest).
    exact (conj IHd Hclose).
  - (* block, recursive group *)
    intros ds xs vs rest body Hds IHds _ Hrest IHrest.
    split.
    + exact (lcf_group_fields _ _ IHds).
    + exact (proj1 lc_bind_group_mut body 0 _ IHrest).
  - (* decls, none *) apply Forall_nil.
  - (* decls, one more *)
    intros d x v ds xs vs Hd IHd _ Hds IHds. exact (Forall_cons v IHd IHds).
  - (* math: the run resolved *)
    intros cs is e Hrun IH Hres. exact (resolve_lc is e IH Hres).
  - (* operand, a chain *)
    intros cs e Hchain IH. exact (Forall_cons (I_val e) IH (Forall_nil _)).
  - (* operand, behind a not *)
    intros cs is Hopd IH. exact (Forall_cons I_not I IH).
  - (* run, one operand *)
    intros cs is Hopd IH. exact IH.
  - (* run, an operator and more *)
    intros c1 is1 o c2 is2 Hopd IH1 Hne Hrun IH2.
    apply Forall_app. split; [ exact IH1 | exact (Forall_cons (I_op o) I IH2) ].
  - (* chain, head *)
    intros t rest e0 e Ht IHt Hposts IHposts. exact (IHposts IHt).
  - (* chain, parenthesised *)
    intros cs rest e0 e Hexpr IHexpr Hposts IHposts. exact (IHposts IHexpr).
  - (* chain, a tag with no payload *)
    intros x w tg rest e Hlookup Hnocall Hposts IHposts. exact (IHposts I).
  - (* chain, a tag with a payload *)
    intros x w tg args es rest e Hlookup Hargs IHargs Hposts IHposts.
    exact (IHposts (lc_payload es IHargs)).
  - (* posts, none *) intros e Hlc. exact Hlc.
  - (* posts, access *)
    intros e l rest e' Hnocall Hrest IHrest Hlc.
    assert (Hproj : lc (e_proj e (lab tbl l))) by exact Hlc.
    exact (IHrest Hproj).
  - (* posts, take *)
    intros e l rest e' Hrest IHrest Hlc.
    assert (Hproj : lc (e_proj e (lab tbl l))) by exact Hlc.
    exact (IHrest Hproj).
  - (* posts, dot call on a path: the receiver is repeated and passed first *)
    intros e l args es rest e' Hpath Hargs IHargs Hrest IHrest Hlc.
    assert (Hrecv : Forall lc (e :: es)) by (apply Forall_cons; assumption).
    assert (Happs : lc (apps (e_proj e (lab tbl l)) (e :: es)))
      by (apply lc_apps; [ exact Hlc | exact Hrecv ]).
    exact (IHrest Happs).
  - (* posts, dot call on another receiver: bound once to a hidden name *)
    intros e s l args es rest e' Hnotpath Hfresh Hargs IHargs Hrest IHrest Hlc.
    assert (Hrecv : Forall lc (e_fvar_f s :: es))
      by (apply Forall_cons; [ exact I | exact IHargs ]).
    assert (Happs : lc (apps (e_proj (e_fvar_f s) (lab tbl l)) (e_fvar_f s :: es)))
      by (apply lc_apps; [ exact I | exact Hrecv ]).
    assert (Hclose : lc_at 1 (close_exp s (apps (e_proj (e_fvar_f s) (lab tbl l))
                                              (e_fvar_f s :: es))))
      by (apply (proj1 lc_close_mut); exact Happs).
    exact (IHrest (conj Hlc Hclose)).
  - (* posts, call *)
    intros e args es rest e' Hargs IHargs Hrest IHrest Hlc.
    assert (Happs : lc (apps e es)) by (apply lc_apps; assumption).
    exact (IHrest Happs).
  - (* args, last *) intros t e Ht IH. exact (Forall_cons e IH (Forall_nil lc)).
  - (* args, trailing comma *) intros t e Ht IH. exact (Forall_cons e IH (Forall_nil lc)).
  - (* args, more *)
    intros t e rest es Ht IHt Hrest IHrest. exact (Forall_cons e IHt IHrest).
  - (* params, one *) intros x. exact I.
  - (* params, more *) intros x rest xs Hrest IH. exact I.
  - (* items, end *) exact I.
  - (* items, field *)
    intros f l e rest fs Hf IHf Hsep IHsep. exact (conj IHf IHsep).
  - (* sep, end *) exact I.
  - (* sep, more *) intros rest fs Hitems IH. exact IH.
  - (* field *) intros l cs e Hexpr IH. exact IH.
  - (* arm: the payload variable is closed over the slot bindings *)
    intros pcs t xs cs body w tg s Hpat Hlookup Hbody IHbody Hfresh Hdistinct.
    exact (proj1 lc_close_mut _ 0 s (lc_slot_lets var_of xs s 0 body IHbody)).
  - (* arms, none *) exact I.
  - (* arms, else *) intros cs e He IH. exact IH.
  - (* arms, one more *)
    intros a w tg b rest ars Ha IHa Hrest IHrest. exact (conj IHa IHrest).
  - (* literal arm *) intros c cs l b Hc IHc Hb IHb. exact (conj IHc IHb).
  - (* literal arms, else *)
    intros cs e He IH. exact (conj (Forall_nil _) IH).
  - (* literal arms, one more *)
    intros a l b rest rows els Ha [IHl IHb] Hrest [IHrows IHels].
    exact (conj (Forall_cons (l, b) (conj IHl IHb) IHrows) IHels).
Qed.

(* ---- the generated local-closure predicate ---- *)

(* The soundness development reads local closure off [lc_at]; the generated
   [lc_exp] (universal binder clause) is the one ADR 0030 names. They agree on
   locally closed terms. *)

Fixpoint size (e : exp) : nat :=
  match e with
  | e_fvar_b _ | e_fvar_f _ | e_num _ | e_dec _ | e_true | e_false | e_unit | e_str _ => 1
  | e_abs b => S (size b)
  | e_app a b | e_let a b => S (size a + size b)
  | e_letrec fs b => S (size_fields fs + size b)
  | e_rec fs => S (size_fields fs)
  | e_proj a _ => S (size a)
  | e_ite a b c => S (size a + size b + size c)
  | e_bin a _ b => S (size a + size b)
  | e_tofloat a => S (size a)
  | e_con _ _ a => S (size a)
  | e_match _ a ars => S (size a + size_arms ars)
  | e_spread a _ b => S (size a + size b)
  | e_restrict a _ => S (size a)
  | e_fold a => S (size a)
  | e_unfold a => S (size a)
  end
with size_fields (fs : fields) : nat :=
  match fs with
  | fs_nil => 1
  | fs_cons _ e fs' => S (size e + size_fields fs')
  | fs_meth _ e fs' => S (size e + size_fields fs')
  end
with size_arms (ars : arms) : nat :=
  match ars with
  | arms_nil => 1
  | arms_else e => S (size e)
  | arms_cons _ e ars' => S (size e + size_arms ars')
  end.

Lemma open_size_mut :
  (forall e k x, size (open_exp_wrt_exp_rec k (e_fvar_f x) e) = size e) /\
  (forall fs k x, size_fields (open_fields_wrt_exp_rec k (e_fvar_f x) fs) = size_fields fs) /\
  (forall ars k x, size_arms (open_arms_wrt_exp_rec k (e_fvar_f x) ars) = size_arms ars).
Proof.
  apply exp_fields_mutind; simpl; intros.
  - (* bound index *)
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* abs *) rewrite H. reflexivity.
  - (* app *) rewrite H, H0. reflexivity.
  - (* let *) rewrite H, H0. reflexivity.
  - (* letrec *) rewrite H, H0. reflexivity.
  - (* rec *) rewrite H. reflexivity.
  - (* proj *) rewrite H. reflexivity.
  - reflexivity.
  - reflexivity.
  - (* ite *) rewrite H, H0, H1. reflexivity.
  - (* bin *) rewrite H, H0. reflexivity.
  - (* tofloat *) rewrite H. reflexivity.
  - (* con *) rewrite H. reflexivity.
  - (* match *) rewrite H, H0. reflexivity.
  - (* spread *) rewrite H, H0. reflexivity.
  - (* restrict *) rewrite H. reflexivity.
  - (* fold *) rewrite H. reflexivity.
  - (* unfold *) rewrite H. reflexivity.
  - reflexivity.
  - (* cons *) rewrite H, H0. reflexivity.
  - (* cons *) rewrite H, H0. reflexivity.
  - reflexivity.
  - (* else *) rewrite H. reflexivity.
  - (* arm *) rewrite H, H0. reflexivity.
Qed.

Lemma open_lc_at_mut :
  (forall e n x, lc_at (S n) e -> lc_at n (open_exp_wrt_exp_rec n (e_fvar_f x) e)) /\
  (forall fs n x, lcf_at (S n) fs -> lcf_at n (open_fields_wrt_exp_rec n (e_fvar_f x) fs)) /\
  (forall ars n x, lca_at (S n) ars -> lca_at n (open_arms_wrt_exp_rec n (e_fvar_f x) ars)).
Proof.
  apply exp_fields_mutind; simpl; intros.
  - (* bound index *)
    destruct (lt_eq_lt_dec n n0) as [[Hlt | Heq] | Hgt]; simpl; [ exact Hlt | exact I | lia ].
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - (* abs *) apply H. assumption.
  - (* app *) destruct H1 as [Ha Hb]. split; [ apply H | apply H0 ]; assumption.
  - (* let *) destruct H1 as [Ha Hb]. split; [ apply H | apply H0 ]; assumption.
  - (* letrec *) destruct H1 as [Ha Hb]. split; [ apply H | apply H0 ]; assumption.
  - (* rec *) apply H. assumption.
  - (* proj *) apply H. assumption.
  - exact I.
  - exact I.
  - (* ite *) destruct H2 as [Ha [Hb Hc]]. split; [ apply H | split; [ apply H0 | apply H1 ] ]; assumption.
  - (* bin *) destruct H1 as [Ha Hb]. split; [ apply H | apply H0 ]; assumption.
  - (* tofloat *) apply H. assumption.
  - (* con *) apply H. assumption.
  - (* match *) destruct H1 as [Ha Hb]. split; [ apply H | apply H0 ]; assumption.
  - (* spread *) destruct H1 as [Ha Hb]. split; [ apply H | apply H0 ]; assumption.
  - (* restrict *) apply H. assumption.
  - (* fold *) apply H. assumption.
  - (* unfold *) apply H. assumption.
  - exact I.
  - (* cons *) destruct H1 as [He Hfs]. split; [ apply H | apply H0 ]; assumption.
  - (* cons *) destruct H1 as [He Hfs]. split; [ apply H | apply H0 ]; assumption.
  - exact I.
  - (* else *) apply H. assumption.
  - (* arm *) destruct H1 as [He Hars]. split; [ apply H | apply H0 ]; assumption.
Qed.

Lemma lc_lc_exp_bounded : forall m,
  (forall e, size e <= m -> lc e -> lc_exp e) /\
  (forall fs, size_fields fs <= m -> lcf fs -> lc_fields fs) /\
  (forall ars, size_arms ars <= m -> lca ars -> lc_arms ars).
Proof.
  induction m as [| m IH]; split; [ | split | | split ]; intros t Hsize Hlc.
  - destruct t; simpl in Hsize; lia.
  - destruct t; simpl in Hsize; lia.
  - destruct t; simpl in Hsize; lia.
  - destruct IH as [IHe [IHfs IHars]].
    destruct t as [i | x | n | d | | | b | a b | a b | fs0 b0 | fs | a l | | q | a b c | a o b | a | w tg a0 | w a0 ars | a3 l3 a4 | a5 l5 | a1 | a2];
      unfold lc, lcf in Hlc; simpl in Hsize, Hlc.
    + lia.
    + apply lc_e_fvar_f.
    + apply lc_e_num.
    + apply lc_e_dec.
    + apply lc_e_true.
    + apply lc_e_false.
    + (* abs *)
      apply lc_e_abs. intros x.
      assert (Hopen : lc (open_exp_wrt_exp b (e_fvar_f x)))
        by (apply (proj1 open_lc_at_mut); exact Hlc).
      assert (Hsmaller : size (open_exp_wrt_exp b (e_fvar_f x)) <= m)
        by (unfold open_exp_wrt_exp; rewrite (proj1 open_size_mut); lia).
      exact (IHe _ Hsmaller Hopen).
    + (* app *)
      destruct Hlc as [Ha Hb].
      apply lc_e_app; [ apply IHe | apply IHe ]; try assumption; lia.
    + (* let *)
      destruct Hlc as [Ha Hb].
      apply lc_e_let.
      * apply IHe; [ lia | exact Ha ].
      * intros x.
        assert (Hopen : lc (open_exp_wrt_exp b (e_fvar_f x)))
          by (apply (proj1 open_lc_at_mut); exact Hb).
        assert (Hsmaller : size (open_exp_wrt_exp b (e_fvar_f x)) <= m)
          by (unfold open_exp_wrt_exp; rewrite (proj1 open_size_mut); lia).
        exact (IHe _ Hsmaller Hopen).
    + (* letrec *)
      destruct Hlc as [Hfs Hb].
      apply lc_e_letrec.
      * intros x.
        assert (Hopen : lcf (open_fields_wrt_exp fs0 (e_fvar_f x)))
          by (apply (proj1 (proj2 open_lc_at_mut)); exact Hfs).
        assert (Hsmaller : size_fields (open_fields_wrt_exp fs0 (e_fvar_f x)) <= m)
          by (unfold open_fields_wrt_exp; rewrite (proj1 (proj2 open_size_mut)); lia).
        exact (IHfs _ Hsmaller Hopen).
      * intros x.
        assert (Hopen : lc (open_exp_wrt_exp b0 (e_fvar_f x)))
          by (apply (proj1 open_lc_at_mut); exact Hb).
        assert (Hsmaller : size (open_exp_wrt_exp b0 (e_fvar_f x)) <= m)
          by (unfold open_exp_wrt_exp; rewrite (proj1 open_size_mut); lia).
        exact (IHe _ Hsmaller Hopen).
    + (* rec *)
      apply lc_e_rec. apply IHfs; [ lia | exact Hlc ].
    + (* proj *)
      apply lc_e_proj. apply IHe; [ lia | exact Hlc ].
    + apply lc_e_unit.
    + apply lc_e_str.
    + (* ite *)
      destruct Hlc as [Ha [Hb Hc]].
      apply lc_e_ite; apply IHe; try assumption; lia.
    + (* bin *)
      destruct Hlc as [Ha Hb].
      apply lc_e_bin; apply IHe; try assumption; lia.
    + (* tofloat *)
      apply lc_e_tofloat. apply IHe; [ lia | exact Hlc ].
    + (* tag construction *)
      apply lc_e_con. apply IHe; [ lia | exact Hlc ].
    + (* match *)
      destruct Hlc as [Ha Hars].
      apply lc_e_match.
      * apply IHe; [ lia | exact Ha ].
      * apply IHars; [ lia | exact Hars ].
    + (* spread *)
      destruct Hlc as [Ha Hb].
      apply lc_e_spread; apply IHe; try assumption; lia.
    + (* restrict *)
      apply lc_e_restrict. apply IHe; [ lia | exact Hlc ].
    + (* fold *)
      apply lc_e_fold. apply IHe; [ lia | exact Hlc ].
    + (* unfold *)
      apply lc_e_unfold. apply IHe; [ lia | exact Hlc ].
  - destruct IH as [IHe [IHfs IHars]].
    destruct t as [| l e fs | l e fs]; unfold lc, lcf in Hlc; simpl in Hsize, Hlc.
    + apply lc_fs_nil.
    + destruct Hlc as [He Hfs].
      apply lc_fs_cons; [ apply IHe | apply IHfs ]; try assumption; lia.
    + destruct Hlc as [He Hfs].
      apply lc_fs_meth; [ apply IHe | apply IHfs ]; try assumption; lia.
  - destruct IH as [IHe [IHfs IHars]].
    destruct t as [| e | tg e ars]; unfold lca in Hlc; simpl in Hsize, Hlc.
    + apply lc_arms_nil.
    + apply lc_arms_else. apply IHe; [ lia | exact Hlc ].
    + destruct Hlc as [He Hars].
      apply lc_arms_cons.
      * intros x.
        assert (Hopen : lc (open_exp_wrt_exp e (e_fvar_f x)))
          by (apply (proj1 open_lc_at_mut); exact He).
        assert (Hsmaller : size (open_exp_wrt_exp e (e_fvar_f x)) <= m)
          by (unfold open_exp_wrt_exp; rewrite (proj1 open_size_mut); lia).
        exact (IHe _ Hsmaller Hopen).
      * apply IHars; [ lia | exact Hars ].
Qed.

Lemma lc_lc_exp : forall e, lc e -> lc_exp e.
Proof.
  intros e Hlc.
  exact (proj1 (lc_lc_exp_bounded (size e)) e (le_n _) Hlc).
Qed.
