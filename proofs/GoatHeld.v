(* Held equations (ADR 0033 amendment, issue 667).

   A spread onto a record whose row may or may not have the label gives the
   entry [l ^ p : y] its own field variable [y] and holds the equation
   [p => y = T], where [T] is the type of the spread's value.  The algorithm
   returns the equations it holds, [heq]s, with each result; a substitution
   applies to them ([apH]).  A substitution [S] solves one when [S p] is
   [Bool] (the entry is absent) or when [S y] and [S T] are the same type.

   [dis] decides a list of equations once the context that could settle their
   presences is no longer open: each equation whose presence is not already
   [Bool] is unified, and an equation whose two sides can never be the same
   makes its presence [Bool] when the rest of its row lacks the label. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatInfer.
Require Import Stdlib.Lists.List.
Import ListNotations.

Record heq : Type := Heq { h_lbl : label; h_pres : typ; h_fld : typ; h_val : typ; h_rest : row }.

Definition apE (s : sub) (h : heq) : heq :=
  Heq (h_lbl h) (apT s (h_pres h)) (apT s (h_fld h)) (apT s (h_val h)) (apR s (h_rest h)).

Definition apH (s : sub) (H : list heq) : list heq := map (apE s) H.

Definition solves1 (D : denv) (h : heq) : Prop :=
  h_pres h = typ_Bool \/ teqD D (h_fld h) (h_val h).

(* [S] solves [H] at [D]: the equations of [H] hold of what [S] makes of them. *)
Definition Sol (D : denv) (S : sub) (H : list heq) : Prop :=
  Forall (fun h => solves1 D (apE S h)) H.

Definition is_bool (T : typ) : bool := match T with typ_Bool => true | _ => false end.

(* A variable against a type with another head, or a sort the type cannot
   meet: a scalar or a function against a variable whose sort it does not
   satisfy, or two types of different heads. *)
Definition is_fn_typ (T : typ) : bool := match T with typ_Arrow _ _ => true | _ => false end.

Definition clash_d (D : denv) (A B : typ) : bool :=
  match A, B with
  | typ_Var a, typ_Var b => false
  | typ_Var a, _ => (is_scalar_typ B || is_fn_typ B) && negb (sat_b D (D a) B)
  | _, typ_Var b => (is_scalar_typ A || is_fn_typ A) && negb (sat_b D (D b) A)
  | _, _ => clash D A B
  end.

Fixpoint dis (k f : nat) (D : denv) (H : list heq) (n : nat) {struct k}
  : option (sub * denv * nat) :=
  match k with
  | O => match H with nil => Some (sid, D, n) | _ => None end
  | S k' =>
  match H with
  | nil => Some (sid, D, n)
  | h :: H' =>
      if is_bool (h_pres h) then dis k' f D H' n
      else
      match unify_tD f D (h_fld h) (h_val h) n with
      | Some (s1, D1, n1) =>
          match dis k' f D1 (apH s1 H') n1 with
          | Some (s2, D2, n2) => Some (scomp s2 s1, D2, n2)
          | None => None
          end
      | None =>
          match h_pres h with
          | typ_Var p =>
              if clash_d D (h_fld h) (h_val h) && sat_b D (D p) typ_Bool
                 && rlacksD D (h_lbl h) (h_rest h)
              then
                match dis k' f D (apH (bool_sub (p :: nil)) H') n with
                | Some (s2, D2, n2) => Some (scomp s2 (bool_sub (p :: nil)), D2, n2)
                | None => None
                end
              else None
          | _ => None
          end
      end
  end
  end.

(* An equation whose presence is a variable of the context: a later statement
   of the enclosing function can still settle it. *)
Definition owned_h (G : ctx) (h : heq) : bool :=
  match h_pres h with
  | typ_Var p => AtomSetImpl.mem p (ftv_ctx G)
  | _ => false
  end.

Definition pres_owned (G : ctx) (H : list heq) : bool := existsb (owned_h G) H.

Lemma pres_owned_nil : forall G, pres_owned G nil = false.
Proof. reflexivity. Qed.

(* A binding that holds an equation on a presence of the context can neither
   discharge nor decide it.  When the algorithm may speculate, it generalizes
   the bound term as if every such presence were absent ([own_sub] makes them
   [Bool], in the type only) and holds [absent_req] in place of the equation: a
   requirement that is satisfied exactly when the presence ends up [Bool], and
   that [dis] never discharges by deciding the presence itself, because its
   rest names the label. *)
Definition own_atoms (H : list heq) : list atom :=
  flat_map (fun h => match h_pres h with typ_Var p => p :: nil | _ => nil end) H.

Definition own_sub (d : sub) (Ho : list heq) : sub := bool_sub (own_atoms (apH d Ho)).

Definition absent_req (h : heq) : heq :=
  Heq (h_lbl h) (h_pres h) typ_Bool typ_Unit (row_Ext (h_lbl h) typ_Unit row_Empty).

(* A use of a scheme re-holds what its entries held.  The presences [ps] are the
   fresh atoms the use gave the scheme's quantified presences; each open entry
   of the instance whose presence is one of them gets a field of its own, a
   fresh variable, and the equation that it is the field it had when the
   presence is present.  A recursive type is left as it is. *)
Definition fresh_pres (ps : list atom) (P : typ) : bool :=
  match P with
  | typ_Var a => if in_dec Atom.eq_dec a ps then true else false
  | _ => false
  end.

Fixpoint rh_t (ps : list atom) (T : typ) (m : nat) {struct T} : typ * list heq * nat :=
  match T with
  | typ_Arrow A B =>
      let '(A', H1, m1) := rh_t ps A m in
      let '(B', H2, m2) := rh_t ps B m1 in
      (typ_Arrow A' B', H1 ++ H2, m2)
  | typ_Record R =>
      let '(R', H, m1) := rh_r ps R m in
      (typ_Record R', H, m1)
  | _ => (T, nil, m)
  end
with rh_r (ps : list atom) (R : row) (m : nat) {struct R} : row * list heq * nat :=
  match R with
  | row_Empty | row_Var _ => (R, nil, m)
  | row_Ext l T R0 =>
      let '(T', H1, m1) := rh_t ps T m in
      let '(R', H2, m2) := rh_r ps R0 m1 in
      (row_Ext l T' R', H1 ++ H2, m2)
  | row_Maybe l P F R0 =>
      let '(F', H1, m1) := rh_t ps F m in
      let '(R', H2, m2) := rh_r ps R0 m1 in
      if fresh_pres ps P then
        (row_Maybe l P (typ_Var (ea m2)) R',
         H1 ++ H2 ++ Heq l P (typ_Var (ea m2)) F' R' :: nil, S m2)
      else (row_Maybe l P F' R', H1 ++ H2, m2)
  end.

(* The discharge of a program's equations at the top: nothing to do for none. *)
Definition dis_top (f : nat) (D : denv) (H : list heq) (n : nat)
  : option (sub * denv * nat) :=
  dis (S (length H)) f D H n.
