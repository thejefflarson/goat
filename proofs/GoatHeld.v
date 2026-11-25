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

(* The equations after the discharge of a run: nothing to do for none. *)
Definition dis_top (f : nat) (D : denv) (T : typ) (H : list heq) (n : nat)
  : option (denv * typ) :=
  match H with
  | nil => Some (D, T)
  | _ =>
      match dis (S (length H)) f D H n with
      | None => None
      | Some (d, D', _) => Some (D', apT d T)
      end
  end.
