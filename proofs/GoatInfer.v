(* The inference algorithm for the core calculus: Hindley-Milner algorithm W
   with Leijen's row unification over scoped labels (ADR 0037, decision 2).

   This file holds the unifier and the pieces of the algorithm, so that they
   extract to OCaml (see [GoatExtract.v]); the algorithm itself, which calls
   them, is in GoatInferW.v, and GoatInferSound.v proves it sound against
   [typing].
   A type variable carries a sort (ADR 0038), read from a kinding environment
   the algorithm threads and the unifiers return.

   Naming discipline that the soundness proof leans on.  The algorithm draws
   every type or row variable it invents from the EVEN atoms [ea n], and
   every quantifier it builds at a [let] from the ODD atoms [oa n].  A
   substitution therefore never touches, and never produces, a quantified
   variable, which is what lets a substitution be applied to a scheme without
   renaming it. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Atom supply                                                          *)
(* ------------------------------------------------------------------ *)

Fixpoint pre (n : nat) : list atom :=
  match n with
  | O => nil
  | S k => let l := pre k in fresh l :: l
  end.

Definition idx_atom (n : nat) : atom := fresh (pre n).
Definition ea (n : nat) : atom := idx_atom (2 * n).
Definition oa (n : nat) : atom := idx_atom (2 * n + 1).

(* ------------------------------------------------------------------ *)
(* Substitutions                                                        *)
(* ------------------------------------------------------------------ *)

Record sub : Type := Sub { sT : tsub; sR : rsub }.

Definition apT (s : sub) (T : typ) : typ := ap_typ (sT s) (sR s) T.
Definition apR (s : sub) (R : row) : row := ap_row (sT s) (sR s) R.

Definition sid : sub := Sub idt idr.

(* [scomp s2 s1] applies [s1] first. *)
Definition scomp (s2 s1 : sub) : sub :=
  Sub (tcomp (sT s2) (sR s2) (sT s1)) (rcomp (sT s2) (sR s2) (sR s1)).

Definition sbT (a : atom) (T : typ) : sub :=
  Sub (fun b => if Atom.eq_dec b a then T else typ_Var b) idr.

Definition sbR (r : atom) (R : row) : sub :=
  Sub idt (fun s => if Atom.eq_dec s r then R else row_Var s).

Definition apC (s : sub) (G : ctx) : ctx :=
  List.map (fun p => (fst p, Sch (s_tq (snd p)) (s_rq (snd p)) (apT s (s_body (snd p))) (s_sk (snd p)) (s_rk (snd p)))) G.

(* ------------------------------------------------------------------ *)
(* Sorts                                                                *)
(* ------------------------------------------------------------------ *)

(* A type variable carries a sort (ADR 0038), read from the kinding
   environment the algorithm threads.  Unification binds the coarser of two
   variables to the finer, and binds a sorted variable to a type only when the
   type satisfies the sort, after pushing the sort onto the variables inside
   the type ([push_sort]).  Only a fresh variable gets a sort, so the
   environment changes by [upd] on atoms no one has used. *)

Definition upd (D : denv) (a : atom) (k : sort) : denv :=
  DEnv (fun b => if Atom.eq_dec b a then k else D b) (drk D).

(* A row variable's kind (a sort and the labels it lacks) is set the same way,
   on a row variable no one has used. *)
Definition rupd (D : denv) (r : atom) (K : rkind) : denv :=
  DEnv (dsort D) (fun b => if Atom.eq_dec b r then K else drk D b).

Definition finer_b (k1 k2 : sort) : bool :=
  match k1, k2 with
  | _, k_Any => true
  | k_Literal, k_Quot => false
  | k_Literal, _ => true
  | k_Numeric, (k_Numeric | k_Eq) => true
  | k_Quot, (k_Quot | k_Numeric | k_Eq) => true
  | k_Eq, k_Eq => true
  | _, _ => false
  end.

(* The kind a row variable standing for two has: the finer sort and every
   label either lacks. *)
Definition rk_join (K1 K2 : rkind) : rkind :=
  RK (if finer_b (rk_sort K1) (rk_sort K2) then rk_sort K1 else rk_sort K2)
     (fun l => rk_lacks K1 l || rk_lacks K2 l).

Fixpoint sat_b (D : denv) (k : sort) (T : typ) {struct T} : bool :=
  match T with
  | typ_Int => match k with k_Quot => false | _ => true end
  | typ_Float => true
  | typ_Var a => finer_b (D a) k
  | typ_Record R =>
      match k with k_Any => true | k_Eq | k_Numeric | k_Quot => rsat_b D k R | k_Literal => false end
  | typ_String | typ_Bool | typ_Unit | typ_Bvar _ => match k with k_Any | k_Eq => true | _ => false end
  | typ_Mu B => match k with k_Any => true | k_Eq => sat_b D k_Eq B | _ => false end
  | typ_Grp w A => match k with k_Any => true | k_Eq => spine_sat_b D w 0 A | _ => false end
  | typ_Arrow _ _ => match k with k_Any => true | _ => false end
  end
with spine_sat_b (D : denv) (w : gdecl) (j : nat) (A : typ) {struct A} : bool :=
  match A with
  | typ_Arrow T A' =>
      (negb (existsb (fun cs => existsb (Nat.eqb (6 + j)) cs) (gtags w)) || sat_b D k_Eq T)
        && spine_sat_b D w (S j) A'
  | typ_Unit => true
  | _ => false
  end
with rsat_b (D : denv) (k : sort) (R : row) {struct R} : bool :=
  match R with
  | row_Empty => true
  | row_Ext _ T R' => sat_b D k T && rsat_b D k R'
  | row_Var r => finer_b (rk_sort (drk D r)) k
  | row_Maybe _ P T R' => (is_abs P || sat_b D k T) && rsat_b D k R'
  end.

(* ------------------------------------------------------------------ *)
(* Unification                                                          *)
(* ------------------------------------------------------------------ *)

(* A type with a free recursion index is closed by no substitution, so the
   occurs check refuses to bind a variable to one. *)
Fixpoint lcb (k : nat) (T : typ) {struct T} : bool :=
  match T with
  | typ_Int | typ_Float | typ_Bool | typ_Unit | typ_String | typ_Var _ => true
  | typ_Arrow A B => lcb k A && lcb k B
  | typ_Record R => lcrb k R
  | typ_Bvar n => Nat.ltb n k
  | typ_Mu B => lcb (S k) B
  | typ_Grp _ A => lcb k A
  end
with lcrb (k : nat) (R : row) {struct R} : bool :=
  match R with
  | row_Empty | row_Var _ => true
  | row_Ext _ T R' => lcb k T && lcrb k R'
  | row_Maybe _ P T R' => lcb k P && lcb k T && lcrb k R'
  end.

Definition occT (a : atom) (T : typ) : bool :=
  AtomSetImpl.mem a (ftv_typ T) || negb (lcb 0 T).
Definition occR (r : atom) (R : row) : bool :=
  AtomSetImpl.mem r (frv_row R) || negb (lcrb 0 R).

(* A [Literal] variable and a [Quot] variable have no finer sort between them:
   the numeral may be an [Int] and the quotient's type may not, so both
   are [Float]. *)
Definition meet_float (a b : atom) : sub := scomp (sbT b typ_Float) (sbT a typ_Float).

(* The sort [k] reaches the variables inside the type a variable of sort [k] is
   bound to: each variable of [l] that is coarser than [k] is renamed to a fresh
   variable of sort [k], one fresh atom at a time.  The substitution it returns
   is the renaming, and the environment has the fresh variables' sorts. *)
Fixpoint push_sort (D : denv) (k : sort) (l : list atom) (n : nat) {struct l}
  : sub * denv * nat :=
  match l with
  | nil => (sid, D, n)
  | b :: l' =>
      if finer_b (D b) k then push_sort D k l' n
      else if finer_b k (D b) then
        match push_sort (upd D (ea n) k) k l' (S n) with
        | (s, D', n') => (scomp s (sbT b (typ_Var (ea n))), D', n')
        end
      else push_sort D k l' n
  end.

(* The sort [k] also reaches the row variables inside that type: each row
   variable of [l] whose sort is coarser than [k] is renamed to a fresh row
   variable of sort [k] that lacks what it lacked. *)
Fixpoint push_sort_r (D : denv) (k : sort) (l : list atom) (n : nat) {struct l}
  : sub * denv * nat :=
  match l with
  | nil => (sid, D, n)
  | q :: l' =>
      if finer_b (rk_sort (drk D q)) k then push_sort_r D k l' n
      else if finer_b k (rk_sort (drk D q)) then
        match push_sort_r (rupd D (ea n) (RK k (rk_lacks (drk D q)))) k l' (S n) with
        | (s, D', n') => (scomp s (sbR q (row_Var (ea n))), D', n')
        end
      else push_sort_r D k l' n
  end.

(* Bind [a] to [T], at the sort of [a]: the sort is pushed onto the type and
   the row variables of [T], and the renamed [T] must satisfy it.  The occurs
   check runs before the renaming, which never touches [a], and after it. *)
Definition bind_prop (D : denv) (a : atom) (T : typ) (n : nat) : option (sub * denv * nat) :=
  if occT a T then None
  else
    match push_sort D (D a) (AtomSetImpl.elements (ftv_typ T)) n with
    | (sp, D1, n1) =>
        match push_sort_r D1 (D1 a) (AtomSetImpl.elements (frv_typ T)) n1 with
        | (sr, D2, n2) =>
            let T' := apT sr (apT sp T) in
            if occT a T' then None
            else if sat_b D2 (D2 a) T' then Some (scomp (sbT a T') (scomp sr sp), D2, n2) else None
        end
    end.

(* The variable at the end of a row, and the labels before it. *)
Fixpoint row_tail (R : row) : option atom :=
  match R with
  | row_Empty => None
  | row_Var q => Some q
  | row_Ext _ _ R' => row_tail R'
  | row_Maybe _ _ _ R' => row_tail R'
  end.

(* The row variable [rewrite_row] may not bind when it rewrites the second row
   to present the label of the first row's front entry: the tail of the first
   row, the only variable whose binding there leaves the two rests with a common
   tail and no unifier (Leijen's side condition).  A variable inside a field of
   the first row is no obstacle: it is bound, and the field is then compared
   under the binding. *)
Definition side_av (R : row) : atoms :=
  match row_tail R with
  | Some q => {{ q }}
  | None => {}
  end.

Fixpoint row_labels (R : row) : list label :=
  match R with
  | row_Empty | row_Var _ => nil
  | row_Ext l _ R' => l :: row_labels R'
  | row_Maybe l _ _ R' => l :: row_labels R'
  end.

(* A row may mention a label the kind lacks only as an absent entry. *)
Fixpoint lacks_ok (K : rkind) (R : row) {struct R} : bool :=
  match R with
  | row_Empty | row_Var _ => true
  | row_Ext l _ R' => negb (rk_lacks K l) && lacks_ok K R'
  | row_Maybe l P _ R' => (negb (rk_lacks K l) || is_abs P) && lacks_ok K R'
  end.

(* The second half of [bind_row]: after [sq] renamed the tail of [R] (leaving
   [D0] and the supply [n0]), the sort of [r] reaches the type variables of the
   fields, and the renamed row must satisfy the sort and lack the labels [r]
   lacks.  The occurs check runs again after the renaming. *)
Definition bind_row_fin (r : atom) (R : row) (sq : sub) (D0 : denv) (n0 : nat)
  : option (sub * denv * nat) :=
  let R0 := apR sq R in
  match push_sort D0 (rk_sort (drk D0 r)) (AtomSetImpl.elements (ftv_row R0)) n0 with
  | (sp, D1, n1) =>
      let R1 := apR sp R0 in
      if occR r R1 then None
      else if rsat_b D1 (rk_sort (drk D1 r)) R1 && lacks_ok (drk D1 r) R1
           then Some (scomp (sbR r R1) (scomp sp sq), D1, n1) else None
  end.

(* Bind the row variable [r] to [R], at the kind of [r]: the variable at the
   tail of [R] is renamed to a fresh one of the kind both have (a lacks set is
   a function, so the two cannot be compared), the sort of [r] reaches the
   type variables of the fields, and the renamed row must satisfy the sort and
   lack the labels [r] lacks. *)
Definition bind_row_core (D : denv) (r : atom) (R : row) (n : nat) : option (sub * denv * nat) :=
  if occR r R then None
  else
    match row_tail R with
    | None => bind_row_fin r R sid D n
    | Some q =>
        bind_row_fin r R (sbR q (row_Var (ea n)))
          (rupd D (ea n) (rk_join (drk D r) (drk D q))) (S n)
    end.

(* The presence variables of the entries of [R] for labels the kind of the
   row variable lacks: the row variable can be bound to [R] only if they are
   absent, so each is bound to [Bool] first (a presence is nothing else when
   its field is no field). *)
Fixpoint abs_vars (K : rkind) (R : row) {struct R} : list atom :=
  match R with
  | row_Ext _ _ R' => abs_vars K R'
  | row_Maybe l (typ_Var p) _ R' => if rk_lacks K l then p :: abs_vars K R' else abs_vars K R'
  | row_Maybe _ _ _ R' => abs_vars K R'
  | _ => nil
  end.

Fixpoint bool_sub (ps : list atom) : sub :=
  match ps with
  | nil => sid
  | p :: ps' => scomp (bool_sub ps') (sbT p typ_Bool)
  end.

(* Bind the row variable [r] to [R]: the presence of an entry for a label [r]
   lacks becomes [Bool], if the presence variable's sort allows it; the sort of
   [r] reaches the row variables inside [R] (a nested record's tail is as
   sorted as the field it sits in); and then [R] is bound as [bind_row_core]
   does. *)
Definition bind_row (D : denv) (r : atom) (R : row) (n : nat) : option (sub * denv * nat) :=
  let ps := abs_vars (drk D r) R in
  if forallb (fun p => sat_b D (D p) typ_Bool) ps then
    let R0 := apR (bool_sub ps) R in
    if occR r R0 then None
    else
      match push_sort_r D (rk_sort (drk D r)) (AtomSetImpl.elements (frv_row R0)) n with
      | (sr, D1, n1) =>
          match bind_row_core D1 r (apR sr R0) n1 with
          | Some (s, D', n') => Some (scomp s (scomp sr (bool_sub ps)), D', n')
          | None => None
          end
      end
  else None.

(* Rewrite [R] so that it presents label [l] first, with a presence:
   [Some (P, T, R', s, D', n')] with [s R] equivalent to [l ^ P : T ; R'].  A
   field [R] has gives presence [Unit], a closed row that has none gives [Bool]
   (the absent field's type is a fresh variable, and [l] is absent from the
   rest), and a row variable is bound to [l ^ p : a ; r'] for a fresh presence
   variable [p], a fresh field variable [a] of the sort the row variable has (the
   field of an unresolved presence takes the sort of its row), and a fresh row
   variable [r'] of the kind it had.  A row variable that lacks [l] is bound to
   [l ^ Bool : a ; r'] in the same way: [r'] lacks what [r] did, so the binding
   keeps the kind, and the entry is absent from the start.  [av] holds the row
   variables the row variable at the tail of [R] may not be (Leijen's side
   condition). *)
Fixpoint rewrite_row (l : label) (av : atoms) (D : denv) (R : row) (n : nat)
  : option (typ * typ * row * sub * denv * nat) :=
  match R with
  | row_Empty => Some (typ_Bool, typ_Var (ea n), row_Empty, sid, D, S n)
  | row_Var r =>
      if AtomSetImpl.mem r av then None
      else
        let K := drk D r in
        if rk_lacks K l then
          let a := typ_Var (ea n) in
          let r' := row_Var (ea (S n)) in
          Some (typ_Bool, a, r', sbR r (row_Maybe l typ_Bool a r'), rupd D (ea (S n)) K, n + 2)
        else
          let p := typ_Var (ea n) in
          let a := typ_Var (ea (S n)) in
          let r' := row_Var (ea (n + 2)) in
          Some (p, a, r', sbR r (row_Maybe l p a r'),
                rupd (upd D (ea (S n)) (rk_sort K)) (ea (n + 2)) K, n + 3)
  | row_Ext l' T' R'' =>
      if Nat.eqb l l' then Some (typ_Unit, T', R'', sid, D, n)
      else
        match rewrite_row l av D R'' n with
        | None => None
        | Some (P0, T0, R3, s, D1, n1) => Some (P0, T0, row_Ext l' (apT s T') R3, s, D1, n1)
        end
  | row_Maybe l' P' T' R'' =>
      if Nat.eqb l l' then Some (P', T', R'', sid, D, n)
      else
        match rewrite_row l av D R'' n with
        | None => None
        | Some (P0, T0, R3, s, D1, n1) =>
            Some (P0, T0, row_Maybe l' (apT s P') (apT s T') R3, s, D1, n1)
        end
  end.

(* The first entry of a row, as a presence, a type and the rest: a plain field
   is present. *)
Definition row_head (R : row) : option (label * typ * typ * row) :=
  match R with
  | row_Ext l T R' => Some (l, typ_Unit, T, R')
  | row_Maybe l P T R' => Some (l, P, T, R')
  | _ => None
  end.

(* An entry whose presence is [Bool] is no field when nothing after it has the
   label ([req_abs]), whatever its field type says: two rows that differ only
   in such an entry are one row.  The unifier drops them before comparing, so
   the type of an absent field is never unified with anything. *)
Fixpoint drop_abs (R : row) : row :=
  match R with
  | row_Ext l T R' => row_Ext l T (drop_abs R')
  | row_Maybe l P T R' =>
      let R'' := drop_abs R' in
      if is_abs P && rlacks l R'' then R'' else row_Maybe l P T R''
  | _ => R
  end.

Fixpoint unify_t (f : nat) (D : denv) (T1 T2 : typ) (n : nat) {struct f}
  : option (sub * denv * nat) :=
  match f with
  | O => None
  | S f' =>
      match T1, T2 with
      | typ_Int, typ_Int => Some (sid, D, n)
      | typ_Float, typ_Float => Some (sid, D, n)
      | typ_Bool, typ_Bool => Some (sid, D, n)
      | typ_Unit, typ_Unit => Some (sid, D, n)
      | typ_String, typ_String => Some (sid, D, n)
      | typ_Var a, typ_Var b =>
          if Atom.eq_dec a b then Some (sid, D, n)
          else if finer_b (D b) (D a) then Some (sbT a T2, D, n)
          else if finer_b (D a) (D b) then Some (sbT b T1, D, n)
          else Some (meet_float a b, D, n)
      | typ_Var a, _ => bind_prop D a T2 n
      | _, typ_Var b => bind_prop D b T1 n
      | typ_Arrow A B, typ_Arrow A' B' =>
          match unify_t f' D A A' n with
          | None => None
          | Some (s1, D1, n1) =>
              match unify_t f' D1 (apT s1 B) (apT s1 B') n1 with
              | None => None
              | Some (s2, D2, n2) => Some (scomp s2 s1, D2, n2)
              end
          end
      | typ_Record R, typ_Record R' => unify_r f' D (drop_abs R) (drop_abs R') n
      | typ_Grp w A, typ_Grp w' A' =>
          if gdecl_eq_dec w w' then unify_t f' D A A' n else None
      | _, _ => None
      end
  end
with unify_r (f : nat) (D : denv) (R1 R2 : row) (n : nat) {struct f}
  : option (sub * denv * nat) :=
  match f with
  | O => None
  | S f' =>
      match R1, R2 with
      | row_Var r, row_Var s =>
          if Atom.eq_dec r s then Some (sid, D, n) else bind_row D r R2 n
      | row_Var r, _ => bind_row D r R2 n
      | _, row_Var s => bind_row D s R1 n
      | row_Empty, row_Empty => Some (sid, D, n)
      | row_Empty, row_Maybe _ _ _ _ => unify_r f' D R2 R1 n
      | _, _ =>
          match row_head R1 with
          | None => None
          | Some (l, P, T, R1') =>
              match rewrite_row l (side_av R1) D R2 n with
              | None => None
              | Some (P', T', R2', s0, D0, n1) =>
                  match unify_t f' D0 (apT s0 P) P' n1 with
                  | None => None
                  | Some (sp, D1, n2) =>
                      match unify_t f' D1 (apT sp (apT s0 T)) (apT sp T') n2 with
                      | None => None
                      | Some (s1, D2, n3) =>
                          match unify_r f' D2 (drop_abs (apR s1 (apR sp (apR s0 R1')))) (drop_abs (apR s1 (apR sp R2'))) n3 with
                          | None => None
                          | Some (s2, D3, n4) => Some (scomp s2 (scomp s1 (scomp sp s0)), D3, n4)
                          end
                      end
                  end
              end
          end
      end
  end.

(* The unifier W calls.  It is [unify_t] with the conversion of rows read at the
   kinding environment: before two rows are compared each is normalized at the
   environment the comparison runs in ([nfR], GoatDefs.v), which drops an absent
   entry whose rest lacks its label by a row variable's kind as well as by
   syntax.  The checker peels the same entries (an absent entry against its own
   tail, or two absent entries of one label), and [unify_tD_sound] says the result
   is [teqD] at the environment it returns. *)
Fixpoint unify_tD (f : nat) (D : denv) (T1 T2 : typ) (n : nat) {struct f}
  : option (sub * denv * nat) :=
  match f with
  | O => None
  | S f' =>
      match T1, T2 with
      | typ_Int, typ_Int => Some (sid, D, n)
      | typ_Float, typ_Float => Some (sid, D, n)
      | typ_Bool, typ_Bool => Some (sid, D, n)
      | typ_Unit, typ_Unit => Some (sid, D, n)
      | typ_String, typ_String => Some (sid, D, n)
      | typ_Var a, typ_Var b =>
          if Atom.eq_dec a b then Some (sid, D, n)
          else if finer_b (D b) (D a) then Some (sbT a T2, D, n)
          else if finer_b (D a) (D b) then Some (sbT b T1, D, n)
          else Some (meet_float a b, D, n)
      | typ_Var a, _ => bind_prop D a T2 n
      | _, typ_Var b => bind_prop D b T1 n
      | typ_Arrow A B, typ_Arrow A' B' =>
          match unify_tD f' D A A' n with
          | None => None
          | Some (s1, D1, n1) =>
              match unify_tD f' D1 (apT s1 B) (apT s1 B') n1 with
              | None => None
              | Some (s2, D2, n2) => Some (scomp s2 s1, D2, n2)
              end
          end
      | typ_Record R, typ_Record R' => unify_rD f' D (nfR D R) (nfR D R') n
      | typ_Grp w A, typ_Grp w' A' =>
          if gdecl_eq_dec w w' then unify_t f' D A A' n else None
      | _, _ => None
      end
  end
with unify_rD (f : nat) (D : denv) (R1 R2 : row) (n : nat) {struct f}
  : option (sub * denv * nat) :=
  match f with
  | O => None
  | S f' =>
      match R1, R2 with
      | row_Var r, row_Var s =>
          if Atom.eq_dec r s then Some (sid, D, n) else bind_row D r R2 n
      | row_Var r, _ => bind_row D r R2 n
      | _, row_Var s => bind_row D s R1 n
      | row_Empty, row_Empty => Some (sid, D, n)
      | row_Empty, row_Maybe _ _ _ _ => unify_rD f' D R2 R1 n
      | _, _ =>
          match row_head R1 with
          | None => None
          | Some (l, P, T, R1') =>
              match rewrite_row l (side_av R1) D R2 n with
              | None => None
              | Some (P', T', R2', s0, D0, n1) =>
                  match unify_tD f' D0 (apT s0 P) P' n1 with
                  | None => None
                  | Some (sp, D1, n2) =>
                      match unify_tD f' D1 (apT sp (apT s0 T)) (apT sp T') n2 with
                      | None => None
                      | Some (s1, D2, n3) =>
                          match unify_rD f' D2 (nfR D2 (apR s1 (apR sp (apR s0 R1')))) (nfR D2 (apR s1 (apR sp R2'))) n3 with
                          | None => None
                          | Some (s2, D3, n4) => Some (scomp s2 (scomp s1 (scomp sp s0)), D3, n4)
                          end
                      end
                  end
              end
          end
      end
  end.

(* ------------------------------------------------------------------ *)
(* Instantiation and generalization                                     *)
(* ------------------------------------------------------------------ *)

Fixpoint lookup (x : var) (G : ctx) : option scheme :=
  match G with
  | nil => None
  | (y, s) :: G' => if Atom.eq_dec x y then Some s else lookup x G'
  end.

Fixpoint idx (a : atom) (l : list atom) : nat :=
  match l with
  | nil => 0
  | b :: l' => if Atom.eq_dec a b then 0 else S (idx a l')
  end.

(* The quantified type variables become fresh even atoms numbered from [n],
   and the quantified row variables follow them. *)
Definition inst_sub (s : scheme) (n : nat) : sub :=
  let lq := AtomSetImpl.elements (s_tq s) in
  let lr := AtomSetImpl.elements (s_rq s) in
  Sub (fun a => if in_dec Atom.eq_dec a lq then typ_Var (ea (n + idx a lq)) else typ_Var a)
      (fun r => if in_dec Atom.eq_dec r lr
                then row_Var (ea (n + length lq + idx r lr)) else row_Var r).

(* The fresh variable standing for a quantified one has the sort the scheme
   recorded for it. *)
Definition inst_den (D : denv) (s : scheme) (n : nat) : denv :=
  let lq := AtomSetImpl.elements (s_tq s) in
  let lr := AtomSetImpl.elements (s_rq s) in
  DEnv (fun b => fold_right (fun a acc => if Atom.eq_dec b (ea (n + idx a lq)) then s_sk s a else acc)
                            (D b) lq)
       (fun b => fold_right
                   (fun r acc => if Atom.eq_dec b (ea (n + length lq + idx r lr)) then s_rk s r else acc)
                   (drk D b) lr).

Definition instantiate (D : denv) (s : scheme) (n : nat) : typ * denv * nat :=
  (apT (inst_sub s n) (s_body s), inst_den D s n,
   n + length (AtomSetImpl.elements (s_tq s)) + length (AtomSetImpl.elements (s_rq s))).

Definition aset (l : list atom) : atoms := fold_right AtomSetImpl.add AtomSetImpl.empty l.

Definition rename_t (la : list atom) : tsub :=
  fun a => if in_dec Atom.eq_dec a la then typ_Var (oa (idx a la)) else typ_Var a.

Definition rename_r (lr : list atom) : rsub :=
  fun r => if in_dec Atom.eq_dec r lr then row_Var (oa (idx r lr)) else row_Var r.

Definition gen_vars_t (G : ctx) (T : typ) : list atom :=
  AtomSetImpl.elements (AtomSetImpl.diff (ftv_typ T) (ftv_ctx G)).

Definition gen_vars_r (G : ctx) (T : typ) : list atom :=
  AtomSetImpl.elements (AtomSetImpl.diff (frv_typ T) (frv_ctx G)).

(* The sort of each renamed quantified variable is the sort its original has
   in [D]. *)
Definition gen_sk (D : denv) (la : list atom) : sort_fn :=
  fun b => fold_right (fun a acc => if Atom.eq_dec b (oa (idx a la)) then D a else acc) k_Any la.

(* The kind of each renamed quantified row variable is the kind its original
   has in [D]. *)
Definition gen_rk (D : denv) (lr : list atom) : rkind_fn :=
  fun b => fold_right (fun r acc => if Atom.eq_dec b (oa (idx r lr)) then drk D r else acc) rk_any lr.

(* The generalization of [T] over [G], with the quantified variables renamed to
   odd atoms and recorded at their kinds in [D]. *)
Definition gen_ren (D : denv) (G : ctx) (T : typ) : scheme :=
  let la := gen_vars_t G T in
  let lr := gen_vars_r G T in
  Sch (aset (List.map (fun a => oa (idx a la)) la))
      (aset (List.map (fun r => oa (idx r lr)) lr))
      (ap_typ (rename_t la) (rename_r lr) T)
      (gen_sk D la) (gen_rk D lr).

(* [let_pin] is the type whose free variables a [let] leaves monomorphic
   ([let_open], [lit_pinned] in [GoatDefs.v]): [gen_ren] generalizes over the
   context extended with a binding of it. *)
Definition is_lit_sort (k : sort) : bool :=
  match k with k_Literal => true | _ => false end.

Definition lit_vars (D : denv) (T : typ) : list atom :=
  filter (fun a => is_lit_sort (D a)) (AtomSetImpl.elements (ftv_typ T)).

Definition pin_of (la : list atom) : typ :=
  fold_right (fun a acc => typ_Arrow (typ_Var a) acc) typ_Unit la.

Definition let_pin (D : denv) (e : exp) (T : typ) : typ :=
  if let_open e then typ_Unit else pin_of (lit_vars D T).

(* ------------------------------------------------------------------ *)
(* Algorithm W                                                          *)
(* ------------------------------------------------------------------ *)

(* How a binary operator types its operands: both get one fresh variable's
   type, which is [Numeric] for [+ - * // %], [Quot] for [/] (a [Float] or a
   record of them, whatever the operands settle to) and [Eq] for a comparison
   (ADR 0036).  A comparison gives a [Bool] whatever that type is. *)
Definition generic_sort (o : bop) : sort :=
  match kind o with k_cmp => k_Eq | k_quot => k_Quot | _ => k_Numeric end.

Definition bin_res (o : bop) (A : typ) : typ :=
  match kind o with k_cmp => typ_Bool | _ => A end.

(* The type [/] works at.  The checker takes the divisor's shape from a record
   operand, left first (ADR 0012): a closed record becomes the record of the
   same labels at [Float], and anything else is [Float]. *)
Fixpoint float_row (R : row) : option row :=
  match R with
  | row_Empty => Some row_Empty
  | row_Ext l _ R' =>
      match float_row R' with
      | Some R'' => Some (row_Ext l typ_Float R'')
      | None => None
      end
  | _ => None
  end.

Definition float_head (T : typ) : option typ :=
  match T with
  | typ_Record R =>
      match float_row R with Some R' => Some (typ_Record R') | None => None end
  | _ => None
  end.

Definition quot_ty (T1 T2 : typ) : typ :=
  match float_head T1 with
  | Some F => F
  | None => match float_head T2 with Some F => F | None => typ_Float end
  end.

(* A recursive group's members are functions. *)
Fixpoint is_fn_group (fs : fields) : bool :=
  match fs with
  | fs_nil => true
  | fs_cons _ (e_abs _) rest => is_fn_group rest
  | fs_cons _ _ _ => false
  | fs_meth _ _ _ => false
  end.

Fixpoint nfields (fs : fields) : nat :=
  match fs with
  | fs_nil => 0
  | fs_cons _ _ rest => S (nfields rest)
  | fs_meth _ _ rest => S (nfields rest)
  end.

(* The row of a group's members, each at a fresh type variable numbered from [n]. *)
Fixpoint group_row (fs : fields) (n : nat) : row :=
  match fs with
  | fs_nil => row_Empty
  | fs_cons l _ rest => row_Ext l (typ_Var (ea n)) (group_row rest (S n))
  | fs_meth l _ rest => row_Ext l (typ_Var (ea n)) (group_row rest (S n))
  end.

(* The row a method literal's receiver has: the slots of [group_row], then the
   row variable [tl] for what a use adds (ADR 0034 decision 2). *)
Fixpoint obj_row (fs : fields) (n : nat) (tl : row) : row :=
  match fs with
  | fs_nil => tl
  | fs_cons l _ rest => row_Ext l (typ_Var (ea n)) (obj_row rest (S n) tl)
  | fs_meth l _ rest => row_Ext l (typ_Var (ea n)) (obj_row rest (S n) tl)
  end.

(* The number of parameters a group declares: the largest [6 + j] among its
   slot codes, less five. *)
Definition nparams (w : gdecl) : nat :=
  fold_right (fun cs a => fold_right (fun c b => Nat.max (c - 5) b) a cs) 0 (gtags w).

(* [k] fresh variables, from atom [n]. *)
Fixpoint fresh_tys (n k : nat) : list typ :=
  match k with
  | O => nil
  | S k' => typ_Var (ea n) :: fresh_tys (S n) k'
  end.

Fixpoint nodup_b (l : list nat) : bool :=
  match l with
  | nil => true
  | a :: l' => negb (existsb (Nat.eqb a) l') && nodup_b l'
  end.

(* A match is well formed when it names each tag once, only tags of its group,
   and either has an else or names them all ([arms_wf]). *)
Definition arms_wf_b (w : gdecl) (ars : arms) : bool :=
  nodup_b (arms_idx ars)
  && forallb (fun tg => Nat.ltb tg (length (gtags w))) (arms_idx ars)
  && match arms_default ars with
     | Some _ => true
     | None => forallb (fun tg => existsb (Nat.eqb tg) (arms_idx ars)) (seq 0 (length (gtags w)))
     end.

(* A comparison unifies its two operands first and only then requires the
   joined type to be [Eq], as the checker does ([join_operands]); the
   arithmetic operators demand the sort of the left operand first. *)
Definition is_cmp_op (o : bop) : bool :=
  match kind o with k_cmp => true | _ => false end.

Definition fresh_var (G : ctx) (e : exp) : atom :=
  fresh (AtomSetImpl.elements (dom G `union` fv_exp e)).
