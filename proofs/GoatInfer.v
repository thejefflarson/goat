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

Definition finer_b (k1 k2 : sort) : bool :=
  match k1, k2 with
  | _, k_Any => true
  | k_Literal, _ => true
  | k_Numeric, (k_Numeric | k_Eq) => true
  | k_Eq, k_Eq => true
  | _, _ => false
  end.

Fixpoint sat_b (D : denv) (k : sort) (T : typ) {struct T} : bool :=
  match T with
  | typ_Int | typ_Float => true
  | typ_Var a => finer_b (D a) k
  | typ_Record R =>
      match k with k_Any => true | k_Eq | k_Numeric => rsat_b D k R | k_Literal => false end
  | typ_String | typ_Bool | typ_Unit => match k with k_Any | k_Eq => true | _ => false end
  | _ => match k with k_Any => true | _ => false end
  end
with rsat_b (D : denv) (k : sort) (R : row) {struct R} : bool :=
  match R with
  | row_Empty => true
  | row_Ext _ T R' => sat_b D k T && rsat_b D k R'
  | _ => false
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
      else
        match push_sort (upd D (ea n) k) k l' (S n) with
        | (s, D', n') => (scomp s (sbT b (typ_Var (ea n))), D', n')
        end
  end.

(* Bind [a] to [T], at the sort of [a]: the sort is pushed onto the variables
   of [T], and the renamed [T] must satisfy it.  The occurs check runs before
   the renaming, which never touches [a], and after it. *)
Definition bind_prop (D : denv) (a : atom) (T : typ) (n : nat) : option (sub * denv * nat) :=
  if occT a T then None
  else
    match push_sort D (D a) (AtomSetImpl.elements (ftv_typ T)) n with
    | (sp, D1, n1) =>
        let T' := apT sp T in
        if occT a T' then None
        else if sat_b D1 (D1 a) T' then Some (scomp (sbT a T') sp, D1, n1) else None
    end.

(* Rewrite [R] so that it presents label [l] first, with a presence:
   [Some (P, T, R', s, n')] with [s R] equivalent to [l ^ P : T ; R'].  A field
   [R] has gives presence [Unit], a closed row that has none gives [Bool] (the
   absent field's type is a fresh variable, and [l] is absent from the rest),
   and a row variable is bound to [l ^ p : a ; r'] for a fresh presence
   variable [p].  [av] holds the row variables the row variable at the tail of
   [R] may not be (Leijen's side condition). *)
Fixpoint rewrite_row (l : label) (av : atoms) (R : row) (n : nat)
  : option (typ * typ * row * sub * nat) :=
  match R with
  | row_Empty => Some (typ_Bool, typ_Var (ea n), row_Empty, sid, S n)
  | row_Var r =>
      if AtomSetImpl.mem r av then None
      else
        let p := typ_Var (ea n) in
        let a := typ_Var (ea (S n)) in
        let r' := row_Var (ea (n + 2)) in
        Some (p, a, r', sbR r (row_Maybe l p a r'), n + 3)
  | row_Ext l' T' R'' =>
      if Nat.eqb l l' then Some (typ_Unit, T', R'', sid, n)
      else
        match rewrite_row l av R'' n with
        | None => None
        | Some (P0, T0, R3, s, n1) => Some (P0, T0, row_Ext l' (apT s T') R3, s, n1)
        end
  | row_Maybe l' P' T' R'' =>
      if Nat.eqb l l' then Some (P', T', R'', sid, n)
      else
        match rewrite_row l av R'' n with
        | None => None
        | Some (P0, T0, R3, s, n1) =>
            Some (P0, T0, row_Maybe l' (apT s P') (apT s T') R3, s, n1)
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

Definition gdecl_eq_dec (w w' : gdecl) : {w = w'} + {w <> w'} :=
  list_eq_dec (list_eq_dec Nat.eq_dec) w w'.

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
          else if finer_b (D b) (D a) then Some (sbT a T2, D, n) else Some (sbT b T1, D, n)
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
      | typ_Record R, typ_Record R' => unify_r f' D R R' n
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
          if Atom.eq_dec r s then Some (sid, D, n) else Some (sbR r R2, D, n)
      | row_Var r, _ => if occR r R2 then None else Some (sbR r R2, D, n)
      | _, row_Var s => if occR s R1 then None else Some (sbR s R1, D, n)
      | row_Empty, row_Empty => Some (sid, D, n)
      | row_Empty, row_Maybe _ _ _ _ => unify_r f' D R2 R1 n
      | _, _ =>
          match row_head R1 with
          | None => None
          | Some (l, P, T, R1') =>
              match rewrite_row l (frv_row R1) R2 n with
              | None => None
              | Some (P', T', R2', s0, n1) =>
                  match unify_t f' D (apT s0 P) P' n1 with
                  | None => None
                  | Some (sp, D1, n2) =>
                      match unify_t f' D1 (apT sp (apT s0 T)) (apT sp T') n2 with
                      | None => None
                      | Some (s1, D2, n3) =>
                          match unify_r f' D2 (apR s1 (apR sp (apR s0 R1'))) (apR s1 (apR sp R2')) n3 with
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
  DEnv (fun b => fold_right (fun a acc => if Atom.eq_dec b (ea (n + idx a lq)) then s_sk s a else acc)
                            (D b) lq)
       (drk D).

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

(* The generalization of [T] over [G], with the quantified variables renamed to
   odd atoms and recorded at their sorts in [D]. *)
Definition gen_ren (D : denv) (G : ctx) (T : typ) : scheme :=
  let la := gen_vars_t G T in
  let lr := gen_vars_r G T in
  Sch (aset (List.map (fun a => oa (idx a la)) la))
      (aset (List.map (fun r => oa (idx r lr)) lr))
      (ap_typ (rename_t la) (rename_r lr) T)
      (gen_sk D la) (fun _ => rk_any).

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

(* How a binary operator types its operands.  [/] takes Floats.  Every other
   operator is generic: both operands get one fresh variable's type, which is
   [Numeric] for [+ - * // %] and [Eq] for a comparison (ADR 0036), and a
   comparison gives a [Bool] whatever that type is. *)
Definition generic_sort (o : bop) : sort :=
  match kind o with k_cmp => k_Eq | _ => k_Numeric end.

Definition bin_res (o : bop) (A : typ) : typ :=
  match kind o with k_cmp => typ_Bool | _ => A end.

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
  fold_right (fun cs a => fold_right (fun c b => Nat.max (c - 5) b) a cs) 0 w.

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
  && forallb (fun tg => Nat.ltb tg (length w)) (arms_idx ars)
  && match arms_default ars with
     | Some _ => true
     | None => forallb (fun tg => existsb (Nat.eqb tg) (arms_idx ars)) (seq 0 (length w))
     end.

Definition is_generic_op (o : bop) : bool :=
  match kind o with k_quot => false | _ => true end.

Definition fresh_var (G : ctx) (e : exp) : atom :=
  fresh (AtomSetImpl.elements (dom G `union` fv_exp e)).
