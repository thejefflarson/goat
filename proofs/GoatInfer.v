(* The inference algorithm for the core calculus: Hindley-Milner algorithm W
   with Leijen's row unification over scoped labels (ADR 0037, decision 2).

   This file holds only the algorithm, so that it extracts to OCaml (see
   [GoatExtract.v]).  GoatInferSound.v proves it sound against [typing].

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
  | S k => fresh (pre k) :: pre k
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
  List.map (fun p => (fst p, Sch (s_tq (snd p)) (s_rq (snd p)) (apT s (s_body (snd p))))) G.

(* ------------------------------------------------------------------ *)
(* Unification                                                          *)
(* ------------------------------------------------------------------ *)

Definition occT (a : atom) (T : typ) : bool := AtomSetImpl.mem a (ftv_typ T).
Definition occR (r : atom) (R : row) : bool := AtomSetImpl.mem r (frv_row R).

(* Rewrite [R] so that it presents label [l] first: [Some (T, R', s, n')] with
   [s R] equivalent to [l : T ; R'].  [av] holds the row variables the row
   variable at the tail of [R] may not be (Leijen's side condition). *)
Fixpoint rewrite_row (l : label) (av : atoms) (R : row) (n : nat)
  : option (typ * row * sub * nat) :=
  match R with
  | row_Empty => None
  | row_Var r =>
      if AtomSetImpl.mem r av then None
      else
        let a := typ_Var (ea n) in
        let r' := row_Var (ea (S n)) in
        Some (a, r', sbR r (row_Ext l a r'), n + 2)
  | row_Ext l' T' R'' =>
      if Nat.eqb l l' then Some (T', R'', sid, n)
      else
        match rewrite_row l av R'' n with
        | None => None
        | Some (T0, R''', s, n1) => Some (T0, row_Ext l' (apT s T') R''', s, n1)
        end
  end.

Fixpoint unify_t (f : nat) (T1 T2 : typ) (n : nat) {struct f} : option (sub * nat) :=
  match f with
  | O => None
  | S f' =>
      match T1, T2 with
      | typ_Number, typ_Number => Some (sid, n)
      | typ_Bool, typ_Bool => Some (sid, n)
      | typ_Var a, typ_Var b =>
          if Atom.eq_dec a b then Some (sid, n) else Some (sbT a T2, n)
      | typ_Var a, _ => if occT a T2 then None else Some (sbT a T2, n)
      | _, typ_Var b => if occT b T1 then None else Some (sbT b T1, n)
      | typ_Arrow A B, typ_Arrow A' B' =>
          match unify_t f' A A' n with
          | None => None
          | Some (s1, n1) =>
              match unify_t f' (apT s1 B) (apT s1 B') n1 with
              | None => None
              | Some (s2, n2) => Some (scomp s2 s1, n2)
              end
          end
      | typ_Record R, typ_Record R' => unify_r f' R R' n
      | _, _ => None
      end
  end
with unify_r (f : nat) (R1 R2 : row) (n : nat) {struct f} : option (sub * nat) :=
  match f with
  | O => None
  | S f' =>
      match R1, R2 with
      | row_Var r, row_Var s =>
          if Atom.eq_dec r s then Some (sid, n) else Some (sbR r R2, n)
      | row_Var r, _ => if occR r R2 then None else Some (sbR r R2, n)
      | _, row_Var s => if occR s R1 then None else Some (sbR s R1, n)
      | row_Empty, row_Empty => Some (sid, n)
      | row_Ext l T R1', _ =>
          match rewrite_row l (frv_row R1) R2 n with
          | None => None
          | Some (T', R2', s0, n1) =>
              match unify_t f' (apT s0 T) T' n1 with
              | None => None
              | Some (s1, n2) =>
                  match unify_r f' (apR s1 (apR s0 R1')) (apR s1 R2') n2 with
                  | None => None
                  | Some (s2, n3) => Some (scomp s2 (scomp s1 s0), n3)
                  end
              end
          end
      | _, _ => None
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

Definition instantiate (s : scheme) (n : nat) : typ * nat :=
  (apT (inst_sub s n) (s_body s),
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

(* The generalization of [T] over [G], with the quantified variables renamed to
   odd atoms. *)
Definition gen_ren (G : ctx) (T : typ) : scheme :=
  let la := gen_vars_t G T in
  let lr := gen_vars_r G T in
  Sch (aset (List.map (fun a => oa (idx a la)) la))
      (aset (List.map (fun r => oa (idx r lr)) lr))
      (ap_typ (rename_t la) (rename_r lr) T).

(* ------------------------------------------------------------------ *)
(* Algorithm W                                                          *)
(* ------------------------------------------------------------------ *)

Definition fresh_var (G : ctx) (e : exp) : atom :=
  fresh (AtomSetImpl.elements (dom G `union` fv_exp e)).

Fixpoint infer (f : nat) (G : ctx) (e : exp) (n : nat) {struct f}
  : option (sub * typ * nat) :=
  match f with
  | O => None
  | S f' =>
      match e with
      | e_fvar_b _ => None
      | e_fvar_f x =>
          match lookup x G with
          | None => None
          | Some s => let (T, n1) := instantiate s n in Some (sid, T, n1)
          end
      | e_num _ => Some (sid, typ_Number, n)
      | e_true => Some (sid, typ_Bool, n)
      | e_false => Some (sid, typ_Bool, n)
      | e_abs b =>
          let x := fresh_var G b in
          let beta := typ_Var (ea n) in
          match infer f' ((x ~ sch_mono beta) ++ G) (open_exp_wrt_exp b (e_fvar_f x)) (S n) with
          | None => None
          | Some (s, T, n1) => Some (s, typ_Arrow (apT s beta) T, n1)
          end
      | e_app e1 e2 =>
          match infer f' G e1 n with
          | None => None
          | Some (s1, T1, n1) =>
              match infer f' (apC s1 G) e2 n1 with
              | None => None
              | Some (s2, T2, n2) =>
                  let beta := typ_Var (ea n2) in
                  match unify_t f' (apT s2 T1) (typ_Arrow T2 beta) (S n2) with
                  | None => None
                  | Some (s3, n3) =>
                      Some (scomp s3 (scomp s2 s1), apT s3 beta, n3)
                  end
              end
          end
      | e_let e1 e2 =>
          match infer f' G e1 n with
          | None => None
          | Some (s1, T1, n1) =>
              let G1 := apC s1 G in
              let sc := gen_ren G1 T1 in
              let x := fresh_var G1 e2 in
              match infer f' ((x ~ sc) ++ G1) (open_exp_wrt_exp e2 (e_fvar_f x)) n1 with
              | None => None
              | Some (s2, T2, n2) => Some (scomp s2 s1, T2, n2)
              end
          end
      | e_rec fs =>
          match infer_fields f' G fs n with
          | None => None
          | Some (s, R, n1) => Some (s, typ_Record R, n1)
          end
      | e_proj e1 l =>
          match infer f' G e1 n with
          | None => None
          | Some (s1, T1, n1) =>
              let a := typ_Var (ea n1) in
              let r := row_Var (ea (S n1)) in
              match unify_t f' T1 (typ_Record (row_Ext l a r)) (n1 + 2) with
              | None => None
              | Some (s2, n2) => Some (scomp s2 s1, apT s2 a, n2)
              end
          end
      end
  end
with infer_fields (f : nat) (G : ctx) (fs : fields) (n : nat) {struct f}
  : option (sub * row * nat) :=
  match f with
  | O => None
  | S f' =>
      match fs with
      | fs_nil => Some (sid, row_Empty, n)
      | fs_cons l e rest =>
          match infer f' G e n with
          | None => None
          | Some (s1, T1, n1) =>
              match infer_fields f' (apC s1 G) rest n1 with
              | None => None
              | Some (s2, R2, n2) =>
                  Some (scomp s2 s1, row_Ext l (apT s2 T1) R2, n2)
              end
          end
      end
  end.

(* A program is a closed term; the result is its type. *)
Definition infer_closed (fuel : nat) (e : exp) : option typ :=
  match infer fuel nil e 0 with
  | None => None
  | Some (_, T, _) => Some T
  end.
