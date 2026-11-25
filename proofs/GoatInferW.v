(* Algorithm W, elaborating (ADR 0037, decision 3; phase 5, stage 4, part 3b).

   [infer] is Hindley-Milner W with Leijen's row unification (GoatInfer.v),
   with the knot-tying unifier of GoatInferKnot.v and a term as a fifth
   result: the source term with the [fold] and [unfold] its equi-recursive
   types leave implicit written in.  Wherever the algorithm equates the type
   of a subterm with the type its context needs, [unify_co] (GoatCoerce.v)
   finds the substitution and the head coercions that take the subterm to
   that type, and the elaborated term wraps the subterm in them.  A
   difference below a function type or a record field has no head coercion, so
   the algorithm fails on the program: a deep coercion.

   The elaborated term is built from the elaborated subterms alone, never
   rewritten by a substitution, so the substitutions the algorithm threads act
   on the types and the context and leave the term where it is.  A binder's
   body is inferred at its opened form and closed again ([cl], GoatClose.v)
   over the fresh variable that stood for the bound one.

   A recursive group's members are unified with the slots of their names by
   [unify_grp], which puts the coercions a member's result needs under its
   lambda. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatInfer.
Require Import Goat.GoatHeld.
Require Import Goat.GoatElab.
Require Import Goat.GoatClose.
Require Import Goat.GoatCoerce.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* The slots of a method literal are unified with its fields' types, field by
   field: [R] holds the types the fields were inferred at and [Rsl] the slots'
   types under what has been found.  A field whose type meets its slot only up
   to unrolling is wrapped in the head coercions that take it there, which is
   how a method that mentions its own receiver gets a recursive type. *)
Fixpoint tie_obj (f : nat) (D : denv) (fs : fields) (R Rsl : row) (n : nat) {struct fs}
  : option (sub * denv * nat * fields) :=
  match fs, R, Rsl with
  | fs_nil, row_Empty, row_Empty => Some (sid, D, n, fs_nil)
  | fs_cons l e rest, row_Ext l1 T R', row_Ext l2 A Rsl' =>
      if Nat.eqb l l1 && Nat.eqb l l2 then
      match unify_co f D T A n with
      | None => None
      | Some (s1, D1, cs, n1) =>
          match tie_obj f D1 rest (apR s1 R') (apR s1 Rsl') n1 with
          | None => None
          | Some (s2, D2, n2, rest') => Some (scomp s2 s1, D2, n2, fs_cons l (coerce cs e) rest')
          end
      end
      else None
  | fs_meth l e rest, row_Ext l1 T R', row_Ext l2 A Rsl' =>
      if Nat.eqb l l1 && Nat.eqb l l2 then
      match unify_co f D T A n with
      | None => None
      | Some (s1, D1, cs, n1) =>
          match tie_obj f D1 rest (apR s1 R') (apR s1 Rsl') n1 with
          | None => None
          | Some (s2, D2, n2, rest') => Some (scomp s2 s1, D2, n2, fs_meth l (coerce cs e) rest')
          end
      end
      else None
  | _, _, _ => None
  end.

(* A recursive group's member [e] has the type [T] it was inferred at and
   meets the slot type [A] its name was given.  Where the plain unifier
   equates them the member stays as it is.  Where it cannot, and the member
   is a function meeting a function type, the parameters are unified and the
   head coercions that take the result to the slot's result go under the
   member's lambda: a method of the group that calls its own group gets a
   recursive result, and the fold sits where the result is made. *)
Definition unify_mem (f : nat) (D : denv) (e : exp) (T A : typ) (n : nat)
  : option (sub * denv * nat * exp) :=
  match unify_t f D T A n with
  | Some (s, D', n1) => Some (s, D', n1, e)
  | None =>
      match e, T, A with
      | e_abs b, typ_Arrow X Y, typ_Arrow X' Y' =>
          match unify_t f D X X' n with
          | None => None
          | Some (s1, D1, n1) =>
              match unify_co f D1 (apT s1 Y) (apT s1 Y') n1 with
              | None => None
              | Some (s2, D2, cs, n2) => Some (scomp s2 s1, D2, n2, e_abs (coerce cs b))
              end
          end
      | _, _, _ => None
      end
  end.

(* The members of a recursive group against the row of their slots, in order. *)
Fixpoint unify_grp (f : nat) (D : denv) (fs : fields) (R1 R2 : row) (n : nat) {struct f}
  : option (sub * denv * nat * fields) :=
  match f with
  | O => None
  | S f' =>
      match fs, R1, R2 with
      | fs_nil, row_Empty, row_Empty => Some (sid, D, n, fs_nil)
      | fs_cons l e rest, row_Ext l1 T R1', row_Ext l2 A R2' =>
          if Nat.eqb l l1 && Nat.eqb l l2 then
          match unify_mem f' D e T A n with
          | None => None
          | Some (s1, D1, n1, e') =>
              match unify_grp f' D1 rest (apR s1 R1') (apR s1 R2') n1 with
              | None => None
              | Some (s2, D2, n2, rest') => Some (scomp s2 s1, D2, n2, fs_cons l e' rest')
              end
          end
          else None
      | _, _, _ => None
      end
  end.

(* A spread onto a record whose row is not known to lack the label: the label
   is an entry of the base's row with its own presence variable [p] and field
   variable [y], there or not, and a present one in the result.  The spread's
   value has the type [T2] the entry's field has when the entry is there: the
   equation [p => y = T2] is held ([Heq]) until the presence settles.  The rest
   of the base's row lacks the label, as no row holds a label twice (ADR 0033).
   A base whose row variable lacks the label is typed by [infer] directly: its
   row is the one the spread's result extends. *)
Definition spread_present (f : nat) (D2 : denv) (s1 s2 : sub) (T1 T2 : typ) (l : label)
  (e1' e2' : exp) (n2 : nat) (H1 H2 : list heq)
  : option (sub * denv * typ * nat * exp * list heq) :=
  match unify_coD f (rupd D2 (ea (S n2)) (RK k_Any (Nat.eqb l))) (apT s2 T1)
          (typ_Record (row_Maybe l (typ_Var (ea n2)) (typ_Var (ea (n2 + 2))) (row_Var (ea (S n2)))))
          (n2 + 3) with
  | None => None
  | Some (s3, D3, cs, n3) =>
      Some (scomp s3 (scomp s2 s1), D3,
            apT s3 (typ_Record (row_Ext l T2 (row_Var (ea (S n2))))), n3,
            e_spread (coerce cs e1') l e2',
            apH s3 (apH s2 H1) ++ apH s3 H2 ++
              apH s3 (Heq l (typ_Var (ea n2)) (typ_Var (ea (n2 + 2))) T2 (row_Var (ea (S n2))) :: nil))
  end.

(* [infer f D G e n] returns the substitution, the kinding environment the
   result type lives in, the type, the next unused variable number, the
   elaborated term, and the equations it holds ([heq], GoatHeld.v), stated of
   the types at the state it returns.  The environment [D] has [Any] on every even atom from [n]
   on, so a fresh variable is [Any] unless the algorithm gives it a sort with
   [upd]. *)
Fixpoint infer (f : nat) (D : denv) (G : ctx) (e : exp) (n : nat) {struct f}
  : option (sub * denv * typ * nat * exp * list heq) :=
  match f with
  | O => None
  | S f' =>
      match e with
      | e_fvar_b _ => None
      | e_fvar_f x =>
          match lookup x G with
          | None => None
          | Some s => let (p, n1) := instantiate D s n in
                      let (T, D1) := p in Some (sid, D1, T, n1, e, nil)
          end
      | e_num _ => Some (sid, upd D (ea n) k_Literal, typ_Var (ea n), S n, e, nil)
      | e_dec _ => Some (sid, D, typ_Float, n, e, nil)
      | e_unit => Some (sid, D, typ_Unit, n, e, nil)
      | e_str _ => Some (sid, D, typ_String, n, e, nil)
      | e_true => Some (sid, D, typ_Bool, n, e, nil)
      | e_false => Some (sid, D, typ_Bool, n, e, nil)
      | e_abs b =>
          let x := fresh_var G b in
          let beta := typ_Var (ea n) in
          match infer f' D ((x ~ sch_mono beta) ++ G) (open_exp_wrt_exp b (e_fvar_f x)) (S n) with
          | None => None
          | Some (s, D1, T, n1, b', H) =>
              Some (s, D1, typ_Arrow (apT s beta) T, n1, e_abs (cl 0 x b'), H)
          end
      | e_app e1 e2 =>
          match infer f' D G e1 n with
          | None => None
          | Some (s1, D1, T1, n1, e1', H1) =>
              match infer f' D1 (apC s1 G) e2 n1 with
              | None => None
              | Some (s2, D2, T2, n2, e2', H2) =>
                  let beta := typ_Var (ea n2) in
                  match unify_coD f' D2 (apT s2 T1) (typ_Arrow T2 beta) (S n2) with
                  | None => None
                  | Some (s3, D3, cs, n3) =>
                      Some (scomp s3 (scomp s2 s1), D3, apT s3 beta, n3, e_app (coerce cs e1') e2',
                            apH s3 (apH s2 H1) ++ apH s3 H2)
                  end
              end
          end
      | e_let e1 e2 =>
          match infer f' D G e1 n with
          | None => None
          | Some (s1, D1, T1, n1, e1', H1) =>
              if is_gen_value e1' && negb (pres_owned (apC s1 G) H1) then
              match dis (S (length H1)) f' D1 H1 n1 with
              | None => None
              | Some (d, Dd, nd) =>
                  let G1 := apC d (apC s1 G) in
                  let T1' := apT d T1 in
                  let sc := gen_ren Dd (pin_ctx (let_pin Dd e1' T1') G1) T1' in
                  let x := fresh_var G1 e2 in
                  match infer f' Dd ((x ~ sc) ++ G1) (open_exp_wrt_exp e2 (e_fvar_f x)) nd with
                  | None => None
                  | Some (s2, D2, T2, n2, e2', H2) =>
                      Some (scomp s2 (scomp d s1), D2, T2, n2, e_let e1' (cl 0 x e2'), H2)
                  end
              end
              else
              let x := fresh_var (apC s1 G) e2 in
              match infer f' D1 ((x ~ sch_mono T1) ++ apC s1 G) (open_exp_wrt_exp e2 (e_fvar_f x)) n1 with
              | None => None
              | Some (s2, D2, T2, n2, e2', H2) =>
                  Some (scomp s2 s1, D2, T2, n2, e_let e1' (cl 0 x e2'), apH s2 H1 ++ H2)
              end
          end
      | e_letrec fs e2 =>
          if is_fn_group fs then
          let R0 := group_row fs n in
          let p := fresh_var G (e_rec fs) in
          match infer_fields f' D
                  ((p ~ sch_mono (typ_Record R0)) ++ G)
                  (open_fields_wrt_exp fs (e_fvar_f p)) (n + nfields fs) with
          | None => None
          | Some (s1, D1, R1, n1, fs', H1) =>
              match unify_grp f' D1 fs' R1 (apR s1 R0) n1 with
              | None => None
              | Some (s2, D2, n2, fs'') =>
                  match dis (S (length (apH s2 H1))) f' D2 (apH s2 H1) n2 with
                  | None => None
                  | Some (d, Dd, nd) =>
                      let s := scomp d (scomp s2 s1) in
                      let G1 := apC s G in
                      let sc := gen_ren Dd G1 (typ_Record (apR s R0)) in
                      let q := fresh_var G1 e2 in
                      match infer f' Dd ((q ~ sc) ++ G1) (open_exp_wrt_exp e2 (e_fvar_f q)) nd with
                      | None => None
                      | Some (s3, D3, T, n3, e2', H3) =>
                          Some (scomp s3 s, D3, T, n3, e_letrec (clf 0 p fs'') (cl 0 q e2'), H3)
                      end
                  end
              end
          end
          else None
      | e_rec fs =>
          if no_meth fs then
          match infer_fields f' D G fs n with
          | None => None
          | Some (s, D1, R, n1, fs', H) => Some (s, D1, typ_Record R, n1, e_rec fs', H)
          end
          else
          let p := fresh_var G (e_rec fs) in
          let Tp := typ_Record (obj_row fs n (row_Var (ea (n + nfields fs)))) in
          match infer_obj f' D G p Tp fs (S (n + nfields fs)) with
          | None => None
          | Some (s1, D1, R1, n1, fs1, H1) =>
              match tie_obj f' D1 fs1 R1 (apR s1 (group_row fs n)) n1 with
              | None => None
              | Some (s2, D2, n2, fs2) =>
                  Some (scomp s2 s1, D2, typ_Record (apR (scomp s2 s1) (group_row fs n)), n2, e_rec fs2,
                        apH s2 H1)
              end
          end
      | e_proj e1 l =>
          match infer f' D G e1 n with
          | None => None
          | Some (s1, D1, T1, n1, e1', H1) =>
              let a := typ_Var (ea n1) in
              let r := row_Var (ea (S n1)) in
              match unify_coD f' D1 T1 (typ_Record (row_Ext l a r)) (n1 + 2) with
              | None => None
              | Some (s2, D2, cs, n2) =>
                  Some (scomp s2 s1, D2, apT s2 a, n2, e_proj (coerce cs e1') l, apH s2 H1)
              end
          end
      | e_ite c a b =>
          match infer f' D G c n with
          | None => None
          | Some (s1, D1, T1, n1, c', H1) =>
              match unify_coD f' D1 T1 typ_Bool n1 with
              | None => None
              | Some (s2, D1', cs1, n2) =>
                  match infer f' D1' (apC s2 (apC s1 G)) a n2 with
                  | None => None
                  | Some (s3, D3, T2, n3, a', H2) =>
                      match infer f' D3 (apC s3 (apC s2 (apC s1 G))) b n3 with
                      | None => None
                      | Some (s4, D4, T3, n4, b', H3) =>
                          match unify_coD f' D4 (apT s4 T2) T3 n4 with
                          | None => None
                          | Some (s5, D5, cs2, n5) =>
                              Some (scomp s5 (scomp s4 (scomp s3 (scomp s2 s1))), D5, apT s5 T3, n5,
                                    e_ite (coerce cs1 c') (coerce cs2 a') b',
                                    apH s5 (apH s4 (apH s3 (apH s2 H1))) ++ apH s5 (apH s4 H2) ++ apH s5 H3)
                          end
                      end
                  end
              end
          end
      | e_con w tg e1 =>
          if Nat.ltb tg (length (gtags w)) then
          match infer f' D G e1 n with
          | None => None
          | Some (s1, D1, T1, n1, e1', H1) =>
              let Ts := fresh_tys n1 (nparams w) in
              match unify_coD f' D1 T1 (tag_payload w Ts tg) (n1 + nparams w) with
              | None => None
              | Some (s2, D2, cs, n2) =>
                  Some (scomp s2 s1, D2, apT s2 (typ_Grp w (spine Ts)), n2, e_con w tg (coerce cs e1'),
                        apH s2 H1)
              end
          end
          else None
      | e_match w e1 ars =>
          if arms_wf_b w ars then
          match infer f' D G e1 n with
          | None => None
          | Some (s1, D1, T1, n1, e1', H1) =>
              let Ts := fresh_tys n1 (nparams w) in
              match unify_coD f' D1 T1 (typ_Grp w (spine Ts)) (n1 + nparams w) with
              | None => None
              | Some (s2, D2, cs, n2) =>
                  match infer_arms f' D2 (apC s2 (apC s1 G)) w (map (apT s2) Ts)
                          (fresh_var G (e_match w e1 ars)) (typ_Var (ea n2)) ars (S n2) with
                  | None => None
                  | Some (s3, D3, T3, n3, ars', H3) =>
                      Some (scomp s3 (scomp s2 s1), D3, T3, n3, e_match w (coerce cs e1') ars',
                            apH s3 (apH s2 H1) ++ H3)
                  end
              end
          end
          else None
      | e_spread e1 l e2 =>
          match infer f' D G e1 n with
          | None => None
          | Some (s1, D1, T1, n1, e1', H1) =>
              match infer f' D1 (apC s1 G) e2 n1 with
              | None => None
              | Some (s2, D2, T2, n2, e2', H2) =>
                  match unify_coD f' D2 (apT s2 T1) (typ_Record (row_Var (ea n2))) (S n2) with
                  | Some (s3, D3, cs, n3) =>
                      if rlacksD D3 l (apR s3 (row_Var (ea n2))) then
                        Some (scomp s3 (scomp s2 s1), D3,
                              apT s3 (typ_Record (row_Ext l T2 (row_Var (ea n2)))), n3,
                              e_spread (coerce cs e1') l e2',
                              apH s3 (apH s2 H1) ++ apH s3 H2)
                      else spread_present f' D2 s1 s2 T1 T2 l e1' e2' n2 H1 H2
                  | None => spread_present f' D2 s1 s2 T1 T2 l e1' e2' n2 H1 H2
                  end
              end
          end
      | e_restrict e1 l =>
          match infer f' D G e1 n with
          | None => None
          | Some (s1, D1, T1, n1, e1', H1) =>
              let a := typ_Var (ea n1) in
              let r := row_Var (ea (S n1)) in
              let D1' := rupd D1 (ea (S n1)) (RK k_Any (Nat.eqb l)) in
              match unify_coD f' D1' T1 (typ_Record (row_Ext l a r)) (n1 + 2) with
              | None => None
              | Some (s2, D2, cs, n2) =>
                  Some (scomp s2 s1, D2, apT s2 (typ_Record r), n2, e_restrict (coerce cs e1') l,
                        apH s2 H1)
              end
          end
      | e_fold _ => None
      | e_unfold _ => None
      | e_tofloat e1 =>
          match infer f' D G e1 n with
          | None => None
          | Some (s1, D1, T1, n1, e1', H1) =>
              let D1' := upd D1 (ea n1) k_Literal in
              match unify_coD f' D1' T1 (typ_Var (ea n1)) (S n1) with
              | None => None
              | Some (s2, D2, cs, n2) =>
                  Some (scomp s2 s1, D2, typ_Float, n2, e_tofloat (coerce cs e1'), apH s2 H1)
              end
          end
      | e_bin e1 o e2 =>
          match infer f' D G e1 n with
          | None => None
          | Some (s1, D1, T1, n1, e1', H1) =>
              match infer f' D1 (apC s1 G) e2 n1 with
              | None => None
              | Some (s2, D2, T2, n2, e2', H2) =>
                  if is_cmp_op o then
                      match unify_coD f' D2 (apT s2 T1) T2 n2 with
                      | None => None
                      | Some (s3, D3, cs1, n3) =>
                          let D3' := upd D3 (ea n3) k_Eq in
                          let c := typ_Var (ea n3) in
                          match unify_coD f' D3' (apT s3 T2) c (S n3) with
                          | None => None
                          | Some (s4, D4, cs2, n4) =>
                              Some (scomp s4 (scomp s3 (scomp s2 s1)), D4, typ_Bool, n4,
                                    e_bin (coerce cs2 (coerce cs1 e1')) o (coerce cs2 e2'),
                                    apH s4 (apH s3 (apH s2 H1)) ++ apH s4 (apH s3 H2))
                          end
                      end
                  else
                      let D2' := upd D2 (ea n2) (generic_sort o) in
                      let c := typ_Var (ea n2) in
                      match unify_coD f' D2' (apT s2 T1) c (S n2) with
                      | None => None
                      | Some (s3, D3, cs1, n3) =>
                          match unify_coD f' D3 (apT s3 T2) (apT s3 c) n3 with
                          | None => None
                          | Some (s4, D4, cs2, n4) =>
                              Some (scomp s4 (scomp s3 (scomp s2 s1)), D4,
                                    bin_res o (apT s4 (apT s3 c)), n4,
                                    e_bin (coerce cs1 e1') o (coerce cs2 e2'),
                                    apH s4 (apH s3 (apH s2 H1)) ++ apH s4 (apH s3 H2))
                          end
                      end
              end
          end
      end
  end
with infer_fields (f : nat) (D : denv) (G : ctx) (fs : fields) (n : nat) {struct f}
  : option (sub * denv * row * nat * fields * list heq) :=
  match f with
  | O => None
  | S f' =>
      match fs with
      | fs_nil => Some (sid, D, row_Empty, n, fs_nil, nil)
      | fs_cons l e rest =>
          match infer f' D G e n with
          | None => None
          | Some (s1, D1, T1, n1, e', H1) =>
              match infer_fields f' D1 (apC s1 G) rest n1 with
              | None => None
              | Some (s2, D2, R2, n2, rest', H2) =>
                  Some (scomp s2 s1, D2, row_Ext l (apT s2 T1) R2, n2, fs_cons l e' rest',
                        apH s2 H1 ++ H2)
              end
          end
      | fs_meth _ _ _ => None
      end
  end

(* A record literal with methods (ADR 0034 decision 2).  Every method of the
   literal takes one receiver [p] of type [Tp]: the literal's own fields at
   slot variables, and a row variable for a use's extension.  A method's body
   is inferred with [p] in scope and closed over it again, as a function's is
   over its parameter; the slots are unified with the fields' types
   afterwards by [tie_obj], which is where a method's type meets the receiver
   that contains it and a knot forms. *)
with infer_obj (f : nat) (D : denv) (G : ctx) (p : atom) (Tp : typ)
       (fs : fields) (n : nat) {struct f}
  : option (sub * denv * row * nat * fields * list heq) :=
  match f with
  | O => None
  | S f' =>
      match fs with
      | fs_nil => Some (sid, D, row_Empty, n, fs_nil, nil)
      | fs_cons l e rest =>
          match infer f' D G e n with
          | None => None
          | Some (s1, D1, T1, n1, e', H1) =>
              match infer_obj f' D1 (apC s1 G) p (apT s1 Tp) rest n1 with
              | None => None
              | Some (s2, D2, R2, n2, rest', H2) =>
                  Some (scomp s2 s1, D2, row_Ext l (apT s2 T1) R2, n2, fs_cons l e' rest',
                        apH s2 H1 ++ H2)
              end
          end
      | fs_meth l e rest =>
          match e with
          | e_abs b =>
              match infer f' D ((p ~ sch_mono Tp) ++ G) (open_exp_wrt_exp b (e_fvar_f p)) n with
              | None => None
              | Some (s1, D1, T1, n1, b', H1) =>
                  match infer_obj f' D1 (apC s1 G) p (apT s1 Tp) rest n1 with
                  | None => None
                  | Some (s2, D2, R2, n2, rest', H2) =>
                      Some (scomp s2 s1, D2,
                            row_Ext l (typ_Arrow (apT s2 (apT s1 Tp)) (apT s2 T1)) R2, n2,
                            fs_meth l (e_abs (cl 0 p b')) rest', apH s2 H1 ++ H2)
                  end
              end
          | _ => None
          end
      end
  end

(* The arms of a match, in order, against a result type [res] each arm's type
   is brought to by head coercions.  Each tag's payload binder is [x], typed by
   the slot record of its tag at the group's parameters [Ts]. *)
with infer_arms (f : nat) (D : denv) (G : ctx) (w : gdecl) (Ts : list typ) (x : var)
       (res : typ) (ars : arms) (n : nat) {struct f}
  : option (sub * denv * typ * nat * arms * list heq) :=
  match f with
  | O => None
  | S f' =>
      match ars with
      | arms_nil => Some (sid, D, res, n, arms_nil, nil)
      | arms_else e =>
          match infer f' D G e n with
          | None => None
          | Some (s1, D1, T1, n1, e', H1) =>
              match unify_coD f' D1 T1 (apT s1 res) n1 with
              | None => None
              | Some (s2, D2, cs, n2) =>
                  Some (scomp s2 s1, D2, apT s2 (apT s1 res), n2, arms_else (coerce cs e'), apH s2 H1)
              end
          end
      | arms_cons tg e rest =>
          match infer f' D ((x ~ sch_mono (tag_payload w Ts tg)) ++ G)
                  (open_exp_wrt_exp e (e_fvar_f x)) n with
          | None => None
          | Some (s1, D1, T1, n1, e', H1) =>
              match unify_coD f' D1 T1 (apT s1 res) n1 with
              | None => None
              | Some (s2, D2, cs, n2) =>
                  match infer_arms f' D2 (apC (scomp s2 s1) G) w
                          (map (apT (scomp s2 s1)) Ts) x (apT s2 (apT s1 res)) rest n2 with
                  | None => None
                  | Some (s3, D3, T3, n3, rest', H3) =>
                      Some (scomp s3 (scomp s2 s1), D3, T3, n3,
                            arms_cons tg (cl 0 x (coerce cs e')) rest',
                            apH s3 (apH s2 H1) ++ H3)
                  end
              end
          end
      end
  end.

(* A program is a closed term; the result is its type, with the sorts of its
   free variables, and its elaboration.  The equations the algorithm still
   holds at the end are discharged ([dis_top]).  A variable left free in a
   program's type is one the program's derivations may instantiate at any type
   of its sort. *)
Definition infer_closed_elab (fuel : nat) (e : exp) : option (denv * typ * exp) :=
  match infer fuel d_any nil e 0 with
  | None => None
  | Some (_, D, T, n, e', H) =>
      match dis_top fuel D H n with
      | None => None
      | Some (d, D', _) => Some (D', apT d T, e')
      end
  end.

Definition infer_closed_env (fuel : nat) (e : exp) : option (denv * typ) :=
  match infer_closed_elab fuel e with
  | None => None
  | Some (D, T, _) => Some (D, T)
  end.

Definition infer_closed (fuel : nat) (e : exp) : option typ :=
  match infer_closed_env fuel e with
  | None => None
  | Some (_, T) => Some T
  end.
