(* Declarative type system and operational semantics for core goat
   (docs/semantics.md sections 4-6), hand-written over the Ott-generated syntax
   and locally-nameless infrastructure (Goat_ott.v).

   Why hand-written rather than Ott-generated: the typing judgment, schemes,
   generalization and instantiation all turn on the free-type/row-variable SETS
   of a type and a context (docs/semantics.md section 5).  The type and row
   variables are a free-variable set, not binders (ADR 0008), realized here as
   metalib [atom]s (issue #151): [ftv]/[frv] are computable [atoms] finite sets
   with decidable membership, scheme quantifier sets are [atoms], and [gen] is a
   set difference.  Ott cannot emit that set machinery nor the [gen] side
   condition, and the reduction's [open]-based redexes are likewise outside
   Ott's relation codegen.  Term variables stay locally nameless (metalib [var]);
   [open_exp_wrt_exp]/[subst_exp]/[fv_exp] and the cofinite-style binder rules
   are the generated/standard LN idiom.

   The core is single-binder and curried (B2's encoding, docs/semantics.md
   section 10 option (a)): [typ_Arrow] is unary and application is unary, so the
   n-ary surface function [program(x1,...,xk)] is the k-fold iteration of this
   core and the per-type "arity" is the count of nested arrows. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Compare_dec.
Require Import Goat.GoatNum.
Require Import Goat.GoatLit.
Require Import Goat.GoatRows.

(* ================================================================== *)
(* Type / row variable substitution (section 5).                       *)
(* A substitution is a pair of total maps; applied homomorphically.    *)
(* ================================================================== *)

Definition tsub := typvar -> typ.
Definition rsub := rowvar -> row.

Fixpoint ap_typ (st : tsub) (sr : rsub) (T : typ) {struct T} : typ :=
  match T with
  | typ_Int => typ_Int
  | typ_Float => typ_Float
  | typ_Bool => typ_Bool
  | typ_Unit => typ_Unit
  | typ_String => typ_String
  | typ_Arrow A B => typ_Arrow (ap_typ st sr A) (ap_typ st sr B)
  | typ_Record R => typ_Record (ap_row st sr R)
  | typ_Var a => st a
  | typ_Bvar i => typ_Bvar i
  | typ_Mu B => typ_Mu (ap_typ st sr B)
  | typ_Grp w A => typ_Grp w (ap_typ st sr A)
  end
with ap_row (st : tsub) (sr : rsub) (R : row) {struct R} : row :=
  match R with
  | row_Empty => row_Empty
  | row_Var r => sr r
  | row_Ext l T R' => row_Ext l (ap_typ st sr T) (ap_row st sr R')
  | row_Maybe l P T R' =>
      row_Maybe l (ap_typ st sr P) (ap_typ st sr T) (ap_row st sr R')
  end.

Definition idt : tsub := fun a => typ_Var a.
Definition idr : rsub := fun r => row_Var r.

(* ================================================================== *)
(* Recursive types (ADR 0037, decision 3).  [typ_Mu B] binds the index    *)
(* 0 of its body [B] with a de Bruijn index; type and row variables stay    *)
(* atoms.  [open_typ k U T] replaces the index [k] of [T] by [U] and         *)
(* lowers the indices above it, so [open_typ 0 (typ_Mu B) B] is the          *)
(* unrolling of [typ_Mu B].  [lct k T] says every index of [T] is bound by   *)
(* one of [k] enclosing mus.                                                  *)
(* ================================================================== *)

Fixpoint open_typ (k : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_Int => typ_Int
  | typ_Float => typ_Float
  | typ_Bool => typ_Bool
  | typ_Unit => typ_Unit
  | typ_String => typ_String
  | typ_Arrow A B => typ_Arrow (open_typ k U A) (open_typ k U B)
  | typ_Record R => typ_Record (open_row k U R)
  | typ_Var a => typ_Var a
  | typ_Bvar n =>
      match lt_eq_lt_dec n k with
      | inleft (left _) => typ_Bvar n
      | inleft (right _) => U
      | inright _ => typ_Bvar (n - 1)
      end
  | typ_Mu B => typ_Mu (open_typ (S k) U B)
  | typ_Grp w A => typ_Grp w (open_typ k U A)
  end
with open_row (k : nat) (U : typ) (R : row) {struct R} : row :=
  match R with
  | row_Empty => row_Empty
  | row_Var r => row_Var r
  | row_Ext l T R' => row_Ext l (open_typ k U T) (open_row k U R')
  | row_Maybe l P T R' =>
      row_Maybe l (open_typ k U P) (open_typ k U T) (open_row k U R')
  end.

Fixpoint lct (k : nat) (T : typ) {struct T} : Prop :=
  match T with
  | typ_Int | typ_Float | typ_Bool | typ_Unit | typ_String | typ_Var _ => True
  | typ_Arrow A B => lct k A /\ lct k B
  | typ_Record R => lcr k R
  | typ_Bvar n => n < k
  | typ_Mu B => lct (S k) B
  | typ_Grp _ A => lct k A
  end
with lcr (k : nat) (R : row) {struct R} : Prop :=
  match R with
  | row_Empty | row_Var _ => True
  | row_Ext _ T R' => lct k T /\ lcr k R'
  | row_Maybe _ P T R' => lct k P /\ lct k T /\ lcr k R'
  end.

(* A substitution is locally closed when no image has a free index; only
   then does it commute with unrolling ([ap_open_mut], GoatRows.v). *)
Definition lc_sub (st : tsub) (sr : rsub) : Prop :=
  (forall a, lct 0 (st a)) /\ (forall r, lcr 0 (sr r)).

(* Guarded recursion, mirroring ADR 0032: every mention of the index [k] sits
   under a record field and under a function type.  [r] and [f] record whether
   the traversal has passed one of each.  (A variant payload will guard on its
   own once variants join the calculus.) *)
Fixpoint gd (r f : bool) (k : nat) (T : typ) {struct T} : Prop :=
  match T with
  | typ_Int | typ_Float | typ_Bool | typ_Unit | typ_String | typ_Var _ => True
  | typ_Arrow A B => gd r true k A /\ gd r true k B
  | typ_Record R => gdr true f k R
  | typ_Bvar n => n = k -> r = true /\ f = true
  | typ_Mu B => gd r f (S k) B
  | typ_Grp _ A => gd true true k A
  end
with gdr (r f : bool) (k : nat) (R : row) {struct R} : Prop :=
  match R with
  | row_Empty | row_Var _ => True
  | row_Ext _ T R' => gd r f k T /\ gdr r f k R'
  | row_Maybe _ P T R' =>
      gd r f k P /\ (is_abs P = true \/ gd r f k T) /\ gdr r f k R'
  end.

Definition guarded (B : typ) : Prop := gd false false 0 B.

(* ================================================================== *)
(* Free type / row variables, as computable finite [atoms] sets        *)
(* (section 5).  Type variables live at [typ_Var]; row variables at     *)
(* [row_Var]; the recursions cross because a record carries a row and a  *)
(* row field carries a type.                                             *)
(* ================================================================== *)

Fixpoint ftv_typ (T : typ) {struct T} : atoms :=
  match T with
  | typ_Int => {}
  | typ_Float => {}
  | typ_Bool => {}
  | typ_Unit => {}
  | typ_String => {}
  | typ_Arrow A B => ftv_typ A `union` ftv_typ B
  | typ_Record R => ftv_row R
  | typ_Var a => {{a}}
  | typ_Bvar _ => {}
  | typ_Mu B => ftv_typ B
  | typ_Grp _ A => ftv_typ A
  end
with ftv_row (R : row) {struct R} : atoms :=
  match R with
  | row_Empty => {}
  | row_Var _ => {}
  | row_Ext _ T R' => ftv_typ T `union` ftv_row R'
  | row_Maybe _ P T R' => ftv_typ P `union` (ftv_typ T `union` ftv_row R')
  end.

Fixpoint frv_typ (T : typ) {struct T} : atoms :=
  match T with
  | typ_Int => {}
  | typ_Float => {}
  | typ_Bool => {}
  | typ_Unit => {}
  | typ_String => {}
  | typ_Arrow A B => frv_typ A `union` frv_typ B
  | typ_Record R => frv_row R
  | typ_Var _ => {}
  | typ_Bvar _ => {}
  | typ_Mu B => frv_typ B
  | typ_Grp _ A => frv_typ A
  end
with frv_row (R : row) {struct R} : atoms :=
  match R with
  | row_Empty => {}
  | row_Var s => {{s}}
  | row_Ext _ T R' => frv_typ T `union` frv_row R'
  | row_Maybe _ P T R' => frv_typ P `union` (frv_typ T `union` frv_row R')
  end.

(* Membership wrappers: the metatheory is phrased with these predicates, and
   their proofs [unfold] to a finite-set membership that [fsetdec] discharges. *)
Definition Ftv_typ (T : typ) (a : typvar) : Prop := a `in` ftv_typ T.
Definition Frv_typ (T : typ) (r : rowvar) : Prop := r `in` frv_typ T.

(* ================================================================== *)
(* Sorts (ADR 0037, phases 2 and 6).  A type variable has a sort: [Any]   *)
(* stands for any type, [Eq] for a type with no function inside it,        *)
(* [Numeric] and [Literal] for [Int] or [Float].  A [Literal] variable is   *)
(* also [Numeric] and a [Numeric] one also [Eq], so one sort is finer than  *)
(* another when its variables may stand wherever the other is asked.  The sort of  *)
(* a free variable comes from a kinding environment [denv], a total map    *)
(* that is [Any] outside a finite support; a quantified variable's sort    *)
(* is recorded in its scheme.                                              *)
(* ================================================================== *)

Inductive sort : Set := k_Any | k_Eq | k_Numeric | k_Literal.

Inductive finer : sort -> sort -> Prop :=
 | finer_refl : forall k, finer k k
 | finer_any : forall k, finer k k_Any
 | finer_lit : forall k, finer k_Literal k
 | finer_numeric_eq : finer k_Numeric k_Eq.

#[export] Hint Constructors finer : core.

Definition sort_fn := typvar -> sort.

(* A row variable has a kind too (ADR 0038, the row-variable amendment): a
   sort, which says what its fields must satisfy ([Eq] or [Numeric] when the
   record it tails is compared or does arithmetic), and the set of labels it
   lacks, which a spread that adds a field needs.  Like a type variable's sort
   it comes from the kinding environment, and a quantified row variable's kind
   is recorded in its scheme. *)
Record rkind : Type := RK { rk_sort : sort; rk_lacks : label -> bool }.

Definition rk_any : rkind := RK k_Any (fun _ => false).

Definition rkind_fn := rowvar -> rkind.

Definition rk_triv : rkind_fn := fun _ => rk_any.

Record denv : Type := DEnv { dsort : typvar -> sort; drk : rowvar -> rkind }.

Coercion dsort : denv >-> Funclass.

(* [sat D k T]: T may stand where a variable of sort [k] stands.  A concrete
   [Int] or [Float] satisfies every sort; a variable satisfies the sorts its
   own (in [D]) is finer than.  A closed record whose fields all satisfy [k]
   satisfies [k], for [Numeric] (ADR 0012) and for [Eq] (ADR 0036), and is
   never [Literal]: a numeral is a number.  [String], [Bool] and [Unit] are
   [Eq] and [Any].  A function is neither.  A recursive type and a tag group
   are [Eq] when their parts are: inside a [mu] body a bound index counts as
   [Eq] (the recursion is the body itself), and a group is [Eq] when every
   parameter its declaration uses is ([spine_sat]); the group's own recursion
   and its concrete slots are [Eq] by themselves. *)
Fixpoint sat (D : denv) (k : sort) (T : typ) {struct T} : Prop :=
  match T with
  | typ_Int | typ_Float => True
  | typ_Var a => finer (D a) k
  | typ_Record R =>
      match k with k_Any => True | k_Eq | k_Numeric => rsat D k R | k_Literal => False end
  | typ_String | typ_Bool | typ_Unit | typ_Bvar _ => k = k_Any \/ k = k_Eq
  | typ_Mu B => match k with k_Any => True | k_Eq => sat D k_Eq B | _ => False end
  | typ_Grp w A => match k with k_Any => True | k_Eq => spine_sat D w 0 A | _ => False end
  | typ_Arrow _ _ => k = k_Any
  end
with rsat (D : denv) (k : sort) (R : row) {struct R} : Prop :=
  match R with
  | row_Empty => True
  | row_Ext _ T R' => sat D k T /\ rsat D k R'
  | row_Var r => finer (rk_sort (drk D r)) k
  | row_Maybe _ _ _ _ => k = k_Any
  end
with spine_sat (D : denv) (w : gdecl) (j : nat) (A : typ) {struct A} : Prop :=
  match A with
  | typ_Arrow T A' =>
      ((exists cs, In cs w /\ In (6 + j) cs) -> sat D k_Eq T) /\ spine_sat D w (S j) A'
  | typ_Unit => True
  | _ => False
  end.

(* [fsat T]: [T] is [Float], or a closed record of such, which is what [/]
   takes on records (ADR 0012): a quotient is a [Float]. *)
Fixpoint fsat (T : typ) {struct T} : Prop :=
  match T with
  | typ_Float => True
  | typ_Record R => rfsat R
  | _ => False
  end
with rfsat (R : row) {struct R} : Prop :=
  match R with
  | row_Empty => True
  | row_Ext _ T R' => fsat T /\ rfsat R'
  | _ => False
  end.

(* [rlacksD D l R]: the row [R] has no field labeled [l]; a row variable lacks
   what its kind in [D] says.  With no variable in [R] it is [rlacks]. *)
Fixpoint rlacksD (D : denv) (l : label) (R : row) {struct R} : bool :=
  match R with
  | row_Empty => true
  | row_Var r => rk_lacks (drk D r) l
  | row_Ext l' _ R' => negb (Nat.eqb l l') && rlacksD D l R'
  | row_Maybe l' _ _ R' => negb (Nat.eqb l l') && rlacksD D l R'
  end.

(* A row has a kind in [D]: it satisfies the sort and lacks the labels. *)
Definition rkok (D : denv) (K : rkind) (R : row) : Prop :=
  rsat D (rk_sort K) R /\ forall l, rk_lacks K l = true -> rlacksD D l R = true.

(* A substitution from one environment to another gives each variable a type
   of its sort, and each row variable a row of its kind. *)
Definition kres (D D' : denv) (st : tsub) : Prop := forall a, sat D' (D a) (st a).

Definition rkres (D D' : denv) (sr : rsub) : Prop := forall r, rkok D' (drk D r) (sr r).

(* The environment D, extended on V by the sorts k, and on Vr by the kinds rk. *)
Definition ext (D : denv) (V : atoms) (k : sort_fn) : denv :=
  DEnv (fun a => if AtomSetImpl.mem a V then k a else D a) (drk D).

Definition extr (D : denv) (Vr : atoms) (rk : rkind_fn) : denv :=
  DEnv (dsort D) (fun r => if AtomSetImpl.mem r Vr then rk r else drk D r).

(* Outside [S], every atom, as a type variable and as a row variable, is
   unconstrained. *)
Definition supp_ok (D : denv) (S : atoms) : Prop :=
  forall a, a `notin` S -> D a = k_Any /\ drk D a = rk_any.

Definition d_any : denv := DEnv (fun _ => k_Any) (fun _ => rk_any).

(* ================================================================== *)
(* Type schemes (section 5): a quantified set of type and row variables  *)
(* over a monotype body.  Quantified sets are finite [atoms]; a monotype  *)
(* scheme quantifies nothing.                                            *)
(* ================================================================== *)

Record scheme : Type := Sch {
  s_tq : atoms;
  s_rq : atoms;
  s_body : typ;
  s_sk : sort_fn;
  s_rk : rkind_fn
}.

Definition sch_mono (T : typ) : scheme := Sch {} {} T (fun _ => k_Any) (fun _ => rk_any).

(* Free variables of a scheme: free in the body and not quantified. *)
Definition ftv_sch (s : scheme) : atoms := AtomSetImpl.diff (ftv_typ (s_body s)) (s_tq s).
Definition frv_sch (s : scheme) : atoms := AtomSetImpl.diff (frv_typ (s_body s)) (s_rq s).

Definition Ftv_sch (s : scheme) (a : typvar) : Prop := a `in` ftv_sch s.
Definition Frv_sch (s : scheme) (r : rowvar) : Prop := r `in` frv_sch s.

(* ================================================================== *)
(* Contexts and their free variables (computable finite sets).          *)
(* ================================================================== *)

Definition ctx := list (var * scheme).

Fixpoint ftv_ctx (G : ctx) : atoms :=
  match G with
  | nil => {}
  | (_, s) :: G' => ftv_sch s `union` ftv_ctx G'
  end.

Fixpoint frv_ctx (G : ctx) : atoms :=
  match G with
  | nil => {}
  | (_, s) :: G' => frv_sch s `union` frv_ctx G'
  end.

Definition Ftv_ctx (G : ctx) (a : typvar) : Prop := a `in` ftv_ctx G.
Definition Frv_ctx (G : ctx) (r : rowvar) : Prop := r `in` frv_ctx G.

(* ================================================================== *)
(* Generic instance (section 5): [inst T s] says T is a generic instance   *)
(* of s -- T is the body with the quantified variables replaced by          *)
(* arbitrary monotypes/rows, the non-quantified (free) variables fixed.     *)
(* A monotype scheme has only itself as an instance.                        *)
(* ================================================================== *)

Definition inst (D : denv) (T : typ) (s : scheme) : Prop :=
  exists (st : tsub) (sr : rsub),
    (forall a, a `notin` s_tq s -> st a = typ_Var a) /\
    (forall r, r `notin` s_rq s -> sr r = row_Var r) /\
    T = ap_typ st sr (s_body s) /\
    (forall a, a `in` s_tq s -> sat D (s_sk s a) (st a)) /\
    (forall r, r `in` s_rq s -> rkok D (s_rk s r) (sr r)) /\
    lc_sub st sr.

(* ================================================================== *)
(* Generalization (section 5): quantify exactly the variables free in     *)
(* the type but not in the context.                                        *)
(* ================================================================== *)

Definition gen (G : ctx) (T : typ) (k : sort_fn) (rk : rkind_fn) : scheme :=
  Sch (AtomSetImpl.diff (ftv_typ T) (ftv_ctx G))
      (AtomSetImpl.diff (frv_typ T) (frv_ctx G))
      T k rk.

(* A [let] may keep some variables of its binding monomorphic by generalizing
   over the context extended with a binding of a type [Tm] that mentions them
   (ADR 0038, the numeral-let addendum).  Only the free variables of the
   extended context matter to [gen], never its names, so one fixed name serves
   every extension. *)
Definition pin_name : var := proj1_sig (atom_fresh empty).

Definition pin_ctx (Tm : typ) (G : ctx) : ctx := (pin_name ~ sch_mono Tm) ++ G.

Lemma ftv_pin_ctx : forall Tm G, ftv_ctx (pin_ctx Tm G) [=] ftv_typ Tm `union` ftv_ctx G.
Proof.
  intros Tm G. unfold pin_ctx. simpl. unfold ftv_sch. simpl. fsetdec.
Qed.

Lemma frv_pin_ctx : forall Tm G, frv_ctx (pin_ctx Tm G) [=] frv_typ Tm `union` frv_ctx G.
Proof.
  intros Tm G. unfold pin_ctx. simpl. unfold frv_sch. simpl. fsetdec.
Qed.

(* ================================================================== *)
(* Tag groups (docs/design/closed-tags-plan.md).  A group is declared  *)
(* by [w : gdecl], a list of its tags in declaration order, each a list of *)
(* slot codes: 0 is the group itself (the recursion), 1 to 5 are the       *)
(* concrete types Int, Float, Bool, Unit, String, and [6 + j] is the       *)
(* group's implicit parameter [j] (a [_] in the declaration).  The type of *)
(* a value of the group is [typ_Grp w A], where [A] spells the parameters  *)
(* as the spine [spine Ts] = [(T0) -> (T1) -> ... -> Unit]: that reuses    *)
(* the arrow's congruence for the arguments, with no new list in [typ].    *)
(* A tag with no slots carries [Unit]; one with slots carries the closed   *)
(* record of them, labeled by position.                                     *)
(* ================================================================== *)

Fixpoint spine (Ts : list typ) : typ :=
  match Ts with
  | nil => typ_Unit
  | T :: Ts' => typ_Arrow T (spine Ts')
  end.

Definition slot_ty (w : gdecl) (Ts : list typ) (c : nat) : typ :=
  match c with
  | 0 => typ_Grp w (spine Ts)
  | 1 => typ_Int
  | 2 => typ_Float
  | 3 => typ_Bool
  | 4 => typ_Unit
  | 5 => typ_String
  | _ => nth (c - 6) Ts typ_Unit
  end.

Fixpoint slots_row (w : gdecl) (Ts : list typ) (i : label) (cs : list nat) : row :=
  match cs with
  | nil => row_Empty
  | c :: cs' => row_Ext i (slot_ty w Ts c) (slots_row w Ts (S i) cs')
  end.

Definition payload_ty (w : gdecl) (Ts : list typ) (cs : list nat) : typ :=
  match cs with
  | nil => typ_Unit
  | _ :: _ => typ_Record (slots_row w Ts 0 cs)
  end.

(* The payload type of tag [tg] of [w] at the parameters [Ts]; a tag outside
   the group has none (no construction of one types, see [T_Con]). *)
Definition tag_payload (w : gdecl) (Ts : list typ) (tg : nat) : typ :=
  match nth_error w tg with
  | Some cs => payload_ty w Ts cs
  | None => typ_Unit
  end.

(* The arms of a match: the first arm for a tag, the else, and the tags the
   arms name.  A well-formed match names each tag at most once, names only
   tags of its group, and either has an else or names them all. *)
Fixpoint arms_find (tg : tagidx) (ars : arms) {struct ars} : option exp :=
  match ars with
  | arms_nil | arms_else _ => None
  | arms_cons tg' e ars' => if Nat.eqb tg tg' then Some e else arms_find tg ars'
  end.

Fixpoint arms_default (ars : arms) {struct ars} : option exp :=
  match ars with
  | arms_nil => None
  | arms_else e => Some e
  | arms_cons _ _ ars' => arms_default ars'
  end.

Fixpoint arms_idx (ars : arms) {struct ars} : list nat :=
  match ars with
  | arms_nil | arms_else _ => nil
  | arms_cons tg _ ars' => tg :: arms_idx ars'
  end.

Definition arms_wf (w : gdecl) (ars : arms) : Prop :=
  NoDup (arms_idx ars) /\
  (forall tg, In tg (arms_idx ars) -> tg < length w) /\
  (arms_default ars <> None \/ forall tg, tg < length w -> In tg (arms_idx ars)).

(* ================================================================== *)
(* Values (section 2).                                                   *)
(* ================================================================== *)

Inductive value : exp -> Prop :=
 | v_num : forall n, value (e_num n)
 | v_dec : forall d, value (e_dec d)
 | v_true : value e_true
 | v_false : value e_false
 | v_unit : value e_unit
 | v_str : forall q, value (e_str q)
 | v_abs : forall e, value (e_abs e)
 | v_fold : forall v, value v -> value (e_fold v)
 | v_con : forall w tg v, value v -> value (e_con w tg v)
 | v_rec : forall fs, rec_value fs -> value (e_rec fs)
with rec_value : fields -> Prop :=
 | rv_nil : rec_value fs_nil
 | rv_cons : forall l v fs,
     value v -> rec_value fs -> rec_value (fs_cons l v fs)
 | rv_meth : forall l v fs,
     value v -> rec_value fs -> rec_value (fs_meth l v fs).

#[export] Hint Constructors value rec_value : core.

(* First field labeled [l] (matches rewrite_row / ST-ProjRec's side cond). *)
Fixpoint lookup_first (l : label) (fs : fields) : option exp :=
  match fs with
  | fs_nil => None
  | fs_cons l' e fs' => if Nat.eqb l l' then Some e else lookup_first l fs'
  | fs_meth l' e fs' => if Nat.eqb l l' then Some e else lookup_first l fs'
  end.

(* A record's method markers only steer typing (T_Obj); running a record, and
   a spread or restrict of it, ignore them, and the record they build is plain. *)
Fixpoint fs_plain (fs : fields) : fields :=
  match fs with
  | fs_nil => fs_nil
  | fs_cons l e fs' => fs_cons l e (fs_plain fs')
  | fs_meth l e fs' => fs_cons l e (fs_plain fs')
  end.

Fixpoint no_meth (fs : fields) : bool :=
  match fs with
  | fs_nil => true
  | fs_cons _ _ fs' => no_meth fs'
  | fs_meth _ _ _ => false
  end.

(* A spread sets the first field labeled [l] to [v] when there is one, and puts
   [l: v] in front otherwise; a restrict takes the first [l] out.  Both look
   at the record, not its type: the types make the two cases agree. *)
Fixpoint fs_replace (l : label) (v : exp) (fs : fields) {struct fs} : fields :=
  match fs with
  | fs_nil => fs_nil
  | fs_cons l' e fs' =>
      if Nat.eqb l l' then fs_cons l' v fs' else fs_cons l' e (fs_replace l v fs')
  | fs_meth l' e fs' =>
      if Nat.eqb l l' then fs_cons l' v fs' else fs_meth l' e (fs_replace l v fs')
  end.

Definition fs_set (l : label) (v : exp) (fs : fields) : fields :=
  match lookup_first l fs with
  | Some _ => fs_replace l v fs
  | None => fs_cons l v fs
  end.

Fixpoint fs_drop (l : label) (fs : fields) {struct fs} : fields :=
  match fs with
  | fs_nil => fs_nil
  | fs_cons l' e fs' =>
      if Nat.eqb l l' then fs' else fs_cons l' e (fs_drop l fs')
  | fs_meth l' e fs' =>
      if Nat.eqb l l' then fs' else fs_meth l' e (fs_drop l fs')
  end.

(* The first [l] of a row: its type and the row without it.  Entries of other
   labels are skipped, and a [Maybe] entry is a present [l] only when its
   presence is [Unit]. *)
Fixpoint rmf (l : label) (R : row) {struct R} : option (typ * row) :=
  match R with
  | row_Empty | row_Var _ => None
  | row_Ext l' T R' =>
      if Nat.eqb l l' then Some (T, R')
      else match rmf l R' with
           | Some (T0, R0) => Some (T0, row_Ext l' T R0)
           | None => None
           end
  | row_Maybe l' P T R' =>
      if Nat.eqb l l' then (if is_unit P then Some (T, R') else None)
      else match rmf l R' with
           | Some (T0, R0) => Some (T0, row_Maybe l' P T R0)
           | None => None
           end
  end.

Definition rm (l : label) (R : row) (T : typ) (R' : row) : Prop :=
  rmf l R = Some (T, R').

(* The value restriction (ADR 0027): a [let] generalizes its binding only when
   the bound term is a syntactic value, one whose evaluation does no work: unit,
   a literal, a name, a function, or a record of those.  (The checker's
   builtins are names here; variants and spreads join with their phases.)  A
   recursive group of functions around a value is one too, as in ML's
   nonexpansive terms: unrolling the group only rewrites it.  That case is what
   lets a name bound to the unrolled group stay generalizable after
   substitution.  So is the coercion of a value, the [float(n)] elaboration
   writes where the checker widens a literal, the [fold] of a value, and a
   spread of a value onto a value, as in the checker's [is_syntactic_value]. *)
Fixpoint is_gen_value (e : exp) {struct e} : bool :=
  match e with
  | e_fvar_b _ | e_fvar_f _ | e_num _ | e_dec _ | e_true | e_false
  | e_unit | e_str _ | e_abs _ => true
  | e_rec fs => is_gen_fields fs
  | e_letrec fs e2 => is_gen_fields fs && is_gen_value e2
  | e_tofloat e1 => is_gen_value e1
  | e_fold e1 => is_gen_value e1
  | e_con _ _ e1 => is_gen_value e1
  | e_spread e1 _ e2 => is_gen_value e1 && is_gen_value e2
  | _ => false
  end
with is_gen_fields (fs : fields) {struct fs} : bool :=
  match fs with
  | fs_nil => true
  | fs_cons _ e fs' => is_gen_value e && is_gen_fields fs'
  | fs_meth _ e fs' => is_gen_value e && is_gen_fields fs'
  end.

(* A [let] of a function or a bare numeral generalizes the variables of its
   type whatever their sort.  Any other value leaves its
   [Literal] variables shared, still open to [Float], as the checker does
   (ADR 0038, the numeral-let addendum): [lit_pinned] says that no variable
   the [let] quantifies, the set [V], has the sort [Literal] in [k]. *)
Definition let_open (e : exp) : bool :=
  match e with
  | e_abs _ | e_num _ => true
  | _ => false
  end.

Lemma let_open_subst : forall u x e, let_open (subst_exp u x e) = false -> let_open e = false.
Proof. intros u x e. destruct e; simpl; auto. Qed.

Definition lit_pinned (e : exp) (V : atoms) (k : sort_fn) : Prop :=
  let_open e = false -> forall a, a `in` V -> k a <> k_Literal.

(* The members of a recursive group are functions, as in the checker, where a
   binding is recursive exactly when its value is a [program(..)] literal
   (ADR 0003). *)
Inductive fn_group : fields -> Prop :=
 | fg_nil : fn_group fs_nil
 | fg_cons : forall l e fs, fn_group fs -> fn_group (fs_cons l (e_abs e) fs).

#[export] Hint Constructors fn_group : core.

(* ================================================================== *)
(* Base-type operators (ADR 0017, ADR 0036).                            *)
(* An [Int] is a signed 64-bit integer: an arithmetic result outside the *)
(* range is a trap, as in the compiler.  A [Float] is opaque: a decimal  *)
(* value [e_dec d] carries a payload no rule reads, and each Float       *)
(* operation relates its operands to every Float (a comparison, to every  *)
(* Bool).  A property of that relation holds for any function a compiler  *)
(* might compute, so IEEE rounding, infinities and NaN need no model.    *)
(* ================================================================== *)

(* What an operator does, by its row in ADR 0017. *)
Inductive bop_kind : Set := k_ring | k_quot | k_whole | k_cmp.

Definition kind (o : bop) : bop_kind :=
  match o with
  | bop_add | bop_sub | bop_mul => k_ring
  | bop_div => k_quot
  | bop_fdiv | bop_rem => k_whole
  | bop_lt | bop_lte | bop_gt | bop_gte | bop_eq | bop_ne => k_cmp
  end.

Lemma kind_cmp_dec : forall o, kind o = k_cmp \/ kind o <> k_cmp.
Proof. intros o. destruct (kind o); first [ left; reflexivity | right; discriminate ]. Qed.

(* [+ - *] over the integers; meaningful when [kind o = k_ring]. *)
Definition ring_Z (o : bop) (a b : znum) : znum :=
  match o with
  | bop_add => z_add a b
  | bop_sub => z_sub a b
  | _ => z_mul a b
  end.

(* [//] floors and [%] takes the sign of the divisor (Z.div and Z.modulo do
   both); meaningful when [kind o = k_whole] and the divisor is not zero. *)
Definition whole_Z (o : bop) (a b : znum) : znum :=
  match o with
  | bop_fdiv => z_div a b
  | _ => z_mod a b
  end.

(* Which comparison results satisfy a comparison operator. *)
Definition cmp_holds (o : bop) (c : comparison) : bool :=
  match o, c with
  | bop_lt, Lt => true
  | bop_lte, (Lt | Eq) => true
  | bop_gt, Gt => true
  | bop_gte, (Gt | Eq) => true
  | bop_eq, Eq => true
  | bop_ne, (Lt | Gt) => true
  | _, _ => false
  end.

(* Strings order bytewise, and a prefix comes first (ADR 0036). *)
Fixpoint str_compare (p q : list nat) {struct p} : comparison :=
  match p, q with
  | nil, nil => Eq
  | nil, _ :: _ => Lt
  | _ :: _, nil => Gt
  | a :: p', b :: q' =>
      match Nat.compare a b with
      | Eq => str_compare p' q'
      | c => c
      end
  end.

(* [false] orders before [true] (ADR 0036). *)
Definition bool_compare (a b : bool) : comparison :=
  match a, b with
  | false, true => Lt
  | true, false => Gt
  | _, _ => Eq
  end.

Definition of_bool (b : bool) : exp := if b then e_true else e_false.

Definition val_bool (v : exp) : option bool :=
  match v with
  | e_true => Some true
  | e_false => Some false
  | _ => None
  end.

(* A Float value may be a numeral: a whole-number literal is typed at any
   [Literal] type, [Float] included.  Two numerals step as [Int]s; a Float
   operation is the case where one operand is a decimal. *)
Inductive fl_pair : exp -> exp -> Prop :=
 | fp_dd : forall x y, fl_pair (e_dec x) (e_dec y)
 | fp_dn : forall x n, fl_pair (e_dec x) (e_num n)
 | fp_nd : forall n y, fl_pair (e_num n) (e_dec y).

#[export] Hint Constructors fl_pair : core.

Fixpoint fs_labels (fs : fields) : list label :=
  match fs with
  | fs_nil => nil
  | fs_cons l _ fs' | fs_meth l _ fs' => l :: fs_labels fs'
  end.

Fixpoint ins_label (l : label) (ls : list label) : list label :=
  match ls with
  | nil => l :: nil
  | l' :: ls' =>
      if Nat.ltb l l' then l :: ls
      else if Nat.eqb l l' then ls
      else l' :: ins_label l ls'
  end.

Fixpoint sort_labels (ls : list label) : list label :=
  match ls with
  | nil => nil
  | l :: ls' => ins_label l (sort_labels ls')
  end.

(* The labels of a record, each once, in ascending order. *)
Definition rec_labels (fs : fields) : list label := sort_labels (fs_labels fs).

(* The three-way result of comparing two values (ADR 0036).  Two records
   compare field by field in label order, each label read as its first field
   in either record, so the order the fields are written in does not matter.
   Two tags of one group compare by position in the declaration, then by
   payload; a [fold] compares as what it folds.  A Float inside a value relates to every result: a NaN's place is not
   modelled. *)
Inductive cmp_rel : exp -> exp -> comparison -> Prop :=
 | cr_int : forall a b, cmp_rel (e_num a) (e_num b) (z_cmp a b)
 | cr_float : forall x y c, fl_pair x y -> cmp_rel x y c
 | cr_str : forall p q, cmp_rel (e_str p) (e_str q) (str_compare p q)
 | cr_bool : forall x y a b,
     val_bool x = Some a -> val_bool y = Some b -> cmp_rel x y (bool_compare a b)
 | cr_unit : cmp_rel e_unit e_unit Eq
 | cr_fold : forall v1 v2 c, cmp_rel v1 v2 c -> cmp_rel (e_fold v1) (e_fold v2) c
 | cr_con_eq : forall w tg v1 v2 c,
     cmp_rel v1 v2 c -> cmp_rel (e_con w tg v1) (e_con w tg v2) c
 | cr_con_lt : forall w tg1 tg2 v1 v2,
     tg1 < tg2 -> cmp_rel (e_con w tg1 v1) (e_con w tg2 v2) Lt
 | cr_con_gt : forall w tg1 tg2 v1 v2,
     tg2 < tg1 -> cmp_rel (e_con w tg1 v1) (e_con w tg2 v2) Gt
 | cr_rec : forall fs1 fs2 c,
     cr_fields (rec_labels fs1) fs1 fs2 c -> cmp_rel (e_rec fs1) (e_rec fs2) c
with cr_fields : list label -> fields -> fields -> comparison -> Prop :=
 | cf_nil : forall fs1 fs2, cr_fields nil fs1 fs2 Eq
 | cf_eq : forall l ls fs1 fs2 v1 v2 c,
     lookup_first l fs1 = Some v1 -> lookup_first l fs2 = Some v2 ->
     cmp_rel v1 v2 Eq -> cr_fields ls fs1 fs2 c -> cr_fields (l :: ls) fs1 fs2 c
 | cf_ne : forall l ls fs1 fs2 v1 v2 c,
     lookup_first l fs1 = Some v1 -> lookup_first l fs2 = Some v2 ->
     cmp_rel v1 v2 c -> c <> Eq -> cr_fields (l :: ls) fs1 fs2 c.

#[export] Hint Constructors cmp_rel cr_fields : core.

(* What an operator computes from two values.  A relation, because a Float
   operation is unspecified: any Float, or for a comparison any Bool.  Every
   Int case has one answer, and none when the divisor is zero or the result
   leaves the 64-bit range (those trap, see [bin_trap]). *)
Inductive bin_step : bop -> exp -> exp -> exp -> Prop :=
 | bs_ring_int : forall o a b,
     kind o = k_ring -> in_int (ring_Z o a b) = true ->
     bin_step o (e_num a) (e_num b) (e_num (ring_Z o a b))
 | bs_whole : forall o a b,
     kind o = k_whole -> z_is_zero b = false -> in_int (whole_Z o a b) = true ->
     bin_step o (e_num a) (e_num b) (e_num (whole_Z o a b))
 | bs_float : forall o x y d,
     (kind o = k_ring \/ kind o = k_quot) -> fl_pair x y ->
     bin_step o x y (e_dec d)
 | bs_whole_float : forall o x y d,
     kind o = k_whole -> fl_pair x y -> bin_step o x y (e_dec d)
 | bs_quot_num : forall o a b d,
     kind o = k_quot -> bin_step o (e_num a) (e_num b) (e_dec d)
 | bs_cmp_float : forall o x y c,
     kind o = k_cmp -> fl_pair x y -> bin_step o x y (of_bool c)
 | bs_cmp : forall o a b c,
     kind o = k_cmp -> cmp_rel a b c ->
     bin_step o a b (of_bool (cmp_holds o c)).

(* Why a program stops: the defined runtime errors of the fragment. *)
Inductive trap_kind : Set := trap_div_zero | trap_overflow.

Inductive bin_trap : bop -> exp -> exp -> trap_kind -> Prop :=
 | bt_div_zero : forall o a b,
     kind o = k_whole -> z_is_zero b = true ->
     bin_trap o (e_num a) (e_num b) trap_div_zero
 | bt_ring_overflow : forall o a b,
     kind o = k_ring -> in_int (ring_Z o a b) = false ->
     bin_trap o (e_num a) (e_num b) trap_overflow
 | bt_whole_overflow : forall o a b,
     kind o = k_whole -> z_is_zero b = false -> in_int (whole_Z o a b) = false ->
     bin_trap o (e_num a) (e_num b) trap_overflow.

(* The types an operator accepts, and what it gives (ADR 0017, ADR 0036):
   [+ - * // %] are generic: they take two operands of one type that is
   [Numeric] in the kinding environment, a [Numeric] variable included; [/]
   takes two Floats and gives a Float; a comparison takes two of one type
   that is [Eq], and gives a Bool.  An [Int] [//] or [%] traps on a zero
   divisor; a [Float] one is unspecified like any Float operation, so IEEE's
   infinity and NaN fit.  The checker accepts an Int where a Float is wanted;
   elaboration inserts [e_tofloat] there, so the calculus has no mixed
   signature. *)
Inductive bin_sig : denv -> bop -> typ -> typ -> typ -> Prop :=
 | sig_ring : forall D o A,
     kind o = k_ring -> sat D k_Numeric A -> bin_sig D o A A A
 | sig_quot : forall D, bin_sig D bop_div typ_Float typ_Float typ_Float
 | sig_whole : forall D o A,
     kind o = k_whole -> sat D k_Numeric A -> bin_sig D o A A A
 | sig_quot_rec : forall D R, rfsat R ->
     bin_sig D bop_div (typ_Record R) (typ_Record R) (typ_Record R)
 | sig_cmp : forall D o B,
     kind o = k_cmp -> sat D k_Eq B -> bin_sig D o B B typ_Bool.

Lemma finer_trans : forall k1 k2 k3, finer k1 k2 -> finer k2 k3 -> finer k1 k3.
Proof.
  intros k1 k2 k3 H1 H2. inversion H1; subst; auto.
  all: inversion H2; subst; auto.
Qed.

Lemma finer_eqany : forall k k', finer k' k ->
  (k' = k_Any \/ k' = k_Eq) -> (k = k_Any \/ k = k_Eq).
Proof.
  intros k k' Hf H. destruct k, k'; try (inversion Hf; fail);
    first [ (left; reflexivity) | (right; reflexivity) | (destruct H as [H|H]; discriminate) ].
Qed.

Lemma finer_anyonly : forall k k', finer k' k -> k' = k_Any -> k = k_Any.
Proof. intros k k' Hf H. subst. inversion Hf; reflexivity. Qed.

Lemma sat_finer_mut : forall D,
  (forall T k k', finer k' k -> sat D k' T -> sat D k T) /\
  (forall R k k', finer k' k -> rsat D k' R -> rsat D k R).
Proof.
  intros D. apply typ_row_mutind; simpl.
  - intros k k' Hf _. exact I.
  - intros k k' Hf _. exact I.
  - intros k k' Hf. apply finer_eqany. exact Hf.
  - intros k k' Hf. apply finer_eqany. exact Hf.
  - intros k k' Hf. apply finer_eqany. exact Hf.
  - intros T1 _ T2 _ k k' Hf. apply finer_anyonly. exact Hf.
  - intros R H k k' Hf. destruct k, k'; try (inversion Hf; fail);
      first [ (intros _; exact I) | (intros H0; contradiction) | exact (H _ _ Hf) ].
  - intros a k k' Hf H. eapply finer_trans; eassumption.
  - intros i k k' Hf. apply finer_eqany. exact Hf.
  - intros T IH k k' Hf. destruct k, k'; try (inversion Hf; fail);
      first [ (intros _; exact I) | (intros H0; contradiction) | exact (IH _ _ Hf) ].
  - intros w T _ k k' Hf. destruct k, k'; try (inversion Hf; fail);
      first [ (intros _; exact I) | (intros H0; contradiction) | (intros H0; exact H0) ].
  - intros k k' Hf _. exact I.
  - intros r k k' Hf H. eapply finer_trans; eassumption.
  - intros l T H R H0 k k' Hf [H1 H2]. split; [ eapply H; eassumption | eapply H0; eassumption ].
  - intros l T1 _ T2 _ R _ k k' Hf H. eapply finer_anyonly; eassumption.
Qed.

Lemma sat_finer : forall D k k' T, finer k' k -> sat D k' T -> sat D k T.
Proof. intros D k k' T Hf H. exact (proj1 (sat_finer_mut D) T k k' Hf H). Qed.

(* A kind-respecting substitution keeps a type within its sort. *)
Lemma sat_ap_mut : forall D D' st sr,
  kres D D' st -> rkres D D' sr ->
  (forall T, (forall k, sat D k T -> sat D' k (ap_typ st sr T)) /\
             (forall w j, spine_sat D w j T -> spine_sat D' w j (ap_typ st sr T))) /\
  (forall R k, rsat D k R -> rsat D' k (ap_row st sr R)).
Proof.
  intros D D' st sr Hk Hr. apply typ_row_mutind; simpl; intros.
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - destruct H as [H1 _], H0 as [_ H0]. split; [ intros; assumption | ].
    intros w j [Hu Hs]. split; [ intros Hc; exact (H1 k_Eq (Hu Hc)) | exact (H0 w (S j) Hs) ].
  - split; [ | intros; contradiction ]. intros k. destruct k; simpl;
      first [ (intros _; exact I) | (intros HH; contradiction) | exact (H _) ].
  - split; [ intros k Hs; eapply sat_finer; [ exact Hs | apply Hk ] | intros; contradiction ].
  - split; intros; first [ assumption | contradiction ].
  - split; [ | intros; contradiction ]. intros k Hs. destruct k; try exact I; try contradiction.
    exact (proj1 H k_Eq Hs).
  - split; [ | intros; contradiction ]. intros k Hs. destruct k; try exact I; try contradiction.
    exact (proj2 H w 0 Hs).
  - exact I.
  - exact (proj2 (sat_finer_mut D') (sr r) k _ H (proj1 (Hr r))).
  - destruct H1 as [H1 H2]. split; [ exact (proj1 H k H1) | exact (H0 k H2) ].
  - exact H2.
Qed.

Lemma sat_ap : forall D D' k T st sr,
  kres D D' st -> rkres D D' sr -> sat D k T -> sat D' k (ap_typ st sr T).
Proof. intros. eapply (proj1 (proj1 (sat_ap_mut D D' st sr H H0) T)); eassumption. Qed.

Lemma sat_any : forall D T, sat D k_Any T.
Proof.
  intros D T. destruct T; simpl;
    first [ exact I | reflexivity | (left; reflexivity) | apply finer_any ].
Qed.

Lemma rsat_any : forall D R, rsat D k_Any R.
Proof.
  intros D R. induction R; simpl; auto using sat_any, finer_any.
Qed.

(* Every row variable of [R] has the kind the row-variable kind [rk_any]
   says, so an environment that gives every row variable that kind lets any
   row satisfy it. *)
Lemma rkok_any : forall D R, rkok D rk_any R.
Proof.
  intros D R. split; [ apply rsat_any | intros l H; discriminate H ].
Qed.

Lemma rkok_self : forall D r, rkok D (drk D r) (row_Var r).
Proof.
  intros D r. split; [ simpl; apply finer_refl | intros l H; simpl; exact H ].
Qed.

(* A row that lacks a label still lacks it after a substitution that respects
   the row variables' kinds. *)
Lemma rlacksD_ap_mut : forall (D D' : denv) (st : tsub) (sr : rsub) (l : label),
  rkres D D' sr ->
  (forall T : typ, True) /\
  (forall R, rlacksD D l R = true -> rlacksD D' l (ap_row st sr R) = true).
Proof.
  intros D D' st sr l Hr.
  apply typ_row_mutind; simpl; intros; try exact I; try discriminate; auto.
  - exact (proj2 (Hr r) l H).
  - apply Bool.andb_true_iff in H1 as [H1 H2]. rewrite H1. auto.
  - apply Bool.andb_true_iff in H2 as [H2 H3]. rewrite H2. auto.
Qed.

Lemma rlacksD_ap : forall D D' st sr l R,
  rkres D D' sr -> rlacksD D l R = true -> rlacksD D' l (ap_row st sr R) = true.
Proof. intros. apply (proj2 (rlacksD_ap_mut D D' st sr l H)); auto. Qed.

Lemma rkok_ap : forall (D D' : denv) (st : tsub) (sr : rsub) (K : rkind) (R : row),
  kres D D' st -> rkres D D' sr -> rkok D K R -> rkok D' K (ap_row st sr R).
Proof.
  intros D D' st sr K R Hk Hr [H1 H2]. split.
  - exact (proj2 (sat_ap_mut D D' st sr Hk Hr) R _ H1).
  - intros l Hl. eapply rlacksD_ap; [ exact Hr | apply H2; exact Hl ].
Qed.

(* A closed record of [Float]s has no variables to substitute. *)
Lemma fsat_ap_mut : forall st sr,
  (forall T, fsat T -> ap_typ st sr T = T) /\
  (forall R, rfsat R -> ap_row st sr R = R).
Proof.
  intros st sr. apply typ_row_mutind; simpl; intros; try contradiction; try reflexivity.
  - rewrite H by assumption. reflexivity.
  - destruct H1 as [H1 H2]. rewrite H by assumption. rewrite H0 by assumption. reflexivity.
Qed.

(* The signature of an operator at the substituted types. *)
Lemma bin_sig_ap : forall D D' o A B R st sr,
  kres D D' st -> rkres D D' sr -> bin_sig D o A B R ->
  bin_sig D' o (ap_typ st sr A) (ap_typ st sr B) (ap_typ st sr R).
Proof.
  intros D D' o A B R st sr Hk Hr H.
  destruct H; simpl.
  - apply sig_ring; [ assumption | eapply sat_ap; eassumption ].
  - apply sig_quot.
  - apply sig_whole; [ assumption | eapply sat_ap; eassumption ].
  - rewrite (proj2 (fsat_ap_mut st sr) R H). apply sig_quot_rec; assumption.
  - apply sig_cmp; [ assumption | eapply sat_ap; eassumption ].
Qed.

(* ================================================================== *)
(* Small-step, call-by-value, left-to-right (section 6).                 *)
(* No local-closure side conditions: the soundness theorems quantify over  *)
(* well-typed terms, and every typeable term is locally closed            *)
(* (GoatMeta.typing_regular), so reduction need not re-assert it.  [open]   *)
(* is the capture-avoiding substitution of the single bound variable.       *)
(* ================================================================== *)

(* The field-wise operator on two records (ADR 0012): each field of the first
   record meets the first field of the second with its label, in the first
   record's order; the second record's field is then spent.  The result is a
   record of operator applications, which the field rules then evaluate, so a
   trap in one field is the record's trap.  Typing leaves nothing of the
   second record once the first is used up. *)
Inductive rec_zip (o : bop) : fields -> fields -> fields -> Prop :=
 | rz_nil : forall fs2, rec_zip o fs_nil fs2 fs_nil
 | rz_cons : forall l v1 r1 fs2 v2 rs,
     lookup_first l fs2 = Some v2 ->
     rec_zip o r1 (fs_drop l fs2) rs ->
     rec_zip o (fs_cons l v1 r1) fs2 (fs_cons l (e_bin v1 o v2) rs).

#[export] Hint Constructors rec_zip : core.

Inductive step : exp -> exp -> Prop :=
 | st_beta : forall e v,
     value v ->
     step (e_app (e_abs e) v) (open_exp_wrt_exp e v)
 | st_app1 : forall e1 e1' e2,
     step e1 e1' -> step (e_app e1 e2) (e_app e1' e2)
 | st_app2 : forall v e2 e2',
     value v -> step e2 e2' -> step (e_app v e2) (e_app v e2')
 | st_letv : forall v e2,
     value v ->
     step (e_let v e2) (open_exp_wrt_exp e2 v)
 | st_let1 : forall e1 e1' e2,
     step e1 e1' -> step (e_let e1 e2) (e_let e1' e2)
 | st_letrec : forall fs e2,
     fn_group fs ->
     step (e_letrec fs e2)
       (open_exp_wrt_exp e2
          (e_rec (open_fields_wrt_exp fs (e_letrec fs (e_fvar_b 0)))))
 | st_proj : forall e e' l,
     step e e' -> step (e_proj e l) (e_proj e' l)
 | st_projrec : forall fs l v,
     rec_value fs -> lookup_first l fs = Some v ->
     step (e_proj (e_rec fs) l) v
 | st_rec : forall fs fs',
     step_fields fs fs' -> step (e_rec fs) (e_rec fs')
 | st_ite1 : forall e1 e1' e2 e3,
     step e1 e1' -> step (e_ite e1 e2 e3) (e_ite e1' e2 e3)
 | st_ite_true : forall e2 e3, step (e_ite e_true e2 e3) e2
 | st_ite_false : forall e2 e3, step (e_ite e_false e2 e3) e3
 | st_bin1 : forall e1 e1' o e2,
     step e1 e1' -> step (e_bin e1 o e2) (e_bin e1' o e2)
 | st_bin2 : forall v o e2 e2',
     value v -> step e2 e2' -> step (e_bin v o e2) (e_bin v o e2')
 | st_bin : forall v1 o v2 v,
     value v1 -> value v2 -> bin_step o v1 v2 v ->
     step (e_bin v1 o v2) v
 | st_binrec : forall fs1 o fs2 fs,
     kind o <> k_cmp -> rec_value fs1 -> rec_value fs2 -> rec_zip o (fs_plain fs1) (fs_plain fs2) fs ->
     step (e_bin (e_rec fs1) o (e_rec fs2)) (e_rec fs)
 | st_tofloat1 : forall e e', step e e' -> step (e_tofloat e) (e_tofloat e')
 | st_tofloat : forall z d, step (e_tofloat (e_num z)) (e_dec d)
 | st_tofloat_dec : forall d, step (e_tofloat (e_dec d)) (e_dec d)
 | st_spread1 : forall e1 e1' l e2,
     step e1 e1' -> step (e_spread e1 l e2) (e_spread e1' l e2)
 | st_spread2 : forall v1 l e2 e2',
     value v1 -> step e2 e2' -> step (e_spread v1 l e2) (e_spread v1 l e2')
 | st_spread : forall fs l v,
     rec_value fs -> value v ->
     step (e_spread (e_rec fs) l v) (e_rec (fs_plain (fs_set l v fs)))
 | st_restrict1 : forall e e' l,
     step e e' -> step (e_restrict e l) (e_restrict e' l)
 | st_restrict : forall fs l,
     rec_value fs -> step (e_restrict (e_rec fs) l) (e_rec (fs_plain (fs_drop l fs)))
 | st_fold1 : forall e e', step e e' -> step (e_fold e) (e_fold e')
 | st_unfold1 : forall e e', step e e' -> step (e_unfold e) (e_unfold e')
 | st_unfold_fold : forall v, value v -> step (e_unfold (e_fold v)) v
 | st_con1 : forall w tg e e', step e e' -> step (e_con w tg e) (e_con w tg e')
 | st_match1 : forall w e e' ars,
     step e e' -> step (e_match w e ars) (e_match w e' ars)
 | st_match_arm : forall w w' tg v ars body,
     value v -> arms_find tg ars = Some body ->
     step (e_match w (e_con w' tg v) ars) (open_exp_wrt_exp body v)
 | st_match_else : forall w w' tg v ars e0,
     value v -> arms_find tg ars = None -> arms_default ars = Some e0 ->
     step (e_match w (e_con w' tg v) ars) e0
with step_fields : fields -> fields -> Prop :=
 | stf_here : forall l e e' fs,
     step e e' -> step_fields (fs_cons l e fs) (fs_cons l e' fs)
 | stf_cons : forall l v fs fs',
     value v -> step_fields fs fs' -> step_fields (fs_cons l v fs) (fs_cons l v fs')
 | stf_meth_here : forall l e e' fs,
     step e e' -> step_fields (fs_meth l e fs) (fs_meth l e' fs)
 | stf_meth_cons : forall l v fs fs',
     value v -> step_fields fs fs' -> step_fields (fs_meth l v fs) (fs_meth l v fs').

#[export] Hint Constructors step step_fields : core.

(* A runtime trap: the same evaluation order as [step], with the error
   rising out of the one operator that raises it.  Progress says a well-typed
   term is a value, steps, or traps. *)
Inductive traps : exp -> trap_kind -> Prop :=
 | tr_app1 : forall e1 e2 k, traps e1 k -> traps (e_app e1 e2) k
 | tr_app2 : forall v e2 k, value v -> traps e2 k -> traps (e_app v e2) k
 | tr_let1 : forall e1 e2 k, traps e1 k -> traps (e_let e1 e2) k
 | tr_proj : forall e l k, traps e k -> traps (e_proj e l) k
 | tr_rec : forall fs k, traps_fields fs k -> traps (e_rec fs) k
 | tr_ite1 : forall e1 e2 e3 k, traps e1 k -> traps (e_ite e1 e2 e3) k
 | tr_bin1 : forall e1 o e2 k, traps e1 k -> traps (e_bin e1 o e2) k
 | tr_bin2 : forall v o e2 k,
     value v -> traps e2 k -> traps (e_bin v o e2) k
 | tr_tofloat : forall e k, traps e k -> traps (e_tofloat e) k
 | tr_spread1 : forall e1 l e2 k, traps e1 k -> traps (e_spread e1 l e2) k
 | tr_spread2 : forall v1 l e2 k,
     value v1 -> traps e2 k -> traps (e_spread v1 l e2) k
 | tr_restrict : forall e l k, traps e k -> traps (e_restrict e l) k
 | tr_fold : forall e k, traps e k -> traps (e_fold e) k
 | tr_unfold : forall e k, traps e k -> traps (e_unfold e) k
 | tr_con : forall w tg e k, traps e k -> traps (e_con w tg e) k
 | tr_match : forall w e ars k, traps e k -> traps (e_match w e ars) k
 | tr_bin : forall v1 o v2 k,
     value v1 -> value v2 -> bin_trap o v1 v2 k -> traps (e_bin v1 o v2) k
with traps_fields : fields -> trap_kind -> Prop :=
 | trf_here : forall l e fs k, traps e k -> traps_fields (fs_cons l e fs) k
 | trf_cons : forall l v fs k,
     value v -> traps_fields fs k -> traps_fields (fs_cons l v fs) k
 | trf_meth_here : forall l e fs k, traps e k -> traps_fields (fs_meth l e fs) k
 | trf_meth_cons : forall l v fs k,
     value v -> traps_fields fs k -> traps_fields (fs_meth l v fs) k.

#[export] Hint Constructors traps traps_fields : core.

(* [unroll_eq n T T'] holds when T and T' are equal after at most [n]
   unrollings of a mu on either side, at any depth of the types.  Equality
   up to [teq] is free, and budgets add along a chain of equalities.  A
   reordering or a presence rewrite of rows is [req], which is free too.  There
   is no mu/mu congruence rule: two unequal mus are compared by unrolling. *)
Inductive unroll_eq : nat -> typ -> typ -> Prop :=
 | UE_teq : forall n T T', teq T T' -> unroll_eq n T T'
 | UE_trans : forall m n T1 T2 T3,
     unroll_eq m T1 T2 -> unroll_eq n T2 T3 -> unroll_eq (m + n) T1 T3
 | UE_unfold : forall n B, unroll_eq (S n) (typ_Mu B) (open_typ 0 (typ_Mu B) B)
 | UE_fold : forall n B, unroll_eq (S n) (open_typ 0 (typ_Mu B) B) (typ_Mu B)
 | UE_arrow : forall n T1 T1' T2 T2',
     unroll_eq n T1 T1' -> unroll_eq n T2 T2' ->
     unroll_eq n (typ_Arrow T1 T2) (typ_Arrow T1' T2')
 | UE_record : forall n R R', unroll_row n R R' -> unroll_eq n (typ_Record R) (typ_Record R')
 | UE_grp : forall n w T T', unroll_eq n T T' -> unroll_eq n (typ_Grp w T) (typ_Grp w T')
with unroll_row : nat -> row -> row -> Prop :=
 | UR_req : forall n R R', req R R' -> unroll_row n R R'
 | UR_trans : forall m n R1 R2 R3,
     unroll_row m R1 R2 -> unroll_row n R2 R3 -> unroll_row (m + n) R1 R3
 | UR_ext : forall n l T T' R R',
     unroll_eq n T T' -> unroll_row n R R' ->
     unroll_row n (row_Ext l T R) (row_Ext l T' R')
 | UR_maybe : forall n l P P' T T' R R',
     unroll_eq n P P' -> unroll_eq n T T' -> unroll_row n R R' ->
     unroll_row n (row_Maybe l P T R) (row_Maybe l P' T' R').

#[export] Hint Constructors unroll_eq unroll_row : core.

Scheme unroll_eq_ind' := Induction for unroll_eq Sort Prop
  with unroll_row_ind' := Induction for unroll_row Sort Prop.
Combined Scheme unroll_mutind from unroll_eq_ind', unroll_row_ind'.

(* The methods of a record literal share one receiver (ADR 0034 decision 2):
   the literal's own fields at their types, and a row [Rt] for what a use
   adds.  [row_tail_with R Rt] is [R] with [Rt] for its empty tail, and
   [meths_shared Rs fs R] says each method field of [fs], whose type in the
   row [R] is [T], is a function of that receiver [Rs], up to unrolling. *)
Fixpoint row_tail_with (R Rt : row) {struct R} : row :=
  match R with
  | row_Empty => Rt
  | row_Var a => row_Var a
  | row_Ext l T R' => row_Ext l T (row_tail_with R' Rt)
  | row_Maybe l P T R' => row_Maybe l P T (row_tail_with R' Rt)
  end.

Inductive meths_shared (Rs : row) : fields -> row -> Prop :=
 | MS_nil : meths_shared Rs fs_nil row_Empty
 | MS_cons : forall l e fs T R,
     meths_shared Rs fs R -> meths_shared Rs (fs_cons l e fs) (row_Ext l T R)
 | MS_meth : forall l e fs T R n Rr,
     unroll_eq n T (typ_Arrow (typ_Record Rs) Rr) ->
     meths_shared Rs fs R -> meths_shared Rs (fs_meth l e fs) (row_Ext l T R).

#[export] Hint Constructors meths_shared : core.

(* ================================================================== *)
(* Declarative typing (section 4), mutual with record-field typing.      *)
(* Binder rules are cofinite.  The leaf rules carry [uniq G] so that a     *)
(* derivable judgment has a well-formed context.                           *)
(* ================================================================== *)

Inductive typing : denv -> ctx -> exp -> typ -> Prop :=
 | T_Var : forall D G x s T,
     uniq G -> binds x s G -> inst D T s -> typing D G (e_fvar_f x) T
 | T_Num : forall D G n T, uniq G -> sat D k_Literal T -> typing D G (e_num n) T
 | T_Dec : forall D G d, uniq G -> typing D G (e_dec d) typ_Float
 | T_True : forall D G, uniq G -> typing D G e_true typ_Bool
 | T_False : forall D G, uniq G -> typing D G e_false typ_Bool
 | T_Abs : forall (L : vars) D G e T1 T2,
     (forall x, x `notin` L ->
        typing D ((x ~ sch_mono T1) ++ G) (open_exp_wrt_exp e (e_fvar_f x)) T2) ->
     typing D G (e_abs e) (typ_Arrow T1 T2)
 | T_App : forall D G e1 e2 T1 T2,
     typing D G e1 (typ_Arrow T1 T2) ->
     typing D G e2 T1 ->
     typing D G (e_app e1 e2) T2
 | T_Let : forall (L : vars) D G e1 e2 T1 T2 (k : sort_fn) (rk : rkind_fn) (Tm : typ),
     is_gen_value e1 = true ->
     lit_pinned e1 (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G))) k ->
     typing (extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G))) k)
                  (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G))) rk) G e1 T1 ->
     (forall x, x `notin` L ->
        typing D ((x ~ gen (pin_ctx Tm G) T1 k rk) ++ G) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
     typing D G (e_let e1 e2) T2
 | T_LetMono : forall (L : vars) D G e1 e2 T1 T2,
     typing D G e1 T1 ->
     (forall x, x `notin` L ->
        typing D ((x ~ sch_mono T1) ++ G) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
     typing D G (e_let e1 e2) T2
 | T_Letrec : forall (L : vars) D G fs e2 R T (k : sort_fn) (rk : rkind_fn),
     fn_group fs ->
     (forall p, p `notin` L ->
        field_typing (extr (ext D (AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G)) k)
                           (AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G)) rk)
          ((p ~ sch_mono (typ_Record R)) ++ G)
          (open_fields_wrt_exp fs (e_fvar_f p)) R) ->
     (forall p, p `notin` L ->
        typing D ((p ~ gen G (typ_Record R) k rk) ++ G) (open_exp_wrt_exp e2 (e_fvar_f p)) T) ->
     typing D G (e_letrec fs e2) T
 | T_Record : forall D G fs R,
     field_typing D G fs R -> no_meth fs = true ->
     typing D G (e_rec fs) (typ_Record R)
 | T_Obj : forall D G fs R Rt,
     field_typing D G fs R -> meths_shared (row_tail_with R Rt) fs R ->
     typing D G (e_rec fs) (typ_Record R)
 | T_Proj : forall D G e l T R,
     typing D G e (typ_Record (row_Ext l T R)) -> typing D G (e_proj e l) T
 | T_Conv : forall D G e T T',
     typing D G e T -> teq T T' -> typing D G e T'
 | T_Unit : forall D G, uniq G -> typing D G e_unit typ_Unit
 | T_Str : forall D G q, uniq G -> typing D G (e_str q) typ_String
 | T_If : forall D G e1 e2 e3 T,
     typing D G e1 typ_Bool -> typing D G e2 T -> typing D G e3 T ->
     typing D G (e_ite e1 e2 e3) T
 | T_ToFloat : forall D G e A,
     typing D G e A -> sat D k_Literal A -> typing D G (e_tofloat e) typ_Float
 | T_Bin : forall D G e1 o e2 A B R,
     typing D G e1 A -> typing D G e2 B -> bin_sig D o A B R ->
     typing D G (e_bin e1 o e2) R
 | T_Spread : forall D G e1 l e2 P T R,
     typing D G e1 (typ_Record (row_Maybe l P T R)) ->
     typing D G e2 T ->
     typing D G (e_spread e1 l e2) (typ_Record (row_Ext l T R))
 | T_SpreadL : forall D G e1 l e2 T R,
     typing D G e1 (typ_Record R) -> rlacksD D l R = true ->
     typing D G e2 T ->
     typing D G (e_spread e1 l e2) (typ_Record (row_Ext l T R))
 | T_Restrict : forall D G e l R0 T R,
     typing D G e (typ_Record R0) -> rm l R0 T R ->
     typing D G (e_restrict e l) (typ_Record R)
 | T_Fold : forall D G e B,
     lct 0 (typ_Mu B) -> guarded B ->
     typing D G e (open_typ 0 (typ_Mu B) B) -> typing D G (e_fold e) (typ_Mu B)
 | T_Unfold : forall D G e B,
     lct 0 (typ_Mu B) -> guarded B ->
     typing D G e (typ_Mu B) -> typing D G (e_unfold e) (open_typ 0 (typ_Mu B) B)
 | T_Con : forall D G w tg e Ts,
     tg < length w ->
     typing D G e (tag_payload w Ts tg) ->
     typing D G (e_con w tg e) (typ_Grp w (spine Ts))
 | T_Match : forall (L : vars) D G w Ts e ars T,
     typing D G e (typ_Grp w (spine Ts)) ->
     arms_wf w ars ->
     (forall tg body, arms_find tg ars = Some body ->
        forall x, x `notin` L ->
          typing D ((x ~ sch_mono (tag_payload w Ts tg)) ++ G)
            (open_exp_wrt_exp body (e_fvar_f x)) T) ->
     (forall e0, arms_default ars = Some e0 -> typing D G e0 T) ->
     typing D G (e_match w e ars) T
with field_typing : denv -> ctx -> fields -> row -> Prop :=
 | FT_nil : forall D G, uniq G -> field_typing D G fs_nil row_Empty
 | FT_cons : forall D G l e T fs R,
     typing D G e T -> field_typing D G fs R ->
     field_typing D G (fs_cons l e fs) (row_Ext l T R)
 | FT_meth : forall D G l e T fs R,
     typing D G e T -> field_typing D G fs R ->
     field_typing D G (fs_meth l e fs) (row_Ext l T R).

#[export] Hint Constructors typing field_typing : core.

Lemma no_meth_plain : forall fs, no_meth (fs_plain fs) = true.
Proof. induction fs as [|l e fs IH|l e fs IH]; simpl; auto. Qed.

Lemma lookup_first_plain : forall l fs, lookup_first l (fs_plain fs) = lookup_first l fs.
Proof. induction fs as [|l' e fs IH|l' e fs IH]; simpl; auto; destruct (Nat.eqb l l'); auto. Qed.

Lemma field_typing_fs_plain : forall D G fs R,
  field_typing D G fs R -> field_typing D G (fs_plain fs) R.
Proof. intros D G fs R H. induction H; simpl; auto. Qed.

(* The row of a record literal is a spine of [Ext] entries ending in [Empty]. *)
Fixpoint plain_spine (R : row) : bool :=
  match R with
  | row_Empty => true
  | row_Ext _ _ R' => plain_spine R'
  | _ => false
  end.

Lemma field_typing_plain_spine : forall D G fs R,
  field_typing D G fs R -> plain_spine R = true.
Proof. intros D G fs R H. induction H; simpl; auto. Qed.

(* Which fields of a spine are methods.  Substitution and a step in a field
   keep it, and it is all that [no_meth] and [meths_shared] read. *)
Fixpoint marks (fs : fields) : list (bool * label) :=
  match fs with
  | fs_nil => nil
  | fs_cons l _ fs' => (false, l) :: marks fs'
  | fs_meth l _ fs' => (true, l) :: marks fs'
  end.

Lemma no_meth_marks : forall fs fs', marks fs = marks fs' -> no_meth fs = no_meth fs'.
Proof.
  induction fs as [|l e fs IH|l e fs IH]; intros [|l' e' fs'|l' e' fs'] H; simpl in *;
    try discriminate; try reflexivity;
    injection H as _ H; apply IH; exact H.
Qed.

Lemma meths_shared_marks : forall Rs fs R fs',
  meths_shared Rs fs R -> marks fs = marks fs' -> meths_shared Rs fs' R.
Proof.
  intros Rs fs R fs' H. revert fs'. induction H; intros fs' Hm;
    destruct fs' as [|l' e' fs'|l' e' fs']; try discriminate Hm.
  - apply MS_nil.
  - simpl in Hm. injection Hm as Hl Hm. subst. apply MS_cons. auto.
  - simpl in Hm. injection Hm as Hl Hm. subst. eapply MS_meth; [ exact H | auto ].
Qed.

Lemma marks_subst_fields : forall fs u x, marks (subst_fields u x fs) = marks fs.
Proof.
  induction fs as [|l e fs IH|l e fs IH]; intros; simpl; auto; rewrite IH; reflexivity.
Qed.

Lemma fs_plain_drop : forall l fs, fs_plain (fs_drop l fs) = fs_drop l (fs_plain fs).
Proof.
  intros l. induction fs as [|l' e fs IH|l' e fs IH]; simpl; auto;
    destruct (Nat.eqb l l'); simpl; auto; rewrite IH; reflexivity.
Qed.

Lemma marks_open_fields : forall fs k u, marks (open_fields_wrt_exp_rec k u fs) = marks fs.
Proof.
  induction fs as [|l e fs IH|l e fs IH]; intros; simpl; auto; rewrite IH; reflexivity.
Qed.

Lemma fn_group_no_meth : forall fs, fn_group fs -> no_meth fs = true.
Proof. intros fs H. induction H; simpl; auto. Qed.

(* A record literal is typed by T_Record when it has no method field and by
   T_Obj otherwise; [rec_ok] is the side condition either rule asks. *)
Definition rec_ok (fs : fields) (R : row) : Prop :=
  no_meth fs = true \/ exists Rt, meths_shared (row_tail_with R Rt) fs R.

Lemma rec_ok_marks : forall fs R fs', rec_ok fs R -> marks fs = marks fs' -> rec_ok fs' R.
Proof.
  intros fs R fs' [H | [Rt H]] Hm.
  - left. rewrite <- (no_meth_marks _ _ Hm). exact H.
  - right. exists Rt. eapply meths_shared_marks; eauto.
Qed.

Lemma T_rec_ok : forall D G fs R,
  field_typing D G fs R -> rec_ok fs R -> typing D G (e_rec fs) (typ_Record R).
Proof.
  intros D G fs R Hf [H | [Rt H]]; [ apply T_Record | eapply T_Obj ]; eauto.
Qed.

Lemma marks_step_fields : forall fs fs', step_fields fs fs' -> marks fs' = marks fs.
Proof. intros fs fs' H. induction H; simpl; try rewrite IHstep_fields; reflexivity. Qed.

(* Reflexive-transitive closure, for the soundness corollary. *)
Inductive multistep : exp -> exp -> Prop :=
 | ms_refl : forall e, multistep e e
 | ms_step : forall e1 e2 e3, step e1 e2 -> multistep e2 e3 -> multistep e1 e3.

(* A term is stuck if it is not a value, cannot step, and raises no error
   (section 7). *)
Definition stuck (e : exp) : Prop :=
  ~ value e /\ (forall e', ~ step e e') /\ (forall k, ~ traps e k).
