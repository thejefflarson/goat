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
Require Import Goat.GoatNum.
Require Import Goat.GoatLit.

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
  end
with ap_row (st : tsub) (sr : rsub) (R : row) {struct R} : row :=
  match R with
  | row_Empty => row_Empty
  | row_Var r => sr r
  | row_Ext l T R' => row_Ext l (ap_typ st sr T) (ap_row st sr R')
  end.

Definition idt : tsub := fun a => typ_Var a.
Definition idr : rsub := fun r => row_Var r.

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
  end
with ftv_row (R : row) {struct R} : atoms :=
  match R with
  | row_Empty => {}
  | row_Var _ => {}
  | row_Ext _ T R' => ftv_typ T `union` ftv_row R'
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
  end
with frv_row (R : row) {struct R} : atoms :=
  match R with
  | row_Empty => {}
  | row_Var s => {{s}}
  | row_Ext _ T R' => frv_typ T `union` frv_row R'
  end.

(* Membership wrappers: the metatheory is phrased with these predicates, and
   their proofs [unfold] to a finite-set membership that [fsetdec] discharges. *)
Definition Ftv_typ (T : typ) (a : typvar) : Prop := a `in` ftv_typ T.
Definition Frv_typ (T : typ) (r : rowvar) : Prop := r `in` frv_typ T.

(* ================================================================== *)
(* Sorts (ADR 0037, phase 2).  A type variable has a sort: [Any] stands   *)
(* for any type, [Numeric] and [Literal] for [Int] or [Float].  A         *)
(* [Literal] variable is also [Numeric], so one sort is finer than another *)
(* when its variables may stand wherever the other is asked.  The sort of  *)
(* a free variable comes from a kinding environment [denv], a total map    *)
(* that is [Any] outside a finite support; a quantified variable's sort    *)
(* is recorded in its scheme.                                              *)
(* ================================================================== *)

Inductive sort : Set := k_Any | k_Numeric | k_Literal.

Inductive finer : sort -> sort -> Prop :=
 | finer_refl : forall k, finer k k
 | finer_any : forall k, finer k k_Any
 | finer_lit : forall k, finer k_Literal k.

#[export] Hint Constructors finer : core.

Definition sort_fn := typvar -> sort.
Definition denv := typvar -> sort.

(* [sat D k T]: T may stand where a variable of sort [k] stands.  A concrete
   [Int] or [Float] satisfies every sort; any other type only [Any]; a
   variable satisfies the sorts its own (in [D]) is finer than. *)
Definition sat (D : denv) (k : sort) (T : typ) : Prop :=
  match T with
  | typ_Int | typ_Float => True
  | typ_Var a => finer (D a) k
  | _ => k = k_Any
  end.

(* A substitution from one environment to another gives each variable a type
   of its sort. *)
Definition kres (D D' : denv) (st : tsub) : Prop := forall a, sat D' (D a) (st a).

(* The environment D, extended on V by the sorts k. *)
Definition ext (D : denv) (V : atoms) (k : sort_fn) : denv :=
  fun a => if AtomSetImpl.mem a V then k a else D a.

Definition supp_ok (D : denv) (S : atoms) : Prop := forall a, a `notin` S -> D a = k_Any.

Definition d_any : denv := fun _ => k_Any.

(* ================================================================== *)
(* Type schemes (section 5): a quantified set of type and row variables  *)
(* over a monotype body.  Quantified sets are finite [atoms]; a monotype  *)
(* scheme quantifies nothing.                                            *)
(* ================================================================== *)

Record scheme : Type := Sch {
  s_tq : atoms;
  s_rq : atoms;
  s_body : typ;
  s_sk : sort_fn
}.

Definition sch_mono (T : typ) : scheme := Sch {} {} T (fun _ => k_Any).

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
    (forall a, a `in` s_tq s -> sat D (s_sk s a) (st a)).

(* ================================================================== *)
(* Generalization (section 5): quantify exactly the variables free in     *)
(* the type but not in the context.                                        *)
(* ================================================================== *)

Definition gen (G : ctx) (T : typ) (k : sort_fn) : scheme :=
  Sch (AtomSetImpl.diff (ftv_typ T) (ftv_ctx G))
      (AtomSetImpl.diff (frv_typ T) (frv_ctx G))
      T k.

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
 | v_rec : forall fs, rec_value fs -> value (e_rec fs)
with rec_value : fields -> Prop :=
 | rv_nil : rec_value fs_nil
 | rv_cons : forall l v fs,
     value v -> rec_value fs -> rec_value (fs_cons l v fs).

#[export] Hint Constructors value rec_value : core.

(* First field labeled [l] (matches rewrite_row / ST-ProjRec's side cond). *)
Fixpoint lookup_first (l : label) (fs : fields) : option exp :=
  match fs with
  | fs_nil => None
  | fs_cons l' e fs' => if Nat.eqb l l' then Some e else lookup_first l fs'
  end.

(* The value restriction (ADR 0027): a [let] generalizes its binding only when
   the bound term is a syntactic value, one whose evaluation does no work: unit,
   a literal, a name, a function, or a record of those.  (The checker's
   builtins are names here; variants and spreads join with their phases.)  A
   recursive group of functions around a value is one too, as in ML's
   nonexpansive terms: unrolling the group only rewrites it.  That case is what
   lets a name bound to the unrolled group stay generalizable after
   substitution.  So is the coercion of a value, the [float(n)] elaboration
   writes where the checker widens a literal. *)
Fixpoint is_gen_value (e : exp) {struct e} : bool :=
  match e with
  | e_fvar_b _ | e_fvar_f _ | e_num _ | e_dec _ | e_true | e_false
  | e_unit | e_str _ | e_abs _ => true
  | e_rec fs => is_gen_fields fs
  | e_letrec fs e2 => is_gen_fields fs && is_gen_value e2
  | e_tofloat e1 => is_gen_value e1
  | _ => false
  end
with is_gen_fields (fs : fields) {struct fs} : bool :=
  match fs with
  | fs_nil => true
  | fs_cons _ e fs' => is_gen_value e && is_gen_fields fs'
  end.

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
 | bs_quot_num : forall o a b d,
     kind o = k_quot -> bin_step o (e_num a) (e_num b) (e_dec d)
 | bs_cmp_int : forall o a b,
     kind o = k_cmp ->
     bin_step o (e_num a) (e_num b) (of_bool (cmp_holds o (z_cmp a b)))
 | bs_cmp_float : forall o x y c,
     kind o = k_cmp -> fl_pair x y -> bin_step o x y (of_bool c)
 | bs_cmp_str : forall o p q,
     kind o = k_cmp ->
     bin_step o (e_str p) (e_str q) (of_bool (cmp_holds o (str_compare p q)))
 | bs_cmp_bool : forall o x y a b,
     kind o = k_cmp -> val_bool x = Some a -> val_bool y = Some b ->
     bin_step o x y (of_bool (cmp_holds o (bool_compare a b))).

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
   [+ - *] take two Ints or two Floats; [/] takes two Floats and gives a
   Float; [//] and [%] take two Ints; a comparison takes two of one of Int,
   Float, String or Bool.  [+ - *] are generic: they take two operands of one
   type that is [Numeric] in the kinding environment, a [Numeric] variable
   included.  The checker accepts an Int where a Float is wanted; elaboration
   inserts [e_tofloat] there, so the calculus has no mixed signature.  A
   comparison is at concrete types: a generic one waits for the [Eq] and
   [Ordered] sorts. *)
Inductive cmp_typ : typ -> Prop :=
 | ct_int : cmp_typ typ_Int
 | ct_float : cmp_typ typ_Float
 | ct_string : cmp_typ typ_String
 | ct_bool : cmp_typ typ_Bool.

Inductive bin_sig : denv -> bop -> typ -> typ -> typ -> Prop :=
 | sig_ring : forall D o A,
     kind o = k_ring -> sat D k_Numeric A -> bin_sig D o A A A
 | sig_quot : forall D, bin_sig D bop_div typ_Float typ_Float typ_Float
 | sig_whole : forall D o,
     kind o = k_whole -> bin_sig D o typ_Int typ_Int typ_Int
 | sig_cmp : forall D o B,
     kind o = k_cmp -> cmp_typ B -> bin_sig D o B B typ_Bool.

#[export] Hint Constructors cmp_typ : core.

Lemma finer_trans : forall k1 k2 k3, finer k1 k2 -> finer k2 k3 -> finer k1 k3.
Proof.
  intros k1 k2 k3 H1 H2. inversion H1; subst; auto.
  inversion H2; subst; auto.
Qed.

Lemma sat_finer : forall D k k' T, finer k' k -> sat D k' T -> sat D k T.
Proof.
  intros D k k' T Hf H. destruct T; simpl in *; try exact I.
  all: try (subst; inversion Hf; subst; auto; fail).
  eapply finer_trans; eauto.
Qed.

(* A kind-respecting substitution keeps a type within its sort. *)
Lemma sat_ap : forall D D' k T st sr,
  kres D D' st -> sat D k T -> sat D' k (ap_typ st sr T).
Proof.
  intros D D' k T st sr Hk H. destruct T; simpl in *; try exact H.
  eapply sat_finer; [ exact H | apply Hk ].
Qed.

Lemma sat_any : forall D T, sat D k_Any T.
Proof. intros D T. destruct T; simpl; try reflexivity. apply finer_any. Qed.

(* The signature of an operator at the substituted types. *)
Lemma bin_sig_ap : forall D D' o A B R st sr,
  kres D D' st -> bin_sig D o A B R ->
  bin_sig D' o (ap_typ st sr A) (ap_typ st sr B) (ap_typ st sr R).
Proof.
  intros D D' o A B R st sr Hk H.
  assert (Hc : forall N, cmp_typ N -> ap_typ st sr N = N)
    by (intros N HN; destruct HN; reflexivity).
  destruct H; simpl.
  - apply sig_ring; [ assumption | eapply sat_ap; eassumption ].
  - apply sig_quot.
  - apply sig_whole; assumption.
  - rewrite (Hc B H0). apply sig_cmp; assumption.
Qed.

(* ================================================================== *)
(* Small-step, call-by-value, left-to-right (section 6).                 *)
(* No local-closure side conditions: the soundness theorems quantify over  *)
(* well-typed terms, and every typeable term is locally closed            *)
(* (GoatMeta.typing_regular), so reduction need not re-assert it.  [open]   *)
(* is the capture-avoiding substitution of the single bound variable.       *)
(* ================================================================== *)

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
 | st_tofloat1 : forall e e', step e e' -> step (e_tofloat e) (e_tofloat e')
 | st_tofloat : forall z d, step (e_tofloat (e_num z)) (e_dec d)
 | st_tofloat_dec : forall d, step (e_tofloat (e_dec d)) (e_dec d)
with step_fields : fields -> fields -> Prop :=
 | stf_here : forall l e e' fs,
     step e e' -> step_fields (fs_cons l e fs) (fs_cons l e' fs)
 | stf_cons : forall l v fs fs',
     value v -> step_fields fs fs' -> step_fields (fs_cons l v fs) (fs_cons l v fs').

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
 | tr_bin : forall v1 o v2 k,
     value v1 -> value v2 -> bin_trap o v1 v2 k -> traps (e_bin v1 o v2) k
with traps_fields : fields -> trap_kind -> Prop :=
 | trf_here : forall l e fs k, traps e k -> traps_fields (fs_cons l e fs) k
 | trf_cons : forall l v fs k,
     value v -> traps_fields fs k -> traps_fields (fs_cons l v fs) k.

#[export] Hint Constructors traps traps_fields : core.

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
 | T_Let : forall (L : vars) D G e1 e2 T1 T2 (k : sort_fn),
     is_gen_value e1 = true ->
     typing (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx G)) k) G e1 T1 ->
     (forall x, x `notin` L ->
        typing D ((x ~ gen G T1 k) ++ G) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
     typing D G (e_let e1 e2) T2
 | T_LetMono : forall (L : vars) D G e1 e2 T1 T2,
     typing D G e1 T1 ->
     (forall x, x `notin` L ->
        typing D ((x ~ sch_mono T1) ++ G) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
     typing D G (e_let e1 e2) T2
 | T_Letrec : forall (L : vars) D G fs e2 R T (k : sort_fn),
     fn_group fs ->
     (forall p, p `notin` L ->
        field_typing (ext D (AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G)) k)
          ((p ~ sch_mono (typ_Record R)) ++ G)
          (open_fields_wrt_exp fs (e_fvar_f p)) R) ->
     (forall p, p `notin` L ->
        typing D ((p ~ gen G (typ_Record R) k) ++ G) (open_exp_wrt_exp e2 (e_fvar_f p)) T) ->
     typing D G (e_letrec fs e2) T
 | T_Record : forall D G fs R,
     field_typing D G fs R -> typing D G (e_rec fs) (typ_Record R)
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
     typing D G e A -> sat D k_Numeric A -> typing D G (e_tofloat e) typ_Float
 | T_Bin : forall D G e1 o e2 A B R,
     typing D G e1 A -> typing D G e2 B -> bin_sig D o A B R ->
     typing D G (e_bin e1 o e2) R
with field_typing : denv -> ctx -> fields -> row -> Prop :=
 | FT_nil : forall D G, uniq G -> field_typing D G fs_nil row_Empty
 | FT_cons : forall D G l e T fs R,
     typing D G e T -> field_typing D G fs R ->
     field_typing D G (fs_cons l e fs) (row_Ext l T R).

#[export] Hint Constructors typing field_typing : core.

(* Reflexive-transitive closure, for the soundness corollary. *)
Inductive multistep : exp -> exp -> Prop :=
 | ms_refl : forall e, multistep e e
 | ms_step : forall e1 e2 e3, step e1 e2 -> multistep e2 e3 -> multistep e1 e3.

(* A term is stuck if it is not a value, cannot step, and raises no error
   (section 7). *)
Definition stuck (e : exp) : Prop :=
  ~ value e /\ (forall e', ~ step e e') /\ (forall k, ~ traps e k).
