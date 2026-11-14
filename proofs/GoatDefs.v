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
(* Type schemes (section 5): a quantified set of type and row variables  *)
(* over a monotype body.  Quantified sets are finite [atoms]; a monotype  *)
(* scheme quantifies nothing.                                            *)
(* ================================================================== *)

Record scheme : Type := Sch {
  s_tq : atoms;
  s_rq : atoms;
  s_body : typ
}.

Definition sch_mono (T : typ) : scheme := Sch {} {} T.

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

Definition inst (T : typ) (s : scheme) : Prop :=
  exists (st : tsub) (sr : rsub),
    (forall a, a `notin` s_tq s -> st a = typ_Var a) /\
    (forall r, r `notin` s_rq s -> sr r = row_Var r) /\
    T = ap_typ st sr (s_body s).

(* ================================================================== *)
(* Generalization (section 5): quantify exactly the variables free in     *)
(* the type but not in the context.                                        *)
(* ================================================================== *)

Definition gen (G : ctx) (T : typ) : scheme :=
  Sch (AtomSetImpl.diff (ftv_typ T) (ftv_ctx G))
      (AtomSetImpl.diff (frv_typ T) (frv_ctx G))
      T.

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

(* ================================================================== *)
(* Base-type operators (ADR 0017, ADR 0036).                            *)
(* A whole-number literal is a [Z], a decimal literal a numerator over a  *)
(* positive denominator, and a string its bytes.  Integers are unbounded: *)
(* the compiler's per-target overflow trap is not modeled.  A Float is an *)
(* exact rational: IEEE rounding, infinities and NaN are not modeled.     *)
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

(* [+ - *] on integers and on rationals; meaningful when [kind o = k_ring]. *)
Definition ring_Z (o : bop) (a b : znum) : znum :=
  match o with
  | bop_add => z_add a b
  | bop_sub => z_sub a b
  | _ => z_mul a b
  end.

Definition ring_Q (o : bop) (p q : qnum) : qnum :=
  match o with
  | bop_add => q_add p q
  | bop_sub => q_sub p q
  | _ => q_mul p q
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

(* A number value and the rational it stands for: an [Int] widens to a
   [Float] at an operator (ADR 0017). *)
Inductive num_val : exp -> qnum -> Prop :=
 | nv_num : forall z, num_val (e_num z) (q_of_z z)
 | nv_dec : forall d, num_val (e_dec d) (q_of_dec d).

(* Two whole numbers: the operands of integer arithmetic. *)
Definition both_whole (x y : exp) : Prop :=
  exists a b, x = e_num a /\ y = e_num b.

(* What an operator computes from two values.  A relation, because a Float
   quotient by zero is IEEE infinity or NaN, which the model leaves
   unspecified: any decimal.  Every other case has one answer, and an integer
   [//] or [%] by zero has none (it traps, see [bin_trap]). *)
Inductive bin_step : bop -> exp -> exp -> exp -> Prop :=
 | bs_ring_int : forall o a b,
     kind o = k_ring ->
     bin_step o (e_num a) (e_num b) (e_num (ring_Z o a b))
 | bs_ring_float : forall o x y p q,
     kind o = k_ring -> num_val x p -> num_val y q -> ~ both_whole x y ->
     bin_step o x y (e_dec (dec_of_q (ring_Q o p q)))
 | bs_quot : forall x y p q,
     num_val x p -> num_val y q -> q_is_zero q = false ->
     bin_step bop_div x y (e_dec (dec_of_q (q_div p q)))
 | bs_quot_zero : forall x y p q d,
     num_val x p -> num_val y q -> q_is_zero q = true ->
     bin_step bop_div x y (e_dec d)
 | bs_whole : forall o a b,
     kind o = k_whole -> z_is_zero b = false ->
     bin_step o (e_num a) (e_num b) (e_num (whole_Z o a b))
 | bs_cmp_num : forall o x y p q,
     kind o = k_cmp -> num_val x p -> num_val y q ->
     bin_step o x y (of_bool (cmp_holds o (q_cmp p q)))
 | bs_cmp_str : forall o p q,
     kind o = k_cmp ->
     bin_step o (e_str p) (e_str q) (of_bool (cmp_holds o (str_compare p q)))
 | bs_cmp_bool : forall o x y a b,
     kind o = k_cmp -> val_bool x = Some a -> val_bool y = Some b ->
     bin_step o x y (of_bool (cmp_holds o (bool_compare a b))).

(* Why a program stops: the defined runtime errors.  Only integer division by
   zero is in the fragment; overflow and [trap()] are not. *)
Inductive trap_kind : Set := trap_div_zero.

Inductive bin_trap : bop -> exp -> exp -> trap_kind -> Prop :=
 | bt_div_zero : forall o a b,
     kind o = k_whole -> z_is_zero b = true ->
     bin_trap o (e_num a) (e_num b) trap_div_zero.

(* The types an operator accepts, and what it gives (ADR 0017, ADR 0036):
   [+ - *] on two Ints give an Int, with a Float anywhere a Float; [/] gives a
   Float; [//] and [%] want two Ints; a comparison takes any two numbers, two
   strings or two booleans.  Operators are at concrete types: a constraint
   variable has no signature in this phase. *)
Inductive num_typ : typ -> Prop :=
 | nt_int : num_typ typ_Int
 | nt_float : num_typ typ_Float.

Inductive base_typ : typ -> Prop :=
 | base_String : base_typ typ_String
 | base_Bool : base_typ typ_Bool.

Inductive bin_sig : bop -> typ -> typ -> typ -> Prop :=
 | sig_ring_int : forall o,
     kind o = k_ring -> bin_sig o typ_Int typ_Int typ_Int
 | sig_ring_float : forall o A B,
     kind o = k_ring -> num_typ A -> num_typ B ->
     (A = typ_Float \/ B = typ_Float) ->
     bin_sig o A B typ_Float
 | sig_quot : forall A B,
     num_typ A -> num_typ B -> bin_sig bop_div A B typ_Float
 | sig_whole : forall o,
     kind o = k_whole -> bin_sig o typ_Int typ_Int typ_Int
 | sig_cmp_num : forall o A B,
     kind o = k_cmp -> num_typ A -> num_typ B -> bin_sig o A B typ_Bool
 | sig_cmp_base : forall o B,
     kind o = k_cmp -> base_typ B -> bin_sig o B B typ_Bool.

#[export] Hint Constructors num_typ base_typ num_val : core.

(* Every type in a signature is closed, so substitution leaves it alone. *)
Lemma bin_sig_ap : forall o A B R st sr,
  bin_sig o A B R ->
  ap_typ st sr A = A /\ ap_typ st sr B = B /\ ap_typ st sr R = R.
Proof.
  intros o A B R st sr H.
  assert (Hn : forall N, num_typ N -> ap_typ st sr N = N)
    by (intros N HN; destruct HN; reflexivity).
  assert (Hb : forall N, base_typ N -> ap_typ st sr N = N)
    by (intros N HN; destruct HN; reflexivity).
  destruct H; simpl; repeat split;
    first [ reflexivity | apply Hn; assumption | apply Hb; assumption ].
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

Inductive typing : ctx -> exp -> typ -> Prop :=
 | T_Var : forall G x s T,
     uniq G -> binds x s G -> inst T s -> typing G (e_fvar_f x) T
 | T_Num : forall G n, uniq G -> typing G (e_num n) typ_Int
 | T_NumFloat : forall G n, uniq G -> typing G (e_num n) typ_Float
 | T_Dec : forall G d, uniq G -> typing G (e_dec d) typ_Float
 | T_True : forall G, uniq G -> typing G e_true typ_Bool
 | T_False : forall G, uniq G -> typing G e_false typ_Bool
 | T_Abs : forall (L : vars) G e T1 T2,
     (forall x, x `notin` L ->
        typing ((x ~ sch_mono T1) ++ G) (open_exp_wrt_exp e (e_fvar_f x)) T2) ->
     typing G (e_abs e) (typ_Arrow T1 T2)
 | T_App : forall G e1 e2 T1 T2,
     typing G e1 (typ_Arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (e_app e1 e2) T2
 | T_Let : forall (L : vars) G e1 e2 T1 T2,
     typing G e1 T1 ->
     (forall x, x `notin` L ->
        typing ((x ~ gen G T1) ++ G) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
     typing G (e_let e1 e2) T2
 | T_Record : forall G fs R,
     field_typing G fs R -> typing G (e_rec fs) (typ_Record R)
 | T_Proj : forall G e l T R,
     typing G e (typ_Record (row_Ext l T R)) -> typing G (e_proj e l) T
 | T_Conv : forall G e T T',
     typing G e T -> teq T T' -> typing G e T'
 | T_Unit : forall G, uniq G -> typing G e_unit typ_Unit
 | T_Str : forall G q, uniq G -> typing G (e_str q) typ_String
 | T_If : forall G e1 e2 e3 T,
     typing G e1 typ_Bool -> typing G e2 T -> typing G e3 T ->
     typing G (e_ite e1 e2 e3) T
 | T_Bin : forall G e1 o e2 A B R,
     typing G e1 A -> typing G e2 B -> bin_sig o A B R ->
     typing G (e_bin e1 o e2) R
with field_typing : ctx -> fields -> row -> Prop :=
 | FT_nil : forall G, uniq G -> field_typing G fs_nil row_Empty
 | FT_cons : forall G l e T fs R,
     typing G e T -> field_typing G fs R ->
     field_typing G (fs_cons l e fs) (row_Ext l T R).

#[export] Hint Constructors typing field_typing : core.

(* Reflexive-transitive closure, for the soundness corollary. *)
Inductive multistep : exp -> exp -> Prop :=
 | ms_refl : forall e, multistep e e
 | ms_step : forall e1 e2 e3, step e1 e2 -> multistep e2 e3 -> multistep e1 e3.

(* A term is stuck if it is not a value, cannot step, and raises no error
   (section 7). *)
Definition stuck (e : exp) : Prop :=
  ~ value e /\ (forall e', ~ step e e') /\ (forall k, ~ traps e k).
