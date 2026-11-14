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
Require Import Coq.Lists.List.

(* ================================================================== *)
(* Type / row variable substitution (section 5).                       *)
(* A substitution is a pair of total maps; applied homomorphically.    *)
(* ================================================================== *)

Definition tsub := typvar -> typ.
Definition rsub := rowvar -> row.

Fixpoint ap_typ (st : tsub) (sr : rsub) (T : typ) {struct T} : typ :=
  match T with
  | typ_Number => typ_Number
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
  | typ_Number => {}
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
  | typ_Number => {}
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
with step_fields : fields -> fields -> Prop :=
 | stf_here : forall l e e' fs,
     step e e' -> step_fields (fs_cons l e fs) (fs_cons l e' fs)
 | stf_cons : forall l v fs fs',
     value v -> step_fields fs fs' -> step_fields (fs_cons l v fs) (fs_cons l v fs').

#[export] Hint Constructors step step_fields : core.

(* ================================================================== *)
(* Declarative typing (section 4), mutual with record-field typing.      *)
(* Binder rules are cofinite.  The leaf rules carry [uniq G] so that a     *)
(* derivable judgment has a well-formed context.                           *)
(* ================================================================== *)

Inductive typing : ctx -> exp -> typ -> Prop :=
 | T_Var : forall G x s T,
     uniq G -> binds x s G -> inst T s -> typing G (e_fvar_f x) T
 | T_Num : forall G n, uniq G -> typing G (e_num n) typ_Number
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
   (* Rank-2 intersection inference at the point where a generic function
      meets its argument (ADR 0008, issue #72), which is where goat's sharp
      edge bites: a parameter used at several types.  [T_App] binds the
      parameter monomorphically ([sch_mono T1]), so [program(f) do f(1) f(true)]
      is untypeable.  [T_AppPoly] types the redex [(program(e) done)(g)] exactly
      as [let x = g in e]: the argument [g] is generalized against [G] and the
      parameter is usable at every instance of that scheme inside [e].  This is
      rank-2 (a quantifier only to the left of the application arrow) realized as
      HM generalization of the argument -- so the rule's whole metatheory reduces
      to the already-proven polymorphic term substitution ([typing_subst_poly]),
      including the scoped-label-row case ([use2]), with no new theory. *)
 | T_AppPoly : forall G e g T,
     typing G (e_let g e) T ->
     typing G (e_app (e_abs e) g) T
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

(* A term is stuck if it is not a value and cannot step (section 7). *)
Definition stuck (e : exp) : Prop := ~ value e /\ forall e', ~ step e e'.
