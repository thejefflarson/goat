(* Closing a term over a variable (phase 5, stage 4, part 3b).

   Algorithm W infers the body of a binder at its opened form, with a fresh
   variable standing for the bound one, and the elaborated body it returns
   mentions that variable.  The elaborated binder is that body closed over the
   variable again.  [cl k x e] replaces the free variable [x] by the index [k]
   and [lce k e] says the indices of [e] are all below [k].  The lemmas say
   that closing and opening undo each other on such terms, that opening a
   closed binder body at a name is the substitution of the name, and that
   [erase] commutes with closing. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatMeta.
Require Import Goat.GoatElab.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

Fixpoint cl (k : nat) (x : atom) (e : exp) {struct e} : exp :=
  match e with
  | e_fvar_b i => e_fvar_b i
  | e_fvar_f y => if y == x then e_fvar_b k else e_fvar_f y
  | e_num _ | e_dec _ | e_true | e_false | e_unit | e_str _ => e
  | e_abs b => e_abs (cl (S k) x b)
  | e_app a b => e_app (cl k x a) (cl k x b)
  | e_let a b => e_let (cl k x a) (cl (S k) x b)
  | e_letrec fs b => e_letrec (clf (S k) x fs) (cl (S k) x b)
  | e_rec fs => e_rec (clf k x fs)
  | e_proj a l => e_proj (cl k x a) l
  | e_ite a b c => e_ite (cl k x a) (cl k x b) (cl k x c)
  | e_bin a o b => e_bin (cl k x a) o (cl k x b)
  | e_tofloat a => e_tofloat (cl k x a)
  | e_con w tg a => e_con w tg (cl k x a)
  | e_match w a ars => e_match w (cl k x a) (cla k x ars)
  | e_spread a l b => e_spread (cl k x a) l (cl k x b)
  | e_restrict a l => e_restrict (cl k x a) l
  | e_fold a => e_fold (cl k x a)
  | e_unfold a => e_unfold (cl k x a)
  end
with clf (k : nat) (x : atom) (fs : fields) {struct fs} : fields :=
  match fs with
  | fs_nil => fs_nil
  | fs_cons l e fs' => fs_cons l (cl k x e) (clf k x fs')
  | fs_meth l e fs' => fs_meth l (cl k x e) (clf k x fs')
  end
with cla (k : nat) (x : atom) (ars : arms) {struct ars} : arms :=
  match ars with
  | arms_nil => arms_nil
  | arms_else e => arms_else (cl k x e)
  | arms_cons tg e ars' => arms_cons tg (cl (S k) x e) (cla k x ars')
  end.

Fixpoint lce (k : nat) (e : exp) {struct e} : Prop :=
  match e with
  | e_fvar_b i => i < k
  | e_fvar_f _ | e_num _ | e_dec _ | e_true | e_false | e_unit | e_str _ => True
  | e_abs b => lce (S k) b
  | e_app a b | e_bin a _ b | e_spread a _ b => lce k a /\ lce k b
  | e_let a b => lce k a /\ lce (S k) b
  | e_letrec fs b => lcef (S k) fs /\ lce (S k) b
  | e_rec fs => lcef k fs
  | e_proj a _ | e_tofloat a | e_con _ _ a | e_restrict a _ | e_fold a | e_unfold a => lce k a
  | e_ite a b c => lce k a /\ lce k b /\ lce k c
  | e_match _ a ars => lce k a /\ lcea k ars
  end
with lcef (k : nat) (fs : fields) {struct fs} : Prop :=
  match fs with
  | fs_nil => True
  | fs_cons _ e fs' => lce k e /\ lcef k fs'
  | fs_meth _ e fs' => lce k e /\ lcef k fs'
  end
with lcea (k : nat) (ars : arms) {struct ars} : Prop :=
  match ars with
  | arms_nil => True
  | arms_else e => lce k e
  | arms_cons _ e ars' => lce (S k) e /\ lcea k ars'
  end.

Ltac clean_goal :=
  cbn [cl clf cla lce lcef lcea open_exp_wrt_exp_rec open_fields_wrt_exp_rec open_arms_wrt_exp_rec
       subst_exp subst_fields subst_arms fv_exp fv_fields fv_arms erase erase_fields erase_arms] in *.

Ltac simp_cases0 :=
  repeat match goal with
         | |- context [lt_eq_lt_dec ?a ?b] => destruct (lt_eq_lt_dec a b) as [[?|?]|?]
         | H : context [lt_eq_lt_dec ?a ?b] |- _ => destruct (lt_eq_lt_dec a b) as [[?|?]|?]
         | |- context [if ?c then _ else _] => destruct c
         end;
  subst; cbn in *.

Ltac simp_cases := simp_cases0; simp_cases0.

(* ---- opening ---- *)

Lemma lce_open_inv_mut :
  (forall e k y, lce k (open_exp_wrt_exp_rec k (e_fvar_f y) e) -> lce (S k) e) /\
  (forall fs k y, lcef k (open_fields_wrt_exp_rec k (e_fvar_f y) fs) -> lcef (S k) fs) /\
  (forall ars k y, lcea k (open_arms_wrt_exp_rec k (e_fvar_f y) ars) -> lcea (S k) ars).
Proof.
  apply exp_fields_mutind; intros; clean_goal;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try exact I; try (split; eauto; fail); try (repeat split; eauto; fail); eauto.
  all: try (simp_cases; first [ lia | exact I | auto ]).
Qed.

(* ---- closing ---- *)

Lemma lce_cl_mut :
  (forall e k x, lce k e -> lce (S k) (cl k x e)) /\
  (forall fs k x, lcef k fs -> lcef (S k) (clf k x fs)) /\
  (forall ars k x, lcea k ars -> lcea (S k) (cla k x ars)).
Proof.
  apply exp_fields_mutind; intros; clean_goal;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try exact I; try (split; eauto; fail); try (repeat split; eauto; fail); eauto.
  all: try (simp_cases; first [ lia | exact I | auto ]).
Qed.

Lemma open_cl_mut :
  (forall e k x y, lce k e ->
     open_exp_wrt_exp_rec k (e_fvar_f y) (cl k x e) = subst_exp (e_fvar_f y) x e) /\
  (forall fs k x y, lcef k fs ->
     open_fields_wrt_exp_rec k (e_fvar_f y) (clf k x fs) = subst_fields (e_fvar_f y) x fs) /\
  (forall ars k x y, lcea k ars ->
     open_arms_wrt_exp_rec k (e_fvar_f y) (cla k x ars) = subst_arms (e_fvar_f y) x ars).
Proof.
  apply exp_fields_mutind; intros; clean_goal;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try reflexivity;
    try (f_equal; eauto; fail).
  all: try (simp_cases; first [ reflexivity | lia ]).
Qed.

Lemma cl_open_mut :
  (forall e k x, lce (S k) e -> x `notin` fv_exp e ->
     cl k x (open_exp_wrt_exp_rec k (e_fvar_f x) e) = e) /\
  (forall fs k x, lcef (S k) fs -> x `notin` fv_fields fs ->
     clf k x (open_fields_wrt_exp_rec k (e_fvar_f x) fs) = fs) /\
  (forall ars k x, lcea (S k) ars -> x `notin` fv_arms ars ->
     cla k x (open_arms_wrt_exp_rec k (e_fvar_f x) ars) = ars).
Proof.
  apply exp_fields_mutind; intros; clean_goal;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try reflexivity;
    try (f_equal; eauto; fsetdec; fail).
  all: try (simp_cases; first [ reflexivity | lia | exfalso; fsetdec ]).
Qed.

(* ---- erasure and closing ---- *)

Lemma erase_cl_mut :
  (forall e k x, erase (cl k x e) = cl k x (erase e)) /\
  (forall fs k x, erase_fields (clf k x fs) = clf k x (erase_fields fs)) /\
  (forall ars k x, erase_arms (cla k x ars) = cla k x (erase_arms ars)).
Proof.
  apply exp_fields_mutind; intros; clean_goal;
    try reflexivity; try (f_equal; eauto; fail); try (rewrite H; reflexivity).
  all: try (simp_cases; reflexivity).
Qed.

Lemma lce_erase_mut :
  (forall e k, lce k e -> lce k (erase e)) /\
  (forall fs k, lcef k fs -> lcef k (erase_fields fs)) /\
  (forall ars k, lcea k ars -> lcea k (erase_arms ars)).
Proof.
  apply exp_fields_mutind; intros; clean_goal;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try exact I; try (split; eauto; fail); try (repeat split; eauto; fail); eauto.
Qed.

(* ---- coercions ---- *)

Lemma lce_coerce : forall cs e k, lce k e -> lce k (coerce cs e).
Proof.
  induction cs as [|d cs IH]; intros e k H; cbn [coerce]; [ exact H | apply IH ].
  destruct d; cbn; exact H.
Qed.
