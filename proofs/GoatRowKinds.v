(* Stage 7.2 of docs/design/phase7-proof-plan.md: row variables carry a kind.
   A row variable's kind is a sort (what the fields of a record it tails must
   satisfy) and the labels it lacks, and a scheme records the kind of each row
   variable it quantifies, as it records the sort of each type variable.

   In goat source, with the labels x = 0 and y = 1:

     program(a, b) do a == b done     a comparison of two records with an open
                                      row, whose tail has the sort Eq
     {...rest, x: 2}                  a spread onto a row variable that lacks x
     let set_x = program(p) do {...p, x: 1} done in set_x({y: true})
                                      one function for every record without an
                                      x: the row variable it generalizes lacks x

   The examples fail to compile if the row kind is dropped from [sat], from
   [T_SpreadL], or from a scheme. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatLit.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatPhase1.
Require Import Stdlib.Lists.List.
Import ListNotations.

Definition lx7 : label := 0.
Definition ly7 : label := 1.

(* x == x, where x is a record with a field and an open row whose tail is Eq. *)
Example open_row_with_an_eq_tail_compares : forall (D : denv) (x : var) l r,
  finer (rk_sort (drk D r)) k_Eq ->
  typing D (x ~ sch_mono (typ_Record (row_Ext l typ_Int (row_Var r))))
    (e_bin (e_fvar_f x) bop_eq (e_fvar_f x)) typ_Bool.
Proof.
  intros D x l r H.
  eapply T_Bin; [ eapply T_Var | eapply T_Var | apply sig_cmp ].
  all: first [ solve_uniq
             | (apply binds_cons_2; reflexivity)
             | apply inst_mono_self | reflexivity
             | (simpl; split; [ exact I | exact H ]) ].
Qed.

(* A row variable of sort Any is not Eq: the same comparison has no signature. *)
Example open_row_with_an_any_tail_does_not_satisfy_eq : forall (D : denv) l r,
  rk_sort (drk D r) = k_Any -> ~ sat D k_Eq (typ_Record (row_Ext l typ_Int (row_Var r))).
Proof.
  intros D l r H [_ Hf]. simpl in Hf. rewrite H in Hf. inversion Hf.
Qed.

(* {...p, x: 1} where p has an open row that lacks x. *)
Example spread_onto_a_row_that_lacks_the_label : forall (D : denv) (p : var) l r,
  rk_lacks (drk D r) l = true ->
  typing D (p ~ sch_mono (typ_Record (row_Var r)))
    (e_spread (e_fvar_f p) l (e_num 1)) (typ_Record (row_Ext l typ_Int (row_Var r))).
Proof.
  intros D p l r H.
  eapply T_SpreadL.
  - eapply T_Var; [ solve_uniq | | apply inst_mono_self ].
    apply binds_cons_2; reflexivity.
  - exact H.
  - apply T_Num; [ solve_uniq | exact I ].
Qed.

(* ---- a function over every record without an x ---- *)

Definition rr7 : atom := fresh nil.

(* The row variable [rr7] lacks x; every other row variable has no constraint. *)
Definition rk7 : rkind_fn :=
  fun r : atom => if r == rr7 then RK k_Any (fun l => Nat.eqb l lx7) else rk_any.

Lemma rk7_at : rk7 rr7 = RK k_Any (fun l => Nat.eqb l lx7).
Proof. unfold rk7. cbv beta. destruct (rr7 == rr7) as [_|N]; [ reflexivity | congruence ]. Qed.

Definition set_x_ty : typ :=
  typ_Arrow (typ_Record (row_Var rr7)) (typ_Record (row_Ext lx7 typ_Int (row_Var rr7))).

Definition set_x_scheme : scheme := gen nil set_x_ty (fun _ => k_Any) rk7.

Definition y_true : exp := e_rec (fs_cons ly7 e_true fs_nil).

Definition row_y7 : row := row_Ext ly7 typ_Bool row_Empty.

(* set_x({y: true}): the scheme's row variable becomes the row {y: Bool}, which
   lacks x, and the result has both fields. *)
Lemma inst_set_x_at_y : inst d_any
  (typ_Arrow (typ_Record row_y7) (typ_Record (row_Ext lx7 typ_Int row_y7))) set_x_scheme.
Proof.
  exists idt, (fun r : atom => if r == rr7 then row_y7 else row_Var r).
  split; [ | split; [ | split; [ | split; [ | split ] ] ] ].
  - intros a Ha. reflexivity.
  - intros r Hr. simpl in Hr. destruct (r == rr7) as [E|E];
      [ subst; exfalso; apply Hr; fsetdec | reflexivity ].
  - unfold set_x_scheme, set_x_ty. simpl. destruct (rr7 == rr7) as [E|E]; [ reflexivity | congruence ].
  - intros a Ha. exfalso. unfold set_x_scheme in Ha. simpl in Ha. fsetdec.
  - intros r Hr. unfold set_x_scheme in Hr. simpl in Hr.
    apply AtomSetFacts.diff_iff in Hr as [Hr _]. simpl in Hr.
    assert (Hrr : r = rr7) by fsetdec. subst r.
    cbn [set_x_scheme gen s_rk]. rewrite rk7_at.
    destruct (rr7 == rr7) as [E|E]; [ | congruence ].
    split; [ apply rsat_any | ].
    intros l Hl. simpl in Hl. apply Nat.eqb_eq in Hl. subst l. reflexivity.
  - split; [ intros a; exact I | ].
    intros r. cbv beta.
    match goal with |- context [if ?c then _ else _] => destruct c end; [ exact (conj I I) | exact I ].
Qed.

Definition set_x_use : exp :=
  e_let (e_abs (e_spread (e_fvar_b 0) lx7 (e_num 1)))
        (e_app (e_fvar_b 0) y_true).

Example generalized_lacks_instantiates_at_a_row_without_the_label :
  typing d_any nil set_x_use (typ_Record (row_Ext lx7 typ_Int row_y7)).
Proof.
  unfold set_x_use.
  apply T_Let_nopin with (L := {}) (T1 := set_x_ty) (k := fun _ => k_Any) (rk := rk7);
    [ reflexivity | | ].
  - apply T_Abs with (L := {}). intros p Hp.
    cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
    assert (Hin : rr7 `in` AtomSetImpl.diff (frv_typ set_x_ty) (frv_ctx nil))
      by (unfold set_x_ty; simpl; apply AtomSetFacts.diff_iff; split; fsetdec).
    eapply T_SpreadL.
    + eapply T_Var; [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_mono_self ].
    + cbn [rlacksD]. rewrite (extr_in _ _ _ rr7 Hin). rewrite rk7_at. reflexivity.
    + apply T_Num; [ solve_uniq | exact I ].
  - intros f Hf.
    cbn [open_exp_wrt_exp open_exp_wrt_exp_rec open_fields_wrt_exp_rec].
    eapply T_App.
    + eapply T_Var with (s := set_x_scheme);
        [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_set_x_at_y ].
    + unfold y_true. apply T_Record; [ | reflexivity ].
      eapply FT_cons; [ apply T_True; solve_uniq | apply FT_nil; solve_uniq ].
Qed.
