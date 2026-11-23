(* Phase 6 stage 1a: the Eq sort.  A comparison takes two operands of one type
   that satisfies Eq, so a generic comparison types at a variable of that
   sort, Unit compares, and a function does not.  The accepted examples fail to
   compile if a rule is dropped, and the rejected one if a rule is loosened. *)

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

(* () == () *)
Example unit_equality_types :
  typing d_any nil (e_bin e_unit bop_eq e_unit) typ_Bool.
Proof.
  eapply T_Bin; [ apply T_Unit; solve_uniq | apply T_Unit; solve_uniq | apply sig_cmp ];
    first [ reflexivity | (simpl; right; reflexivity) ].
Qed.

Example unit_equality_runs : bin_step bop_eq e_unit e_unit e_true.
Proof. exact (bs_cmp bop_eq e_unit e_unit _ eq_refl cr_unit). Qed.

Example unit_inequality_runs : bin_step bop_ne e_unit e_unit e_false.
Proof. exact (bs_cmp bop_ne e_unit e_unit _ eq_refl cr_unit). Qed.

(* A function is not Eq, so two of them do not compare. *)
Example arrow_is_not_eq : ~ sat d_any k_Eq (typ_Arrow typ_Int typ_Int).
Proof. simpl. intros H. discriminate H. Qed.

Example scalars_are_eq :
  sat d_any k_Eq typ_Int /\ sat d_any k_Eq typ_Float /\ sat d_any k_Eq typ_String
  /\ sat d_any k_Eq typ_Bool /\ sat d_any k_Eq typ_Unit.
Proof.
  repeat split; simpl; first [ exact I | (left; reflexivity) | (right; reflexivity) ].
Qed.

(* ---- same = program(x) do x == x done ---- *)

Definition ga6 : atom := fresh nil.

Definition k_eq : sort_fn := fun _ => k_Eq.

Lemma inst_same_at : forall U,
  sat d_any k_Eq U -> lct 0 U ->
  inst d_any (typ_Arrow U typ_Bool) (gen nil (typ_Arrow (typ_Var ga6) typ_Bool) k_eq).
Proof.
  intros U HU HL.
  exists (fun a => if a == ga6 then U else typ_Var a), idr.
  split; [ | split; [ | split; [ | split ] ] ].
  - intros a Ha. simpl in Ha. destruct (a == ga6) as [E|E];
      [ subst; exfalso; apply Ha; fsetdec | reflexivity ].
  - intros r _. reflexivity.
  - simpl. destruct (ga6 == ga6) as [E|E]; [ reflexivity | congruence ].
  - intros a Ha. simpl in Ha. apply AtomSetFacts.diff_iff in Ha as [Ha _].
    simpl in Ha. assert (a = ga6) by fsetdec. subst a.
    destruct (ga6 == ga6) as [E|E]; [ exact HU | congruence ].
  - split; [ intros a; simpl; match goal with |- context [if ?c then _ else _] => destruct c end; [ exact HL | exact I ] | intros r; exact I ].
Qed.

(* let same = program(x) do x == x done, then {0: same(1), 1: same("a"), 2: same(())} *)
Definition same_triple : exp :=
  e_let (e_abs (e_bin (e_fvar_b 0) bop_eq (e_fvar_b 0)))
        (e_rec (fs_cons 0 (e_app (e_fvar_b 0) (e_num 1))
               (fs_cons 1 (e_app (e_fvar_b 0) (e_str [97]))
               (fs_cons 2 (e_app (e_fvar_b 0) e_unit) fs_nil)))).

Example same_is_used_at_int_string_and_unit :
  typing d_any nil same_triple
    (typ_Record (row_Ext 0 typ_Bool (row_Ext 1 typ_Bool (row_Ext 2 typ_Bool row_Empty)))).
Proof.
  unfold same_triple.
  apply T_Let_nopin with (L := {}) (T1 := typ_Arrow (typ_Var ga6) typ_Bool) (k := k_eq);
    [ reflexivity | | ].
  - apply T_Abs with (L := {}). intros x Hx.
    cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
    assert (Hga : ga6 `in` AtomSetImpl.diff (ftv_typ (typ_Arrow (typ_Var ga6) typ_Bool)) (ftv_ctx nil))
      by (simpl; apply AtomSetFacts.diff_iff; split; [ fsetdec | fsetdec ]).
    eapply T_Bin; [ | | apply sig_cmp ].
    + apply T_Var with (s := sch_mono (typ_Var ga6));
        [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_mono_self ].
    + apply T_Var with (s := sch_mono (typ_Var ga6));
        [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_mono_self ].
    + reflexivity.
    + cbn [sat]. rewrite (ext_in _ _ _ ga6 Hga). apply finer_refl.
  - intros f Hf.
    cbn [open_exp_wrt_exp open_exp_wrt_exp_rec open_fields_wrt_exp_rec].
    apply T_Record; [ | reflexivity ]. eapply FT_cons.
    + eapply T_App with (T1 := typ_Int); [ | apply T_Num; [ solve_uniq | ] ].
      * apply T_Var with (s := gen nil (typ_Arrow (typ_Var ga6) typ_Bool) k_eq);
          [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_same_at; simpl; first [ exact I | (right; reflexivity) ] ].
      * exact I.
    + eapply FT_cons.
      * eapply T_App with (T1 := typ_String); [ | apply T_Str; solve_uniq ].
        apply T_Var with (s := gen nil (typ_Arrow (typ_Var ga6) typ_Bool) k_eq);
          [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_same_at; simpl; first [ exact I | (right; reflexivity) ] ].
      * eapply FT_cons; [ | apply FT_nil; solve_uniq ].
        eapply T_App with (T1 := typ_Unit); [ | apply T_Unit; solve_uniq ].
        apply T_Var with (s := gen nil (typ_Arrow (typ_Var ga6) typ_Bool) k_eq);
          [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_same_at; simpl; first [ exact I | (right; reflexivity) ] ].
Qed.

(* A variable only a comparison constrains is Eq, so a function is no instance
   of its scheme. *)
Example same_scheme_rejects_functions :
  ~ inst d_any (typ_Arrow (typ_Arrow typ_Int typ_Int) typ_Bool)
      (gen nil (typ_Arrow (typ_Var ga6) typ_Bool) k_eq).
Proof.
  intros [st [sr [Hst [Hsr [Heq [Hsat _]]]]]]. simpl in Heq.
  injection Heq as Hs.
  assert (Hin : ga6 `in` AtomSetImpl.diff (ftv_typ (typ_Arrow (typ_Var ga6) typ_Bool)) {})
    by (simpl; apply AtomSetFacts.diff_iff; split; [ fsetdec | fsetdec ]).
  pose proof (Hsat ga6 Hin) as H. cbn [gen s_sk s_tq] in H. rewrite <- Hs in H. simpl in H. discriminate H.
Qed.
