(* Rank-2 intersection inference: the sharp-edge examples (ADR 0008, issue #72).

   docs/plan.md's "Known limitation" lists three programs that core HM rejects
   because a lambda-bound parameter is monomorphic.  With [T_AppPoly] (GoatDefs)
   they type, and -- via the extended [soundness] (GoatSound) -- never get
   stuck.  We give the no-record case [both] and the scoped-label-row case
   [use2]; the latter is the rank-2 + rows combination ADR 0008 flagged as
   unexplored, and it types here because [T_AppPoly] generalizes the argument's
   principal type (row variable included), reducing to the proven row-aware
   polymorphic substitution.

   The examples are written in direct-application form [(program(f) ...)(g)],
   which is what the surface [f = program... f(...)] reduces to under st-letv.
   Typing a rank-2 function as a stored first-class value needs rank-2 types in
   the grammar; that is a heavier delta and out of this pass (see the PR notes).

   No sequencing/Unit in the core, so "use f twice" is encoded as a two-field
   record literal whose fields apply the parameter at the two types. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSound.
Require Import Coq.Lists.List.

(* one-point substitutions used to witness the instance relation *)
Definition tsub1 (a : typvar) (tau : typ) : tsub :=
  fun b => if a == b then tau else typ_Var b.
Definition rsub1 (p : rowvar) (R : row) : rsub :=
  fun s => if p == s then R else row_Var s.

(* ================================================================== *)
(* Example 1: [both = program(f) do f(1) f(true) done], no record.      *)
(* Direct form: [(program(f) do {a: f(1), b: f(true)} done)(id)].        *)
(* ================================================================== *)

Definition tm_id : exp := e_abs (e_fvar_b 0).

Definition tm_both_body : exp :=
  e_rec (fs_cons 0 (e_app (e_fvar_b 0) (e_num 1))
        (fs_cons 1 (e_app (e_fvar_b 0) e_true) fs_nil)).

Definition tm_both : exp := e_app (e_abs tm_both_body) tm_id.

Definition ty_both : typ :=
  typ_Record (row_Ext 0 typ_Number (row_Ext 1 typ_Bool row_Empty)).

(* identity has every arrow [tau -> tau] *)
Lemma tm_id_typing : forall G a, uniq G -> typing G tm_id (typ_Arrow (typ_Var a) (typ_Var a)).
Proof.
  intros G a Hu. unfold tm_id.
  apply T_Abs with (L := dom G). intros x Hx. cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
  apply T_Var with (s := sch_mono (typ_Var a)).
  - solve_uniq.
  - apply binds_cons_2; reflexivity.
  - exists idt, idr. repeat split; intros; reflexivity.
Qed.

(* every instance of [gen nil (a -> a)] of the form [tau -> tau] *)
Lemma inst_idscheme : forall a tau,
  inst (typ_Arrow tau tau) (gen nil (typ_Arrow (typ_Var a) (typ_Var a))).
Proof.
  intros a tau. unfold inst.
  exists (tsub1 a tau), idr. split; [ | split ].
  - intros b Hb. simpl in Hb. unfold tsub1.
    destruct (a == b) as [He|Hne]; [ subst b; exfalso; apply Hb; fsetdec | reflexivity ].
  - intros r _. reflexivity.
  - unfold tsub1; simpl. destruct (a == a) as [_|Hne]; [ reflexivity | contradiction ].
Qed.

Theorem both_types : typing nil tm_both ty_both.
Proof.
  unfold tm_both, ty_both.
  (* rank-2: type the redex as [let f = id in body] *)
  apply T_AppPoly.
  (* pick a type variable for the identity's domain; nil has none, so any atom *)
  pose (a := fresh (@nil atom)).
  apply T_Let with (L := dom (@nil (var * scheme)))
                   (T1 := typ_Arrow (typ_Var a) (typ_Var a)).
  - apply tm_id_typing. auto.
  - intros x Hx. cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
    set (s := gen nil (typ_Arrow (typ_Var a) (typ_Var a))).
    assert (Hu : uniq ((x ~ s) ++ nil)) by solve_uniq.
    apply T_Record.
    apply FT_cons.
    { (* field a: f(1) : Number *)
      eapply T_App with (T1 := typ_Number).
      - apply T_Var with (s := s);
          [ exact Hu | apply binds_cons_2; reflexivity | unfold s; apply (inst_idscheme a typ_Number) ].
      - apply T_Num; exact Hu. }
    apply FT_cons.
    { (* field b: f(true) : Bool *)
      eapply T_App with (T1 := typ_Bool).
      - apply T_Var with (s := s);
          [ exact Hu | apply binds_cons_2; reflexivity | unfold s; apply (inst_idscheme a typ_Bool) ].
      - apply T_True; exact Hu. }
    apply FT_nil; exact Hu.
Qed.

(* Soundness delta: [both] never gets stuck, by the extended [soundness]. *)
Corollary both_never_stuck : forall e', multistep tm_both e' -> ~ stuck e'.
Proof. intros e' Hms. eapply soundness_not_stuck; [ apply both_types | exact Hms ]. Qed.

(* ================================================================== *)
(* Example 2: [use2 = program(g) do g({x:1}) g({x:2,y:3}) done] with      *)
(* [getx = program(p) do p.x done].  The scoped-label-row case.           *)
(* Direct form: [(program(g) do {a: g({x:1}), b: g({x:2,y:3})} done)(getx)].*)
(* Labels: x = 0, y = 1.                                                   *)
(* ================================================================== *)

Definition tm_getx : exp := e_abs (e_proj (e_fvar_b 0) 0).

Definition tm_use2_body : exp :=
  e_rec (fs_cons 0 (e_app (e_fvar_b 0) (e_rec (fs_cons 0 (e_num 1) fs_nil)))
        (fs_cons 1 (e_app (e_fvar_b 0)
                      (e_rec (fs_cons 0 (e_num 2) (fs_cons 1 (e_num 3) fs_nil))))
        fs_nil)).

Definition tm_use2 : exp := e_app (e_abs tm_use2_body) tm_getx.

Definition ty_use2 : typ :=
  typ_Record (row_Ext 0 typ_Number (row_Ext 1 typ_Number row_Empty)).

(* [getx] projects field [x]: it has every type [Record (x : tau | rho) -> tau]. *)
Lemma tm_getx_typing : forall G a r,
  uniq G ->
  typing G tm_getx
    (typ_Arrow (typ_Record (row_Ext 0 (typ_Var a) (row_Var r))) (typ_Var a)).
Proof.
  intros G a r Hu. unfold tm_getx.
  apply T_Abs with (L := dom G). intros x Hx. cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
  eapply T_Proj.
  apply T_Var with (s := sch_mono (typ_Record (row_Ext 0 (typ_Var a) (row_Var r)))).
  - solve_uniq.
  - apply binds_cons_2; reflexivity.
  - exists idt, idr. repeat split; intros; reflexivity.
Qed.

(* the getx-scheme instantiated at a given codomain type var and a given row *)
Lemma inst_getxscheme : forall a r tau Rho,
  inst (typ_Arrow (typ_Record (row_Ext 0 tau Rho)) tau)
       (gen nil (typ_Arrow (typ_Record (row_Ext 0 (typ_Var a) (row_Var r))) (typ_Var a))).
Proof.
  intros a r tau Rho. unfold inst.
  exists (tsub1 a tau), (rsub1 r Rho). split; [ | split ].
  - intros b Hb. simpl in Hb. unfold tsub1.
    destruct (a == b) as [He|Hne]; [ subst b; exfalso; apply Hb; fsetdec | reflexivity ].
  - intros s Hs. simpl in Hs. unfold rsub1.
    destruct (r == s) as [He|Hne]; [ subst s; exfalso; apply Hs; fsetdec | reflexivity ].
  - unfold tsub1, rsub1; simpl.
    destruct (a == a) as [_|Hne]; [ | contradiction ].
    destruct (r == r) as [_|Hne]; [ reflexivity | contradiction ].
Qed.

Theorem use2_types : typing nil tm_use2 ty_use2.
Proof.
  unfold tm_use2, ty_use2.
  apply T_AppPoly.
  pose (a := fresh (@nil atom)).
  pose (r := fresh (a :: nil)).
  apply T_Let with (L := dom (@nil (var * scheme)))
                   (T1 := typ_Arrow (typ_Record (row_Ext 0 (typ_Var a) (row_Var r))) (typ_Var a)).
  - apply tm_getx_typing. auto.
  - intros x Hx. cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
    set (s := gen nil (typ_Arrow (typ_Record (row_Ext 0 (typ_Var a) (row_Var r))) (typ_Var a))).
    assert (Hu : uniq ((x ~ s) ++ nil)) by solve_uniq.
    apply T_Record.
    apply FT_cons.
    { (* g({x:1}) : Number, row instantiated to empty *)
      eapply T_App with (T1 := typ_Record (row_Ext 0 typ_Number row_Empty)).
      - apply T_Var with (s := s);
          [ exact Hu | apply binds_cons_2; reflexivity
          | unfold s; apply (inst_getxscheme a r typ_Number row_Empty) ].
      - apply T_Record. apply FT_cons; [ apply T_Num; exact Hu | apply FT_nil; exact Hu ]. }
    apply FT_cons.
    { (* g({x:2,y:3}) : Number, row instantiated to [y : Number] *)
      eapply T_App with (T1 := typ_Record (row_Ext 0 typ_Number (row_Ext 1 typ_Number row_Empty))).
      - apply T_Var with (s := s);
          [ exact Hu | apply binds_cons_2; reflexivity
          | unfold s; apply (inst_getxscheme a r typ_Number (row_Ext 1 typ_Number row_Empty)) ].
      - apply T_Record. apply FT_cons; [ apply T_Num; exact Hu | ].
        apply FT_cons; [ apply T_Num; exact Hu | apply FT_nil; exact Hu ]. }
    apply FT_nil; exact Hu.
Qed.

Corollary use2_never_stuck : forall e', multistep tm_use2 e' -> ~ stuck e'.
Proof. intros e' Hms. eapply soundness_not_stuck; [ apply use2_types | exact Hms ]. Qed.
