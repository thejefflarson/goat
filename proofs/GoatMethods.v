(* Methods in the iso calculus: worked examples (docs/design/phase5-proof-plan.md,
   stage 3; ADR 0034, ADR 0037).  In goat source, with moved = 0 and x = 1:

     ball = {x: 1, moved: program(self) do {...self, x: self.x + 1} done}
     ball.moved()          # (unfold ball).moved(ball)
     step = program(p) do p.moved() done
     step(ball)

   A method's receiver has the record's own recursive type
   P = mu t. {moved: (t) -> t; x: Int}.  Every [self.f] is [(unfold self).f]
   and a record returned as the receiver is [fold]ed.  [erase] gives back the
   source program, which is the claim of GoatElab.v: the folds and unfolds are
   the only difference.  Nothing here needs a rule the calculus lacks.

   Not here: [big = {...ball, size: 10}] and the three-method model.  They
   instantiate the receiver's row variable, which is the shared-receiver rule
   of the plan's stage 5.

   The accepted examples fail to compile if a rule is dropped; the rejected
   ones fail if the guard on recursion or the type of a field is weakened. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatLit.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatMu.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatRecTypes.
Require Import Goat.GoatElab.
Require Import Stdlib.Lists.List.
Import ListNotations.

Definition l_moved : label := 0.
Definition l_x : label := 1.

(* the unrolled receiver: P_body with P for the index *)
Definition P_row : row := row_Ext l_moved (typ_Arrow P P) (row_Ext l_x typ_Int row_Empty).

(* [moved]'s rest once [x] is taken out *)
Definition P_rest : row := row_Ext l_moved (typ_Arrow P P) row_Empty.

(* ---- the terms ---- *)

(* {...self, x: self.x + 1}, folded back into the receiver type *)
Definition bump (self : exp) : exp :=
  e_fold (e_spread (e_unfold self) l_x
            (e_bin (e_proj (e_unfold self) l_x) bop_add (e_num 1))).

Definition ball : exp :=
  e_fold (e_rec (fs_cons l_moved (e_abs (bump (e_fvar_b 0)))
                   (fs_cons l_x (e_num 1) fs_nil))).

(* ball.moved(), that is (unfold ball).moved(ball) *)
Definition ball_moved : exp := e_app (e_proj (e_unfold ball) l_moved) ball.

(* ball.moved().x *)
Definition ball_moved_x : exp := e_proj (e_unfold ball_moved) l_x.

Definition step_m : exp := e_abs (e_app (e_proj (e_unfold (e_fvar_b 0)) l_moved) (e_fvar_b 0)).

(* ---- typing ---- *)

Lemma var_P : forall s, typing d_any ((s ~ sch_mono P) ++ nil) (e_fvar_f s) P.
Proof.
  intros s. apply T_Var with (s := sch_mono P);
    [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_mono_self ].
Qed.

Lemma unfold_var_P : forall s,
  typing d_any ((s ~ sch_mono P) ++ nil) (e_unfold (e_fvar_f s)) (typ_Record P_row).
Proof.
  intros s. change (typ_Record P_row) with (open_typ 0 P P_body).
  apply T_Unfold; [ apply P_is_closed | apply P_is_guarded | apply var_P ].
Qed.

(* the receiver's fields reordered with [x] in front: what a spread on [x] reads *)
Lemma P_row_maybe : req P_row (row_Maybe l_x typ_Unit typ_Int P_rest).
Proof.
  unfold P_row, P_rest, l_x, l_moved.
  eapply req_trans; [ apply req_swap; discriminate | ].
  apply req_sym. apply req_pre.
Qed.

Lemma P_row_ext : req (row_Ext l_x typ_Int P_rest) P_row.
Proof.
  unfold P_row, P_rest, l_x, l_moved.
  apply req_sym. apply req_swap. discriminate.
Qed.

Lemma bump_types : forall s, typing d_any ((s ~ sch_mono P) ++ nil) (bump (e_fvar_f s)) P.
Proof.
  intros s. unfold bump. apply T_Fold; [ apply P_is_closed | apply P_is_guarded | ].
  change (open_typ 0 (typ_Mu P_body) P_body) with (open_typ 0 P P_body).
  assert (HU : open_typ 0 P P_body = typ_Record P_row) by reflexivity.
  rewrite HU.
  eapply T_Conv; [ | apply teq_rec; exact P_row_ext ].
  eapply T_Spread with (P := typ_Unit) (T := typ_Int) (R := P_rest).
  - eapply T_Conv; [ apply unfold_var_P | apply teq_rec; exact P_row_maybe ].
  - eapply T_Bin with (A := typ_Int) (B := typ_Int); [ | apply T_Num; [ solve_uniq | exact I ] | apply sig_ring; first [ reflexivity | exact I ] ].
    eapply T_Proj.
    eapply T_Conv; [ apply unfold_var_P | apply teq_rec; apply req_sym; exact P_row_ext ].
Qed.

Lemma ball_record_types : typing d_any nil
  (e_rec (fs_cons l_moved (e_abs (bump (e_fvar_b 0))) (fs_cons l_x (e_num 1) fs_nil)))
  (typ_Record P_row).
Proof.
  apply T_Record. eapply FT_cons.
  - apply T_Abs with (L := {}). intros s Hs.
    cbn [open_exp_wrt_exp open_exp_wrt_exp_rec]. unfold bump.
    exact (bump_types s).
  - eapply FT_cons; [ apply T_Num; [ solve_uniq | exact I ] | apply FT_nil; solve_uniq ].
Qed.

Example ball_types : typing d_any nil ball P.
Proof.
  unfold ball. apply T_Fold; [ apply P_is_closed | apply P_is_guarded | ].
  exact ball_record_types.
Qed.

(* A head coercion does what the checker's equi-recursive equality does
   silently: the record literal has the unrolled type, and one [fold] gives
   it the receiver type.  The erasure of the coerced term is the literal. *)
Example ball_by_head_coercion : typing d_any nil
  (coerce [d_fold] (e_rec (fs_cons l_moved (e_abs (bump (e_fvar_b 0)))
                             (fs_cons l_x (e_num 1) fs_nil)))) P.
Proof.
  eapply coerce_typing.
  - apply (ch_fold P_body); [ apply P_is_closed | apply P_is_guarded | apply ch_nil ].
  - exact ball_record_types.
Qed.

Lemma unfold_ball : typing d_any nil (e_unfold ball) (typ_Record P_row).
Proof.
  change (typ_Record P_row) with (open_typ 0 P P_body).
  apply T_Unfold; [ apply P_is_closed | apply P_is_guarded | exact ball_types ].
Qed.

(* ball.moved() *)
Example ball_moved_types : typing d_any nil ball_moved P.
Proof.
  unfold ball_moved. eapply T_App with (T1 := P).
  - apply T_Proj with (R := row_Ext l_x typ_Int row_Empty). exact unfold_ball.
  - exact ball_types.
Qed.

(* ball.moved().x *)
Example ball_moved_x_types : typing d_any nil ball_moved_x typ_Int.
Proof.
  unfold ball_moved_x.
  eapply T_Conv; [ | apply teq_refl ].
  eapply T_Conv.
  - apply T_Proj with (R := row_Ext l_moved (typ_Arrow P P) row_Empty).
    eapply T_Conv.
    + change (typ_Record P_row) with (open_typ 0 P P_body).
      apply T_Unfold; [ apply P_is_closed | apply P_is_guarded | exact ball_moved_types ].
    + apply teq_rec. apply req_sym. exact P_row_ext.
  - apply teq_refl.
Qed.

(* step = program(p) do p.moved() done *)
Example step_m_types : typing d_any nil step_m (typ_Arrow P P).
Proof.
  unfold step_m. apply T_Abs with (L := {}). intros p Hp.
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
  eapply T_App with (T1 := P).
  - apply T_Proj with (R := row_Ext l_x typ_Int row_Empty). apply unfold_var_P.
  - apply var_P.
Qed.

Example step_ball_types : typing d_any nil (e_app step_m ball) P.
Proof. eapply T_App; [ exact step_m_types | exact ball_types ]. Qed.

(* ---- the source program: erasure removes exactly the folds ---- *)

Example erase_ball : erase ball =
  e_rec (fs_cons l_moved
           (e_abs (e_spread (e_fvar_b 0) l_x (e_bin (e_proj (e_fvar_b 0) l_x) bop_add (e_num 1))))
           (fs_cons l_x (e_num 1) fs_nil)).
Proof. reflexivity. Qed.

Example erase_ball_moved : erase ball_moved =
  e_app (e_proj (erase ball) l_moved) (erase ball).
Proof. reflexivity. Qed.

(* ---- runs ---- *)

Lemma ms_trans : forall a b c, multistep a b -> multistep b c -> multistep a c.
Proof. intros a b c H. induction H; [ auto | intros H2; eapply ms_step; eauto ]. Qed.

Lemma ms_lift : forall (f : exp -> exp) a b,
  (forall x y, step x y -> step (f x) (f y)) -> multistep a b -> multistep (f a) (f b).
Proof. intros f a b Hf H. induction H; [ apply ms_refl | eapply ms_step; eauto ]. Qed.

Lemma ms_proj : forall a b l, multistep a b -> multistep (e_proj a l) (e_proj b l).
Proof. intros. apply ms_lift with (f := fun x => e_proj x l); auto. Qed.

Lemma ms_unfold : forall a b, multistep a b -> multistep (e_unfold a) (e_unfold b).
Proof. intros. apply ms_lift with (f := e_unfold); auto. Qed.

Lemma ms_fold : forall a b, multistep a b -> multistep (e_fold a) (e_fold b).
Proof. intros. apply ms_lift with (f := e_fold); auto. Qed.

Lemma ms_app1 : forall a b c, multistep a b -> multistep (e_app a c) (e_app b c).
Proof. intros. apply ms_lift with (f := fun x => e_app x c); auto. Qed.

Lemma ms_spread1 : forall a b l c,
  multistep a b -> multistep (e_spread a l c) (e_spread b l c).
Proof. intros. apply ms_lift with (f := fun x => e_spread x l c); auto. Qed.

Lemma ms_spread2 : forall v l a b, value v ->
  multistep a b -> multistep (e_spread v l a) (e_spread v l b).
Proof.
  intros v l a b Hv. apply ms_lift with (f := fun x => e_spread v l x).
  intros. apply st_spread2; auto.
Qed.

Lemma ms_bin1 : forall a b o c, multistep a b -> multistep (e_bin a o c) (e_bin b o c).
Proof. intros. apply ms_lift with (f := fun x => e_bin x o c); auto. Qed.

(* the fields of ball, and after one [moved] *)
Definition ball_body : exp := bump (e_fvar_b 0).

Definition ball_fields (n : BinNums.Z) : fields :=
  fs_cons l_moved (e_abs ball_body) (fs_cons l_x (e_num n) fs_nil).

Arguments ball_fields n%_znum_scope.

Lemma ball_fields_value : forall n, rec_value (ball_fields n).
Proof. intros n. repeat constructor. Qed.

Lemma ball_value : value ball.
Proof. unfold ball. constructor. constructor. apply ball_fields_value. Qed.

Lemma unfold_ball_runs : multistep (e_unfold ball) (e_rec (ball_fields 1)).
Proof.
  eapply ms_step; [ apply st_unfold_fold; constructor; apply ball_fields_value | apply ms_refl ].
Qed.

(* (unfold ball).moved, the method *)
Lemma moved_field_runs : multistep (e_proj (e_unfold ball) l_moved) (e_abs ball_body).
Proof.
  eapply ms_trans; [ apply ms_proj, unfold_ball_runs | ].
  eapply ms_step; [ apply st_projrec; [ apply ball_fields_value | reflexivity ] | apply ms_refl ].
Qed.

Definition ball2 : exp := e_fold (e_rec (ball_fields 2)).

(* bump(ball): the spread replaces x, the result is folded *)
Lemma bump_ball_runs : multistep (bump ball) ball2.
Proof.
  unfold bump, ball2. apply ms_fold.
  eapply ms_trans; [ apply ms_spread1, unfold_ball_runs | ].
  eapply ms_trans.
  { apply ms_spread2; [ constructor; apply ball_fields_value | ].
    eapply ms_trans; [ apply ms_bin1, ms_proj, unfold_ball_runs | ].
    eapply ms_trans; [ apply ms_bin1; eapply ms_step;
      [ apply st_projrec; [ apply ball_fields_value | reflexivity ] | apply ms_refl ] | ].
    eapply ms_step.
    { apply st_bin; [ constructor | constructor | apply bs_ring_int; reflexivity ]. }
    apply ms_refl. }
  eapply ms_step.
  { apply st_spread; [ apply ball_fields_value | constructor ]. }
  apply ms_refl.
Qed.

(* ball.moved() is ball with x = 2. *)
Example ball_moved_runs : multistep ball_moved ball2.
Proof.
  unfold ball_moved.
  eapply ms_trans; [ apply ms_app1, moved_field_runs | ].
  eapply ms_step; [ apply st_beta, ball_value | ].
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec]. unfold ball_body, bump.
  exact bump_ball_runs.
Qed.

(* ball.moved().x is 2 *)
Example ball_moved_x_runs : multistep ball_moved_x (e_num 2).
Proof.
  unfold ball_moved_x.
  eapply ms_trans; [ apply ms_proj, ms_unfold, ball_moved_runs | ].
  unfold ball2.
  eapply ms_step; [ apply st_proj, st_unfold_fold; constructor; apply ball_fields_value | ].
  eapply ms_step; [ apply st_projrec; [ apply ball_fields_value | reflexivity ] | apply ms_refl ].
Qed.

(* The source program does the same: its erasure reaches the erased result.
   This is [erase_multistep] on the elaborated run. *)
Example erased_ball_moved_x_runs :
  multistep (erase ball_moved_x) (erase (e_num 2)).
Proof. apply erase_multistep. exact ball_moved_x_runs. Qed.

(* step(ball) is ball.moved() *)
Example step_ball_runs : multistep (e_app step_m ball) ball2.
Proof.
  unfold step_m.
  eapply ms_step; [ apply st_beta, ball_value | ].
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec].
  exact ball_moved_runs.
Qed.

(* ---- what has no derivation ---- *)

(* The record view of a receiver needs the unfold: a [fold]ed value has the
   mu type, which is no record, so the field read [ball.moved] without it has
   no derivation.  The checker supplies the unfold; elaboration writes it. *)
Example ball_is_not_its_unrolling : forall G, ~ typing d_any G ball (typ_Record P_row).
Proof.
  intros G H. unfold ball in H. destruct (fold_inv _ _ _ _ H) as [B [Hteq _]].
  apply teq_Mu_inv in Hteq. destruct Hteq as [B' [E _]]. discriminate E.
Qed.

Example proj_without_unfold_rejected : forall G T, ~ typing d_any G (e_proj ball l_moved) T.
Proof.
  intros G T H. destruct (proj_inv _ _ _ _ _ H) as [T0 [R [Hb _]]].
  unfold ball in Hb. destruct (fold_inv _ _ _ _ Hb) as [B [Hteq _]].
  apply teq_Mu_inv in Hteq. destruct Hteq as [B' [E _]]. discriminate E.
Qed.
