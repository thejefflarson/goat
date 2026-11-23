(* Phase 6 stages 1a to 1c: the Eq sort, record comparison, and comparison of
   tag groups and recursive types.  A comparison takes two operands of one
   type that satisfies Eq, so a generic comparison types at a variable of that
   sort, Unit compares, a function does not, two records compare label by
   label, two tags of one group compare by position and then by payload, and a
   fold compares as what it holds.  The accepted examples fail to compile if a
   rule is dropped, and the rejected ones if a rule is loosened. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatLit.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatPhase1.
Require Import Goat.GoatRecArithExamples.
Require Import Goat.GoatPhase3.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

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

(* ---- stage 1b: records compare by label ---- *)

Definition pair_xy (m n : num) : exp :=
  e_rec (fs_cons lx (e_num m) (fs_cons ly (e_num n) fs_nil)).
Definition pair_yx (m n : num) : exp :=
  e_rec (fs_cons ly (e_num n) (fs_cons lx (e_num m) fs_nil)).

Arguments pair_xy (m n)%_znum_scope.
Arguments pair_yx (m n)%_znum_scope.

Lemma pair_xy_types : forall m n, typing d_any nil (pair_xy m n) (typ_Record row_inner).
Proof.
  intros m n. unfold pair_xy, row_inner. apply T_Record; [ | reflexivity ].
  eapply FT_cons; [ apply T_Num; [ solve_uniq | exact I ] | ].
  eapply FT_cons; [ apply T_Num; [ solve_uniq | exact I ] | apply FT_nil; solve_uniq ].
Qed.

Lemma pair_yx_types : forall m n, typing d_any nil (pair_yx m n) (typ_Record row_inner).
Proof.
  intros m n. unfold pair_yx, row_inner.
  eapply T_Conv with (T := typ_Record (row_Ext ly typ_Int (row_Ext lx typ_Int row_Empty))).
  - apply T_Record; [ | reflexivity ].
    eapply FT_cons; [ apply T_Num; [ solve_uniq | exact I ] | ].
    eapply FT_cons; [ apply T_Num; [ solve_uniq | exact I ] | apply FT_nil; solve_uniq ].
  - apply teq_rec. apply req_swap. unfold lx, ly. discriminate.
Qed.

Lemma pair_compare_types : forall o a b c d, kind o = k_cmp ->
  typing d_any nil (e_bin (pair_xy a b) o (pair_yx c d)) typ_Bool.
Proof.
  intros o a b c d Hk.
  eapply T_Bin with (A := typ_Record row_inner) (B := typ_Record row_inner);
    [ apply pair_xy_types | apply pair_yx_types | apply sig_cmp; [ exact Hk | ] ].
  simpl. repeat split; exact I.
Qed.

(* {x: 1, y: 2} == {y: 2, x: 1}: the order the fields are written in does not matter. *)
Example pair_equal_in_either_order : bin_step bop_eq (pair_xy 1 2) (pair_yx 1 2) e_true.
Proof.
  refine (bs_cmp bop_eq _ _ Eq eq_refl _).
  unfold pair_xy, pair_yx. apply cr_rec. unfold rec_labels. simpl.
  eapply cf_eq; [ reflexivity | reflexivity | exact (cr_int 1 1) | ].
  eapply cf_eq; [ reflexivity | reflexivity | exact (cr_int 2 2) | ].
  apply cf_nil.
Qed.

(* {x: 1, y: 2} < {y: 3, x: 1}: x ties, then y decides. *)
Example pair_less_by_second_field : bin_step bop_lt (pair_xy 1 2) (pair_yx 1 3) e_true.
Proof.
  refine (bs_cmp bop_lt _ _ Lt eq_refl _).
  unfold pair_xy, pair_yx. apply cr_rec. unfold rec_labels. simpl.
  eapply cf_eq; [ reflexivity | reflexivity | exact (cr_int 1 1) | ].
  eapply cf_ne; [ reflexivity | reflexivity | exact (cr_int 2 3) | discriminate ].
Qed.

(* Labels compare in label order, not in the order the first record lists
   them: {p: 1, x: 2} against {p: 2, x: 1} decides on x (label 0) before p
   (label 2), so the first is the greater. *)
Definition px (p x : num) : exp :=
  e_rec (fs_cons lp (e_num p) (fs_cons lx (e_num x) fs_nil)).

Arguments px (p x)%_znum_scope.

Example label_order_gt : bin_step bop_gt (px 1 2) (px 2 1) e_true.
Proof.
  refine (bs_cmp bop_gt _ _ Gt eq_refl _).
  unfold px. apply cr_rec. unfold rec_labels. simpl.
  eapply cf_ne; [ reflexivity | reflexivity | exact (cr_int 2 1) | discriminate ].
Qed.

Lemma label_order_only_gt : forall c, cmp_rel (px 1 2) (px 2 1) c -> c = Gt.
Proof.
  intros c H. unfold px in H. apply cmp_rel_rec_inv in H. unfold rec_labels in H. simpl in H.
  unfold lx, lp in *. inversion H; subst; simpl in *;
    repeat match goal with E : Some _ = Some _ |- _ => inversion E; subst; clear E end;
    match goal with Hc : cmp_rel (e_num _) (e_num _) _ |- _ =>
      inversion Hc; subst; try (match goal with Hf : fl_pair _ _ |- _ => inversion Hf end);
      simpl in *; first [ reflexivity | discriminate | congruence ] end.
Qed.

Example label_order_not_lt : ~ bin_step bop_lt (px 1 2) (px 2 1) e_true.
Proof.
  intros H. inversion H; subst;
    first [ (match goal with Hf : fl_pair _ _ |- _ => inversion Hf end) | idtac ].
  match goal with Hc : cmp_rel _ _ _ |- _ =>
    rewrite (label_order_only_gt _ Hc) in *; simpl in *; discriminate end.
Qed.

(* A record inside a record compares the same way. *)
Example nested_less : bin_step bop_lt outer_l outer_r e_true.
Proof.
  refine (bs_cmp bop_lt _ _ Lt eq_refl _).
  unfold outer_l, outer_r. apply cr_rec. unfold rec_labels. simpl.
  eapply cf_ne; [ reflexivity | reflexivity | exact (cr_int 4 5) | discriminate ].
Qed.

Example nested_less_types : typing d_any nil (e_bin outer_l bop_lt outer_r) typ_Bool.
Proof.
  eapply T_Bin with (A := typ_Record row_outer) (B := typ_Record row_outer);
    [ apply outer_l_types | apply outer_r_types | apply sig_cmp; [ reflexivity | ] ].
  simpl. repeat split; exact I.
Qed.

Definition outer_l2 : exp :=
  e_rec (fs_cons lx (e_num 4)
          (fs_cons lp (e_rec (fs_cons ly (e_num 3) (fs_cons lx (e_num 2) fs_nil))) fs_nil)).

Example nested_equal_in_other_order : bin_step bop_eq outer_l outer_l2 e_true.
Proof.
  refine (bs_cmp bop_eq _ _ Eq eq_refl _).
  unfold outer_l, outer_l2, inner_l. apply cr_rec. unfold rec_labels. simpl.
  eapply cf_eq; [ reflexivity | reflexivity | exact (cr_int 4 4) | ].
  eapply cf_eq; [ reflexivity | reflexivity | | apply cf_nil ].
  apply cr_rec. unfold rec_labels. simpl.
  eapply cf_eq; [ reflexivity | reflexivity | exact (cr_int 2 2) | ].
  eapply cf_eq; [ reflexivity | reflexivity | exact (cr_int 3 3) | ].
  apply cf_nil.
Qed.

(* Records of strings, booleans and unit are Eq; a record holding a function is not. *)
Example record_of_eq_fields_is_eq :
  sat d_any k_Eq
    (typ_Record (row_Ext lx typ_String (row_Ext ly typ_Bool (row_Ext lp typ_Unit row_Empty)))).
Proof. simpl. repeat split; first [ exact I | (right; reflexivity) ]. Qed.

Example record_with_function_is_not_eq :
  ~ sat d_any k_Eq (typ_Record (row_Ext lx (typ_Arrow typ_Int typ_Int) row_Empty)).
Proof. simpl. intros [H _]. discriminate H. Qed.

(* ---- stage 1c: tags compare by position, then by payload ---- *)

(* tag Level = Low | Medium | High *)
Definition low : exp := e_con level 0 e_unit.
Definition medium : exp := e_con level 1 e_unit.
Definition high : exp := e_con level 2 e_unit.

Example level_is_eq : sat d_any k_Eq (typ_Grp level (spine [])).
Proof. exact I. Qed.

Lemma level_types : forall tg, tg < 3 ->
  typing d_any nil (e_con level tg e_unit) (typ_Grp level (spine [])).
Proof.
  intros tg Hlt. destruct tg as [ | [ | [ | tg ] ] ]; [ | | | lia ];
    (apply T_Con; [ simpl; lia | cbn; apply T_Unit; solve_uniq ]).
Qed.

Example level_compare_types : forall o, kind o = k_cmp ->
  typing d_any nil (e_bin low o high) typ_Bool.
Proof.
  intros o Hk.
  eapply T_Bin with (A := typ_Grp level (spine [])) (B := typ_Grp level (spine []));
    [ apply level_types; lia | apply level_types; lia | apply sig_cmp; [ exact Hk | exact I ] ].
Qed.

Example low_lt_medium : bin_step bop_lt low medium e_true.
Proof. refine (bs_cmp bop_lt _ _ Lt eq_refl _). apply cr_con_lt. lia. Qed.

Example medium_lt_high : bin_step bop_lt medium high e_true.
Proof. refine (bs_cmp bop_lt _ _ Lt eq_refl _). apply cr_con_lt. lia. Qed.

Example high_gt_low : bin_step bop_gt high low e_true.
Proof. refine (bs_cmp bop_gt _ _ Gt eq_refl _). apply cr_con_gt. lia. Qed.

Example medium_equals_medium : bin_step bop_eq medium medium e_true.
Proof. refine (bs_cmp bop_eq _ _ Eq eq_refl _). apply cr_con_eq. apply cr_unit. Qed.

(* Position decides, so High is not below Low. *)
Example high_not_lt_low : ~ bin_step bop_lt high low e_true.
Proof.
  intros H. inversion H; subst;
    first [ (match goal with Hf : fl_pair _ _ |- _ => inversion Hf end) | idtac ].
  match goal with Hc : cmp_rel _ _ _ |- _ =>
    destruct (cmp_rel_con_inv _ _ _ _ _ _ Hc) as [[E _] | [[Hl ->] | [Hg ->]]];
      [ discriminate E | lia | simpl in *; discriminate ] end.
Qed.

(* ---- lists: Empty < Link, then head, then tail ---- *)

Definition lst_1_9 : exp := link (e_num 1) (link (e_num 9) empty_l).
Definition lst_2 : exp := link (e_num 2) empty_l.
Definition lst_1_2 : exp := link (e_num 1) (link (e_num 2) empty_l).
Definition lst_1_2_0 : exp := link (e_num 1) (link (e_num 2) (link (e_num 0) empty_l)).
Definition lst_1 : exp := link (e_num 1) empty_l.

Example list_is_eq_at_int : sat d_any k_Eq (typ_Grp list_g (spine [typ_Int])).
Proof. simpl. split; [ intros _; exact I | exact I ]. Qed.

Lemma list_int_types : forall l, l = lst_1_9 \/ l = lst_2 \/ l = lst_1_2 \/ l = lst_1_2_0 \/ l = lst_1 \/ l = empty_l ->
  typing d_any nil l (typ_Grp list_g (spine [typ_Int])).
Proof.
  intros l H. destruct H as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    unfold lst_1_9, lst_2, lst_1_2, lst_1_2_0, lst_1;
    repeat first [ apply link_types | apply empty_is_every_list | (apply T_Num; [ solve_uniq | exact I ]) ].
Qed.

Example lists_compare_types : typing d_any nil (e_bin lst_1_9 bop_lt lst_2) typ_Bool.
Proof.
  eapply T_Bin with (A := typ_Grp list_g (spine [typ_Int])) (B := typ_Grp list_g (spine [typ_Int]));
    [ apply list_int_types; tauto | apply list_int_types; tauto
    | apply sig_cmp; [ reflexivity | exact list_is_eq_at_int ] ].
Qed.

(* [1, 9] < [2]: the heads decide. *)
Example list_head_decides : bin_step bop_lt lst_1_9 lst_2 e_true.
Proof.
  refine (bs_cmp bop_lt _ _ Lt eq_refl _).
  unfold lst_1_9, lst_2, link. apply cr_con_eq. apply cr_rec. unfold rec_labels. simpl.
  eapply cf_ne; [ reflexivity | reflexivity | exact (cr_int 1 2) | discriminate ].
Qed.

(* [] < [1]: Empty is the first tag. *)
Example empty_lt_one : bin_step bop_lt empty_l lst_1 e_true.
Proof.
  refine (bs_cmp bop_lt _ _ Lt eq_refl _).
  unfold empty_l, lst_1, link. apply cr_con_lt. lia.
Qed.

(* [1, 2] < [1, 2, 0]: a prefix comes first. *)
Example list_prefix_first : bin_step bop_lt lst_1_2 lst_1_2_0 e_true.
Proof.
  refine (bs_cmp bop_lt _ _ Lt eq_refl _).
  unfold lst_1_2, lst_1_2_0, link. apply cr_con_eq. apply cr_rec. unfold rec_labels. simpl.
  eapply cf_eq; [ reflexivity | reflexivity | exact (cr_int 1 1) | ].
  eapply cf_ne; [ reflexivity | reflexivity | | discriminate ].
  apply cr_con_eq. apply cr_rec. unfold rec_labels. simpl.
  eapply cf_eq; [ reflexivity | reflexivity | exact (cr_int 2 2) | ].
  eapply cf_ne; [ reflexivity | reflexivity | | discriminate ].
  unfold empty_l. apply cr_con_lt. lia.
Qed.

(* Any two lists of Int compare: totality reaches a group that contains itself. *)
Example lists_have_a_result : exists c, cmp_rel lst_1_9 lst_2 c.
Proof.
  eapply cmp_total with (D := d_any) (G := nil) (A := typ_Grp list_g (spine [typ_Int]));
    [ exact list_is_eq_at_int | | | apply list_int_types; tauto | apply list_int_types; tauto ].
  - unfold lst_1_9, link, empty_l. repeat first [ constructor | assumption ].
  - unfold lst_2, link, empty_l. repeat first [ constructor | assumption ].
Qed.

(* A list of functions is not Eq; a group that never mentions its parameter is
   Eq whatever the parameter. *)
Example list_of_functions_is_not_eq :
  ~ sat d_any k_Eq (typ_Grp list_g (spine [typ_Arrow typ_Int typ_Int])).
Proof.
  simpl. intros [H _]. discriminate (H (ex_intro _ [6; 0] (conj (or_intror (or_introl eq_refl)) (or_introl eq_refl)))).
Qed.

Example unused_parameter_is_unconstrained :
  sat d_any k_Eq (typ_Grp shot (spine [typ_Arrow typ_Int typ_Int])).
Proof.
  simpl. split; [ | exact I ].
  intros [cs [Hcs H6]]. simpl in Hcs. destruct Hcs as [<- | [<- | []]];
    simpl in H6; first [ contradiction | (destruct H6 as [H6 | []]; discriminate H6) ].
Qed.

(* ---- a recursive tree: mu t. {v: Int; kids: List t} ---- *)

Definition tree_body : typ :=
  typ_Record (row_Ext 0 typ_Int (row_Ext 1 (typ_Grp list_g (spine [typ_Bvar 0])) row_Empty)).
Definition tree_t : typ := typ_Mu tree_body.

Example tree_is_eq : sat d_any k_Eq tree_t.
Proof.
  unfold tree_t, tree_body. simpl. repeat split; first [ exact I | (right; reflexivity) | (intros _; right; reflexivity) ].
Qed.

Example tree_with_a_function_is_not_eq :
  ~ sat d_any k_Eq (typ_Mu (typ_Record (row_Ext 0 (typ_Arrow (typ_Bvar 0) (typ_Bvar 0)) row_Empty))).
Proof. simpl. intros [H _]. discriminate H. Qed.

Example tree_closed : lct 0 tree_t.
Proof. unfold tree_t, tree_body. simpl. repeat split; first [ exact I | lia ]. Qed.

Example tree_guarded : guarded tree_body.
Proof. unfold guarded, tree_body. simpl. repeat split; auto. Qed.

Example tree_unrolls :
  open_typ 0 tree_t tree_body =
  typ_Record (row_Ext 0 typ_Int (row_Ext 1 (typ_Grp list_g (spine [tree_t])) row_Empty)).
Proof. reflexivity. Qed.

Definition node (n : num) (kids : exp) : exp :=
  e_fold (e_rec (fs_cons 0 (e_num n) (fs_cons 1 kids fs_nil))).
Arguments node n%_znum_scope kids.

Lemma node_types : forall n kids,
  typing d_any nil kids (typ_Grp list_g (spine [tree_t])) ->
  typing d_any nil (node n kids) tree_t.
Proof.
  intros n kids Hk. unfold node. apply T_Fold; [ apply tree_closed | apply tree_guarded | ].
  change (typ_Mu tree_body) with tree_t. rewrite tree_unrolls.
  apply T_Record; [ | reflexivity ]. eapply FT_cons; [ apply T_Num; [ solve_uniq | exact I ] | ].
  eapply FT_cons; [ exact Hk | apply FT_nil; solve_uniq ].
Qed.

Definition leaf (n : num) : exp := node n empty_l.
Arguments leaf n%_znum_scope.

Lemma leaf_types : forall n, typing d_any nil (leaf n) tree_t.
Proof. intros n. apply node_types. apply empty_is_every_list. Qed.

Lemma one_kid_types : forall t, typing d_any nil t tree_t ->
  typing d_any nil (link t empty_l) (typ_Grp list_g (spine [tree_t])).
Proof. intros t Ht. apply link_types; [ exact Ht | apply empty_is_every_list ]. Qed.

Example tree_compare_types :
  typing d_any nil (e_bin (leaf 1) bop_lt (node 1 (link (leaf 0) empty_l))) typ_Bool.
Proof.
  eapply T_Bin with (A := tree_t) (B := tree_t);
    [ apply leaf_types | apply node_types, one_kid_types, leaf_types
    | apply sig_cmp; [ reflexivity | exact tree_is_eq ] ].
Qed.

(* A leaf is below a node with a kid at the same value: Empty < Link. *)
Example leaf_lt_node : bin_step bop_lt (leaf 1) (node 1 (link (leaf 0) empty_l)) e_true.
Proof.
  refine (bs_cmp bop_lt _ _ Lt eq_refl _).
  unfold leaf, node. apply cr_fold. apply cr_rec. unfold rec_labels. simpl.
  eapply cf_eq; [ reflexivity | reflexivity | exact (cr_int 1 1) | ].
  eapply cf_ne; [ reflexivity | reflexivity | | discriminate ].
  unfold empty_l, link. apply cr_con_lt. lia.
Qed.

(* Two trees compare through their kids: the comparison goes under the fold and
   through the list. *)
Example kids_decide : bin_step bop_lt (node 1 (link (leaf 3) empty_l)) (node 1 (link (leaf 4) empty_l)) e_true.
Proof.
  refine (bs_cmp bop_lt _ _ Lt eq_refl _).
  unfold node, leaf, link, empty_l. apply cr_fold. apply cr_rec. unfold rec_labels. simpl.
  eapply cf_eq; [ reflexivity | reflexivity | exact (cr_int 1 1) | ].
  eapply cf_ne; [ reflexivity | reflexivity | | discriminate ].
  apply cr_con_eq. apply cr_rec. unfold rec_labels. simpl.
  eapply cf_ne; [ reflexivity | reflexivity | | discriminate ].
  apply cr_fold. apply cr_rec. unfold rec_labels. simpl.
  eapply cf_ne; [ reflexivity | reflexivity | exact (cr_int 3 4) | discriminate ].
Qed.

Example trees_have_a_result :
  exists c, cmp_rel (leaf 1) (node 1 (link (leaf 0) empty_l)) c.
Proof.
  eapply cmp_total with (D := d_any) (G := nil) (A := tree_t);
    [ exact tree_is_eq | | | apply leaf_types | apply node_types, one_kid_types, leaf_types ].
  - unfold leaf, node, empty_l. repeat constructor.
  - unfold leaf, node, link, empty_l. repeat constructor.
Qed.
