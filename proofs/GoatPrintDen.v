(* The tree the printer builds denotes the term it was printed from. A bound
   index of the term is read back as the free variable the parser gives the
   binder's name, and each binder closes that variable again, so the term is
   recovered exactly (up to the label table). *)

From Stdlib Require Import String List Arith Lia.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintParse.
Require Import Goat.GoatPrintInst.
Open Scope string_scope.
Open Scope list_scope.

(* ---- the label table ---- *)

Definition LabelsOK (tbl : list string) (ls : list nat) : Prop :=
  forall n, List.In n ls -> index_of (lname n) tbl = n.

Lemma labelsok_app_l : forall tbl a b, LabelsOK tbl (a ++ b) -> LabelsOK tbl a.
Proof. intros tbl a b H n Hn. apply H, in_or_app. left. exact Hn. Qed.

Lemma labelsok_app_r : forall tbl a b, LabelsOK tbl (a ++ b) -> LabelsOK tbl b.
Proof. intros tbl a b H n Hn. apply H, in_or_app. right. exact Hn. Qed.

Lemma lab_lname : forall tbl n, LabelsOK tbl [n] -> lab tbl (lname n) = n.
Proof. intros tbl n H. unfold lab. apply H. left. reflexivity. Qed.

(* ---- extending a chain by a postfix ---- *)

(* A call straight after an access is a dot call, so a chain that ends in an
   access cannot be extended by a call. *)
Definition ends_in_access (cs : list tree) : Prop :=
  exists init c, cs = init ++ [Node R_access c].

Lemma ends_cons : forall t cs, ends_in_access cs -> ends_in_access (t :: cs).
Proof.
  intros t cs [init [c H]]. exists (t :: init), c. rewrite H. reflexivity.
Qed.

Lemma ends_access_last : forall pre t,
  (forall c, t <> Node R_access c) -> ~ ends_in_access (pre ++ [t]).
Proof.
  intros pre t Ht [init [c H]].
  apply app_inj_tail in H. destruct H as [_ H]. exact (Ht c H).
Qed.

Lemma den_posts_snoc : forall var_of tbl e rest e0,
  Den_posts var_of tbl e rest e0 ->
  forall post e', Den_posts var_of tbl e0 [post] e' ->
  (starts_call [post] -> ~ ends_in_access rest) ->
  Den_posts var_of tbl e (rest ++ [post]) e'.
Proof.
  intros var_of tbl e rest e0 H. induction H; intros post e'' Hp Hcall.
  - exact Hp.
  - (* access *)
    simpl. apply DP_access.
    + destruct rest as [| r rs].
      * intros Hstarts. apply (Hcall Hstarts).
        exists [], [sym "."; ident l]. reflexivity.
      * exact H.
    + apply IHDen_posts; [ exact Hp | ].
      intros Hstarts Hend. exact (Hcall Hstarts (ends_cons _ _ Hend)).
  - (* take *)
    simpl. apply DP_take.
    apply IHDen_posts; [ exact Hp | ].
    intros Hstarts Hend. exact (Hcall Hstarts (ends_cons _ _ Hend)).
  - (* dot call on a path *)
    simpl. eapply DP_dot_path; [ eassumption | eassumption | ].
    apply IHDen_posts; [ exact Hp | ].
    intros Hstarts Hend. exact (Hcall Hstarts (ends_cons _ _ (ends_cons _ _ Hend))).
  - (* dot call on another receiver *)
    simpl. eapply DP_dot_bind; [ eassumption | eassumption | eassumption | ].
    apply IHDen_posts; [ exact Hp | ].
    intros Hstarts Hend. exact (Hcall Hstarts (ends_cons _ _ (ends_cons _ _ Hend))).
  - (* call *)
    simpl. eapply DP_call; [ eassumption | ].
    apply IHDen_posts; [ exact Hp | ].
    intros Hstarts Hend. exact (Hcall Hstarts (ends_cons _ _ Hend)).
  - (* call with no arguments *)
    simpl. apply DP_call_unit.
    apply IHDen_posts; [ exact Hp | ].
    intros Hstarts Hend. exact (Hcall Hstarts (ends_cons _ _ Hend)).
  - (* dot call on a path, no other arguments *)
    simpl. apply DP_dot_path_unit; [ assumption | ].
    apply IHDen_posts; [ exact Hp | ].
    intros Hstarts Hend. exact (Hcall Hstarts (ends_cons _ _ (ends_cons _ _ Hend))).
  - (* dot call on another receiver, no other arguments *)
    simpl. eapply DP_dot_bind_unit; [ eassumption | ].
    apply IHDen_posts; [ exact Hp | ].
    intros Hstarts Hend. exact (Hcall Hstarts (ends_cons _ _ (ends_cons _ _ Hend))).
Qed.

Lemma den_chain_snoc : forall var_of tbl cs e0 post e',
  Den_chain var_of tbl cs e0 -> Den_posts var_of tbl e0 [post] e' ->
  (starts_call [post] -> ~ ends_in_access cs) ->
  Den_chain var_of tbl (cs ++ [post]) e'.
Proof.
  intros var_of tbl cs e0 post e' H Hp Hcall. inversion H; subst.
  - simpl. eapply DC_head; [ eassumption | ].
    eapply den_posts_snoc; [ eassumption | eassumption | ].
    intros Hstarts Hend. exact (Hcall Hstarts (ends_cons _ _ Hend)).
  - simpl. eapply DC_paren; [ eassumption | ].
    eapply den_posts_snoc; [ eassumption | eassumption | ].
    intros Hstarts Hend.
    exact (Hcall Hstarts (ends_cons _ _ (ends_cons _ _ (ends_cons _ _ Hend)))).
  - (* a tag: the printer's table has none *) discriminate.
  - discriminate.
  - discriminate.
Qed.

Lemma den_chain_call : forall var_of tbl cs e0 b ea,
  Den_chain var_of tbl cs e0 -> Den var_of tbl (Node R_expr b) ea ->
  ~ ends_in_access cs ->
  Den_chain var_of tbl (cs ++ [call_tree b]) (e_app e0 ea).
Proof.
  intros var_of tbl cs e0 b ea Hc Hb Hend.
  eapply den_chain_snoc; [ exact Hc | | intros _; exact Hend ].
  eapply DP_call with (es := [ea]).
  - apply DA_last. exact Hb.
  - apply DP_nil.
Qed.

Lemma den_chain_call_unit : forall var_of tbl cs e0,
  Den_chain var_of tbl cs e0 -> ~ ends_in_access cs ->
  Den_chain var_of tbl (cs ++ [call_unit_tree]) (e_app e0 e_unit).
Proof.
  intros var_of tbl cs e0 Hc Hend.
  eapply den_chain_snoc; [ exact Hc | | intros _; exact Hend ].
  unfold call_unit_tree. apply DP_call_unit. apply DP_nil.
Qed.

Lemma den_chain_access : forall var_of tbl cs e0 l,
  Den_chain var_of tbl cs e0 -> LabelsOK tbl [l] ->
  Den_chain var_of tbl (cs ++ [access_tree l]) (e_proj e0 l).
Proof.
  intros var_of tbl cs e0 l Hc Hl.
  eapply den_chain_snoc; [ exact Hc | | intros Hstarts; destruct Hstarts ].
  unfold access_tree. apply DP_access; [ intros Hstarts; destruct Hstarts | ].
  rewrite (lab_lname tbl l Hl). apply DP_nil.
Qed.

(* No operand of a call ends in an access: a projection callee is
   parenthesised. *)
Lemma callee_not_access : forall G P f, ~ ends_in_access (as_callee f (block G P f)).
Proof.
  intros G P f. destruct f; try (cbn [as_callee as_operand block paren_kids];
    first
    [ (intros [init [c H]]; destruct init; discriminate H)
    | (apply (ends_access_last [sym "("; Node R_expr _]); intros c Hc; discriminate Hc)
    | (apply (ends_access_last []); intros c Hc; discriminate Hc)
    | (apply ends_access_last; intros c Hc; discriminate Hc) ]; fail).
  - destruct (block_abs_cases G P f) as [(-> & E) | (_ & E)];
      cbn [as_callee as_operand]; rewrite E;
      apply (ends_access_last []); intros c Hc; discriminate Hc.
  - destruct (block_app_cases G P f1 f2) as [(-> & E) | (_ & E)];
      cbn [as_callee as_operand]; rewrite E;
      apply ends_access_last; intros c Hc; discriminate Hc.
  - destruct (block_ite_cases G P f1 f2 f3) as [(-> & E) | (_ & E)];
      cbn [as_callee as_operand]; rewrite E;
      apply (ends_access_last []); intros c Hc; discriminate Hc.
Qed.

Lemma den_pack : forall var_of tbl G P e x,
  Den_chain var_of tbl (block G P e) x ->
  Den var_of tbl (Node R_expr (block G P e)) x /\
  (NonRec e -> BlkG var_of tbl (block G P e) x) /\
  (NonLet e -> Den_math var_of tbl (block G P e) x) /\
  (NonLet e -> bin_end e = false -> Den_chain var_of tbl (block G P e) x).
Proof.
  intros var_of tbl G P e x H.
  assert (Hb : BlkG var_of tbl (block G P e) x)
    by (intros ctx fin; apply DK_chain; apply DM_chain; exact H).
  repeat split.
  - exact (D_expr_g _ _ _ _ Hb).
  - intros _. exact Hb.
  - intros _. apply DM_chain. exact H.
  - intros _ _. exact H.
Qed.

Lemma den_chain_single : forall var_of tbl t e,
  Den var_of tbl t e -> Den_chain var_of tbl [t] e.
Proof. intros var_of tbl t e H. eapply DC_head; [ exact H | apply DP_nil ]. Qed.

Lemma den_chain_paren : forall var_of tbl b e,
  Den var_of tbl (Node R_expr b) e -> Den_chain var_of tbl (paren_kids b) e.
Proof.
  intros var_of tbl b e H. unfold paren_kids.
  eapply DC_paren; [ exact H | apply DP_nil ].
Qed.

(* A printed binding's value is never a bare function literal, so the binding is
   a plain let and not a group member. *)
Lemma fn_value_single : forall cs,
  fn_value cs = true -> exists c, cs = [Node R_function c].
Proof.
  intros cs H. destruct cs as [| t [| t2 cs']].
  - discriminate H.
  - destruct t as [k | r c]; try discriminate H.
    destruct r; try discriminate H. eauto.
  - destruct t as [k | r c]; try discriminate H.
    destruct r; discriminate H.
Qed.

Lemma block_app_not_fn : forall G P f a c, block G P (e_app f a) <> [Node R_function c].
Proof.
  intros G P f a c Hc.
  destruct (block_app_cases G P f a) as [(_ & E) | (_ & E)]; rewrite E in Hc.
  - assert (Hin : In call_unit_tree [Node R_function c])
      by (rewrite <- Hc; apply in_or_app; right; left; reflexivity).
    destruct Hin as [Hin | []]; discriminate Hin.
  - assert (Hin : In (call_tree (block G P a)) [Node R_function c])
      by (rewrite <- Hc; apply in_or_app; right; left; reflexivity).
    destruct Hin as [Hin | []]; discriminate Hin.
Qed.

Lemma block_proj_not_fn : forall G P f l c, block G P (e_proj f l) <> [Node R_function c].
Proof.
  intros G P f l c Hc. destruct (proj_level G P f) eqn:EL.
  - rewrite (block_proj_group G P f l n EL) in Hc. discriminate Hc.
  - rewrite (block_proj_plain G P f l EL) in Hc.
    assert (Hin : In (access_tree l) [Node R_function c])
      by (rewrite <- Hc; apply in_or_app; right; left; reflexivity).
    destruct Hin as [Hin | []]; discriminate Hin.
Qed.

Lemma block_ite_not_fn : forall G P a b d c, block G P (e_ite a b d) <> [Node R_function c].
Proof.
  intros G P a b d c Hc.
  destruct (block_ite_cases G P a b d) as [(_ & E) | (_ & E)]; rewrite E in Hc; discriminate Hc.
Qed.

Lemma value_not_fn : forall G P v,
  is_fn_decl (decl_tree P (as_value v (block G P v))) = false.
Proof.
  intros G P v. unfold decl_tree, decl_named, is_fn_decl.
  destruct (fn_value (as_value v (block G P v))) eqn:H; [ | reflexivity ].
  exfalso. destruct (fn_value_single _ H) as (c & Hc).
  destruct v; try (cbn [as_value block] in Hc;
    first
    [ discriminate Hc
    | (match goal with
       | o : bop |- _ =>
           assert (Hin : In (op_tree o) [Node R_function c])
             by (rewrite <- Hc; apply in_or_app; right; left; reflexivity);
           destruct Hin as [Hin | []]; destruct o; discriminate Hin
       end) ]; fail).
  all: cbn [as_value] in Hc;
    first [ exact (block_app_not_fn _ _ _ _ _ Hc)
          | exact (block_proj_not_fn _ _ _ _ _ Hc)
          | exact (block_ite_not_fn _ _ _ _ _ _ Hc) ].
Qed.

Lemma is_fn_decl_abs : forall x G P v,
  is_abs v -> is_fn_decl (decl_named x (block G P v)) = true.
Proof.
  intros x G P v H. destruct v; try contradiction.
  unfold is_fn_decl, decl_named.
  match goal with |- context [block G P (e_abs ?b)] =>
    destruct (block_abs_cases G P b) as [(_ & E) | (_ & E)]; rewrite E; reflexivity end.
Qed.

Lemma is_abs_nonlet : forall v, is_abs v -> NonLet v.
Proof. intros v H. destruct v; first [ contradiction | exact I ]. Qed.

(* ---- the groups in scope lie below the depth ---- *)

Definition GOK (G : Grp) (P : nat) : Prop := forall L m, grp_size G L = Some m -> L < P.

Lemma gok_S : forall G P, GOK G P -> GOK G (S P).
Proof. intros G P H L m Hg. specialize (H L m Hg). lia. Qed.

Lemma gok_none : forall G P, GOK G P -> grp_size G P = None.
Proof.
  intros G P H. destruct (grp_size G P) eqn:E; [ | reflexivity ].
  specialize (H P n E). lia.
Qed.

Lemma gok_cons : forall G P n, GOK G P -> GOK ((P, n) :: G) (S P).
Proof.
  intros G P n H L m Hg. simpl in Hg. destruct (Nat.eqb P L) eqn:E.
  - apply Nat.eqb_eq in E. lia.
  - specialize (H L m Hg). lia.
Qed.

Lemma proj_level_other : forall G P f,
  (forall i, f <> e_fvar_b i) -> proj_level G P f = None.
Proof. intros G P f H. destruct f; try reflexivity. exfalso. exact (H _ eq_refl). Qed.

Lemma proj_level_some : forall G P f L,
  proj_level G P f = Some L ->
  exists i m, f = e_fvar_b i /\ L = P - 1 - i /\ grp_size G L = Some m.
Proof.
  intros G P f L H. destruct (bvar_or_not f) as [[i ->] | Hnb].
  - unfold proj_level in H. destruct (grp_size G (P - 1 - i)) eqn:E; [ | discriminate H ].
    injection H as <-. exists i, n. auto.
  - rewrite (proj_level_other G P f Hnb) in H. discriminate H.
Qed.

Lemma inst_proj_group : forall var_of G P i l m,
  grp_size G (P - 1 - i) = Some m ->
  inst var_of G P (e_proj (e_fvar_b i) l) = e_fvar_f (var_of (gm (P - 1 - i) l)).
Proof.
  intros var_of G P i l m H. unfold inst. cbn [inst_rec]. rewrite Nat.add_0_l, H. reflexivity.
Qed.

Lemma inst_proj_plain : forall var_of G P f l,
  proj_level G P f = None ->
  inst var_of G P (e_proj f l) = e_proj (inst var_of G P f) l.
Proof.
  intros var_of G P f l H. destruct (bvar_or_not f) as [[i ->] | Hnb].
  - unfold proj_level in H. destruct (grp_size G (P - 1 - i)) eqn:E; [ discriminate H | ].
    unfold inst. cbn [inst_rec]. rewrite Nat.add_0_l, E. reflexivity.
  - unfold inst. exact (inst_proj_other var_of G 0 P f l Hnb).
Qed.

Lemma curry_one : forall x b, curry [x] b = e_abs (close_exp x b).
Proof. reflexivity. Qed.

Lemma inst_abs : forall var_of G P b, inst var_of G P (e_abs b) = e_abs (inst_rec var_of G 1 P b).
Proof. reflexivity. Qed.

Lemma lbls_proj_plain : forall G P f l,
  proj_level G P f = None -> lbls G P (e_proj f l) = lbls G P f ++ [l].
Proof. intros G P f l H. cbn [lbls]. rewrite H. reflexivity. Qed.

Lemma wrap_group_nonempty : forall xs gs b,
  xs <> [] -> wrap_group xs gs b = e_letrec (group_fields xs gs) (bind_group xs b).
Proof. intros xs gs b H. destruct xs; [ contradiction | reflexivity ]. Qed.

(* The members of a group and its body, read as the hoisted group and the
   rest of the block, are the instantiated group. *)
Lemma den_wrap : forall var_of, names_distinct var_of -> forall D n G fs b,
  0 < n -> grp_size G D = Some n ->
  scoped_group G (S D) 0 fs -> scoped G (S D) b ->
  wrap_group (List.map var_of (gnames D 0 n))
             (List.map (inst_rec var_of G 0 (S D)) (fvals fs))
             (inst_rec var_of G 0 (S D) b)
  = e_letrec (inst_fields var_of G 1 D fs) (inst_rec var_of G 1 D b).
Proof.
  intros var_of Hdist D n G fs b Hn HD Hg Hb.
  destruct n as [| n']; [ lia | ].
  rewrite wrap_group_nonempty; [ | cbn [gnames List.map]; discriminate ].
  unfold group_fields, bind_group.
  rewrite (group_fields_inst var_of Hdist D (S n') G HD fs 0 Hg).
  rewrite (proj1 (bind_inst var_of Hdist D (S n')) b G 0 HD Hb).
  reflexivity.
Qed.

(* ---- the main lemma ---- *)

Lemma print_den : forall var_of tbl, names_distinct var_of ->
  (forall e G P, GOK G P -> scoped G P e -> LabelsOK tbl (lbls G P e) ->
     Den var_of tbl (Node R_expr (block G P e)) (inst var_of G P e) /\
     (NonRec e -> BlkG var_of tbl (block G P e) (inst var_of G P e)) /\
     (NonLet e -> Den_math var_of tbl (block G P e) (inst var_of G P e)) /\
     (NonLet e -> bin_end e = false ->
        Den_chain var_of tbl (block G P e) (inst var_of G P e))) /\
  (forall fs,
     (forall G P, GOK G P -> scoped_fields G P fs -> LabelsOK tbl (lbls_fields G P fs) ->
        Den_items var_of tbl (field_trees G P fs ++ [sym "}"]) (inst_fields var_of G 0 P fs) /\
        Den_sep var_of tbl (more_field_trees G P fs ++ [sym "}"]) (inst_fields var_of G 0 P fs)) /\
     (forall G P i, GOK G (S P) -> scoped_group G (S P) i fs ->
        LabelsOK tbl (lbls_members G P fs) ->
        forall rest xs gs b, (forall fin, Den_blk var_of tbl [] fin rest xs gs b) ->
          forall fin, Den_blk var_of tbl [] fin (member_trees G P i fs ++ rest)
            (gnames P i (flen fs) ++ xs)
            (List.map (inst var_of G (S P)) (fvals fs) ++ gs) b)) /\
  (forall ars : arms, True).
Proof.
  intros var_of tbl Hdist.
  apply exp_fields_mutind.
  - (* bound index *)
    intros i G P HG Hs Hl.
    assert (Hchain : Den_chain var_of tbl (block G P (e_fvar_b i)) (inst var_of G P (e_fvar_b i))).
    { rewrite inst_bvar. apply den_chain_single. apply D_name. reflexivity. }
    apply den_pack; exact Hchain.
  - intros y G P HG Hs. destruct Hs.
  - intros n G P HG Hs Hl.
    assert (Hn : Den var_of tbl (Node R_number [Leaf (TNum (nat_of_z n))]) (e_num n)).
    { rewrite <- (z_of_nat_of_z n Hs) at 2. apply D_num. }
    assert (Hchain : Den_chain var_of tbl (block G P (e_num n)) (e_num n))
      by (apply den_chain_single; exact Hn).
    apply den_pack; exact Hchain.
  - intros d G P HG Hs Hl.
    assert (Hchain : Den_chain var_of tbl (block G P (e_dec d)) (e_dec d))
      by (apply den_chain_single; apply D_dec).
    apply den_pack; exact Hchain.
  - intros G P HG Hs Hl.
    assert (Hchain : Den_chain var_of tbl (block G P e_true) e_true)
      by (apply den_chain_single; apply D_true).
    apply den_pack; exact Hchain.
  - intros G P HG Hs Hl.
    assert (Hchain : Den_chain var_of tbl (block G P e_false) e_false)
      by (apply den_chain_single; apply D_false).
    apply den_pack; exact Hchain.
  - (* program *)
    intros b IH G P HG Hs Hl.
    destruct (block_abs_cases G P b) as [(-> & E) | (Hne & E)]; rewrite E.
    { assert (Hfun : Den var_of tbl (function_empty_tree P)
                       (curry [var_of (nm P)] e_unit)).
      { unfold function_empty_tree. eapply D_function_empty with (xs := [nm P]).
        apply DPa_one. }
      assert (Hcurry : curry [var_of (nm P)] e_unit = inst var_of G P (e_abs e_unit))
        by reflexivity.
      rewrite Hcurry in Hfun.
      assert (Hchain : Den_chain var_of tbl [function_empty_tree P]
                         (inst var_of G P (e_abs e_unit)))
        by (apply den_chain_single; exact Hfun).
      rewrite <- E. apply den_pack. rewrite E. exact Hchain. }
    destruct Hs as [Hs | Hs]; [ exfalso; exact (Hne Hs) | ].
    destruct (IH G (S P) (gok_S G P HG) Hs Hl) as [Hef _].
    assert (Hfun : Den var_of tbl (function_tree P (block G (S P) b))
                     (curry [var_of (nm P)] (inst var_of G (S P) b))).
    { unfold function_tree. eapply D_function with (xs := [nm P]).
      - apply DPa_one.
      - exact Hef. }
    assert (Hcurry : curry [var_of (nm P)] (inst var_of G (S P) b)
                     = inst var_of G P (e_abs b)).
    { rewrite curry_one, inst_abs. unfold inst.
      rewrite (close_inst_exp var_of G P b Hdist (gok_none G P HG) Hs). reflexivity. }
    rewrite Hcurry in Hfun.
    assert (Hchain : Den_chain var_of tbl [function_tree P (block G (S P) b)]
                       (inst var_of G P (e_abs b)))
      by (apply den_chain_single; exact Hfun).
    rewrite <- E. apply den_pack. rewrite E. exact Hchain.
  - (* call *)
    intros f IHf a IHa G P HG [Hf Ha] Hl.
    destruct (IHf G P HG Hf (labelsok_app_l _ _ _ Hl)) as [Hef [_ [_ Hcf]]].
    assert (Hop : Den_chain var_of tbl (as_callee f (block G P f)) (inst var_of G P f)).
    { destruct f; cbn [as_callee as_operand];
        first [ apply den_chain_paren; exact Hef | exact (Hcf I eq_refl) ]. }
    destruct (block_app_cases G P f a) as [(-> & E) | (Hne & E)]; rewrite E.
    { assert (Hchain : Den_chain var_of tbl (as_callee f (block G P f) ++ [call_unit_tree])
                         (inst var_of G P (e_app f e_unit)))
        by exact (den_chain_call_unit var_of tbl _ _ Hop (callee_not_access G P f)).
      rewrite <- E. apply den_pack. rewrite E. exact Hchain. }
    destruct Ha as [Ha | Ha]; [ exfalso; exact (Hne Ha) | ].
    destruct (IHa G P HG Ha (labelsok_app_r _ _ _ Hl)) as [Hea _].
    assert (Hchain : Den_chain var_of tbl (as_callee f (block G P f) ++ [call_tree (block G P a)])
                       (inst var_of G P (e_app f a))).
    { exact (den_chain_call var_of tbl _ _ _ _ Hop Hea (callee_not_access G P f)). }
    rewrite <- E. apply den_pack. rewrite E. exact Hchain.
  - (* binding *)
    intros v IHv b IHb G P HG (Hv & Hb & Hnr) Hl.
    destruct (IHv G P HG Hv (labelsok_app_l _ _ _ Hl)) as [Hev [_ [Hmv _]]].
    destruct (IHb G (S P) (gok_S G P HG) Hb (labelsok_app_r _ _ _ Hl)) as [_ [Hbb _]].
    assert (Hval : Den_math var_of tbl (as_value v (block G P v)) (inst var_of G P v)).
    { destruct v; cbn [as_value];
        first [ (apply DM_chain; apply den_chain_paren; exact Hev) | exact (Hmv I) ]. }
    assert (Hdecl : Den_decl var_of tbl
                      (decl_tree P (as_value v (block G P v))) (nm P) (inst var_of G P v)).
    { apply DD_semi. apply D_value. exact Hval. }
    assert (Hlet : inst var_of G P (e_let v b)
                   = e_let (inst var_of G P v)
                           (close_exp (var_of (nm P)) (inst var_of G (S P) b))).
    { unfold inst. cbn [inst_rec].
      rewrite (close_inst_exp var_of G P b Hdist (gok_none G P HG) Hb). reflexivity. }
    assert (Hblk : BlkG var_of tbl (block G P (e_let v b)) (inst var_of G P (e_let v b))).
    { rewrite Hlet. cbn [block]. intros ctx fin.
      eapply DK_value; [ exact Hdecl | apply value_not_fn | exact (Hbb Hnr _ _) ]. }
    refine (conj (D_expr_g _ _ _ _ Hblk) (conj (fun _ => Hblk) (conj _ _)));
      intros Hn; destruct Hn.
  - (* recursive group *)
    intros fs [IHfs IHmem] b IHb G P HG (Hlen & Hgrp & Hb & Hnr) Hl.
    assert (HG' : GOK ((P, flen fs) :: G) (S P)) by exact (gok_cons G P _ HG).
    assert (Hl' : LabelsOK tbl (lbls_members ((P, flen fs) :: G) P fs
                                ++ lbls ((P, flen fs) :: G) (S P) b)) by exact Hl.
    destruct (IHb _ (S P) HG' Hb (labelsok_app_r _ _ _ Hl')) as [_ [Hbb _]].
    pose proof (IHmem ((P, flen fs) :: G) P 0 HG' Hgrp (labelsok_app_l _ _ _ Hl')
                  (block ((P, flen fs) :: G) (S P) b) [] [] (inst var_of ((P, flen fs) :: G) (S P) b)
                  (fun fin => Hbb Hnr [] fin) e_unit) as Hmem.
    rewrite !app_nil_r in Hmem.
    assert (Hden : Den var_of tbl (Node R_expr (block G P (e_letrec fs b)))
                     (inst var_of G P (e_letrec fs b))).
    { assert (Hw : inst var_of G P (e_letrec fs b)
                   = wrap_group (List.map var_of (gnames P 0 (flen fs)))
                                (List.map (inst_rec var_of ((P, flen fs) :: G) 0 (S P)) (fvals fs))
                                (inst_rec var_of ((P, flen fs) :: G) 0 (S P) b)).
      { symmetry. exact (den_wrap var_of Hdist P (flen fs) ((P, flen fs) :: G) fs b
                           Hlen (grp_size_here P _ G) Hgrp Hb). }
      rewrite Hw.
      exact (D_expr var_of tbl _ _ (DB_top var_of tbl _ _ _ _ Hmem)). }
    refine (conj Hden (conj _ (conj _ _))); intros Hn; destruct Hn.
  - (* record *)
    intros fs [IH _] G P HG Hs Hl.
    destruct (IH G P HG Hs Hl) as [Hitems _].
    assert (Hrec : Den var_of tbl
                     (Node R_record ((sym "{" :: field_trees G P fs) ++ [sym "}"]))
                     (e_rec (inst_fields var_of G 0 P fs))).
    { apply D_record. exact Hitems. }
    assert (Hchain : Den_chain var_of tbl (block G P (e_rec fs)) (inst var_of G P (e_rec fs)))
      by (apply den_chain_single; exact Hrec).
    apply den_pack; exact Hchain.
  - (* projection *)
    intros f IHf l G P HG Hs Hl.
    destruct (proj_level G P f) eqn:EL.
    + destruct (proj_level_some G P f n EL) as (i & m & -> & HL & Hm).
      rewrite HL in Hm.
      assert (Hchain : Den_chain var_of tbl (block G P (e_proj (e_fvar_b i) l))
                         (inst var_of G P (e_proj (e_fvar_b i) l))).
      { rewrite (block_proj_group G P _ l n EL), (inst_proj_group var_of G P i l m Hm).
        rewrite HL. apply den_chain_single. apply D_name. reflexivity. }
      apply den_pack; exact Hchain.
    + assert (Hf : scoped G P f) by exact (proj_plain G P f l Hs EL).
      rewrite (lbls_proj_plain G P f l EL) in Hl.
      destruct (IHf G P HG Hf (labelsok_app_l _ _ _ Hl)) as [Hef [_ [_ Hcf]]].
      assert (Hop : Den_chain var_of tbl (as_operand f (block G P f)) (inst var_of G P f)).
      { destruct f; cbn [as_operand];
          first [ apply den_chain_paren; exact Hef | exact (Hcf I eq_refl) ]. }
      assert (Hchain : Den_chain var_of tbl (block G P (e_proj f l))
                         (inst var_of G P (e_proj f l))).
      { rewrite (block_proj_plain G P f l EL), (inst_proj_plain var_of G P f l EL).
        exact (den_chain_access var_of tbl _ _ _ Hop (labelsok_app_r _ _ _ Hl)). }
      apply den_pack; exact Hchain.
  - (* unit *)
    intros G P HG Hs. destruct Hs.
  - (* string *)
    intros q G P HG Hs Hl.
    assert (Hchain : Den_chain var_of tbl (block G P (e_str q)) (e_str q))
      by (apply den_chain_single; apply D_str).
    apply den_pack; exact Hchain.
  - (* conditional *)
    intros c IHc a IHa b IHb G P HG [Hc [Ha Hb]] Hl.
    destruct (IHc G P HG Hc (labelsok_app_l _ _ _ Hl)) as [Hec _].
    destruct (IHa G P HG Ha (labelsok_app_l _ _ _ (labelsok_app_r _ _ _ Hl))) as [Hea _].
    destruct (block_ite_cases G P c a b) as [(-> & E) | (Hne & E)]; rewrite E.
    + assert (Hcond : Den var_of tbl (cond_tree_noelse (block G P c) (block G P a))
                        (e_ite (inst var_of G P c) (inst var_of G P a) e_unit)).
      { unfold cond_tree_noelse. apply D_cond_noelse; assumption. }
      assert (Hchain : Den_chain var_of tbl [cond_tree_noelse (block G P c) (block G P a)]
                         (e_ite (inst var_of G P c) (inst var_of G P a) e_unit))
        by (apply den_chain_single; exact Hcond).
      rewrite <- E.
      apply den_pack. rewrite E. exact Hchain.
    + destruct Hb as [Hb | Hb]; [ exfalso; exact (Hne Hb) | ].
      destruct (IHb G P HG Hb (labelsok_app_r _ _ _ (labelsok_app_r _ _ _ Hl))) as [Heb _].
      assert (Hcond : Den var_of tbl (cond_tree (block G P c) (block G P a) (block G P b))
                        (e_ite (inst var_of G P c) (inst var_of G P a) (inst var_of G P b))).
      { unfold cond_tree. apply D_cond; assumption. }
      assert (Hchain : Den_chain var_of tbl [cond_tree (block G P c) (block G P a) (block G P b)]
                         (e_ite (inst var_of G P c) (inst var_of G P a) (inst var_of G P b)))
        by (apply den_chain_single; exact Hcond).
      rewrite <- E.
      apply den_pack. rewrite E. exact Hchain.
  - (* operation *)
    intros a IHa o b IHb G P HG [Ha Hb] Hl.
    destruct (IHa G P HG Ha (labelsok_app_l _ _ _ Hl)) as [Hea [_ [_ Hca]]].
    destruct (IHb G P HG Hb (labelsok_app_r _ _ _ Hl)) as [Heb [_ [_ Hcb]]].
    assert (H1 : Den_chain var_of tbl (as_binop a (block G P a)) (inst var_of G P a)).
    { destruct a; cbn [as_binop];
        first [ apply den_chain_paren; exact Hea | exact (Hca I eq_refl) ]. }
    assert (H2 : Den_chain var_of tbl (as_binop b (block G P b)) (inst var_of G P b)).
    { destruct b; cbn [as_binop];
        first [ apply den_chain_paren; exact Heb | exact (Hcb I eq_refl) ]. }
    assert (Hmath : Den_math var_of tbl (block G P (e_bin a o b))
                      (inst var_of G P (e_bin a o b))).
    { cbn [block]. exact (DM_bin var_of tbl _ _ o _ _ H1 H2). }
    assert (Hblk : BlkG var_of tbl (block G P (e_bin a o b)) (inst var_of G P (e_bin a o b)))
      by (intros ctx fin; apply DK_chain; exact Hmath).
    refine (conj (D_expr_g _ _ _ _ Hblk) (conj (fun _ => Hblk) (conj (fun _ => Hmath) _))).
    intros _ Hx. discriminate Hx.
  - (* coercion: not a term of the printed fragment *)
    intros a IH G P HG Hs. destruct Hs.
  - intros w tg a IH G P HG Hs. destruct Hs.
  - intros w a IHa ars IHars G P HG Hs. destruct Hs.
  - (* spread *)
    intros a IHa l b IHb G P HG [Ha Hb] Hl.
    assert (Hl' : LabelsOK tbl (lbls G P a ++ l :: lbls G P b)) by exact Hl.
    assert (Hla : LabelsOK tbl (lbls G P a)) by exact (labelsok_app_l _ _ _ Hl').
    assert (Hlrest : LabelsOK tbl (l :: lbls G P b)) by exact (labelsok_app_r _ _ _ Hl').
    assert (Hll : LabelsOK tbl [l]).
    { intros n Hn. apply Hlrest. destruct Hn as [<- | []]. left. reflexivity. }
    assert (Hlb : LabelsOK tbl (lbls G P b)).
    { intros n Hn. apply Hlrest. right. exact Hn. }
    destruct (IHa G P HG Ha Hla) as [Hea _].
    destruct (IHb G P HG Hb Hlb) as [Heb _].
    assert (Hbasep : Den var_of tbl (Node R_expr (paren_kids (block G P a))) (inst var_of G P a)).
    { apply D_expr_g. intros ctx fin. apply DK_chain. apply DM_chain.
      apply den_chain_paren. exact Hea. }
    assert (Hfield : Den_field var_of tbl (field_tree l (block G P b)) (lname l)
                       (inst var_of G P b)).
    { unfold field_tree. apply DF. exact Heb. }
    assert (Hsep : Den_sep var_of tbl [sym ","; field_tree l (block G P b); sym "}"]
                     (fs_cons (lab tbl (lname l)) (inst var_of G P b) fs_nil)).
    { apply DS_more. exact (DI_field var_of tbl _ _ _ _ _ Hfield (DS_end var_of tbl)). }
    assert (Hrec : Den var_of tbl (Node R_record [sym "{"; spread_tree (block G P a); sym ",";
                                                  field_tree l (block G P b); sym "}"])
                     (e_spread (inst var_of G P a) l (inst var_of G P b))).
    { rewrite <- (lab_lname tbl l Hll) at 2.
      exact (D_spread_record var_of tbl _ _ _ _ Hbasep Hsep). }
    assert (Hchain : Den_chain var_of tbl (block G P (e_spread a l b))
                       (inst var_of G P (e_spread a l b)))
      by (apply den_chain_single; exact Hrec).
    apply den_pack; exact Hchain.
  - intros a IH l G P HG Hs. destruct Hs.
  - intros a IH G P HG Hs Hl. destruct Hs.
  - intros a IH G P HG Hs Hl. destruct Hs.
  - (* no fields *)
    split.
    + intros G P HG Hs Hl. split.
      * apply DI_end.
      * apply DS_end.
    + intros G P i HG Hs Hl rest xs gs b Hrest fin. exact (Hrest fin).
  - (* a field, then the rest *)
    intros l e IHe rest [IHrest IHmem]. split.
    + intros G P HG [He Hrest] Hl.
      assert (Hl' : LabelsOK tbl (l :: lbls G P e ++ lbls_fields G P rest)) by exact Hl.
      assert (Hll : LabelsOK tbl [l]).
      { intros n Hn. apply Hl'. destruct Hn as [<- | []]. left. reflexivity. }
      assert (Hle : LabelsOK tbl (lbls G P e)).
      { intros n Hn. apply Hl'. right. apply in_or_app. left. exact Hn. }
      assert (Hlrest : LabelsOK tbl (lbls_fields G P rest)).
      { intros n Hn. apply Hl'. right. apply in_or_app. right. exact Hn. }
      destruct (IHe G P HG He Hle) as [Hee _].
      destruct (IHrest G P HG Hrest Hlrest) as [Hitems Hsep].
      assert (Hfield : Den_field var_of tbl (field_tree l (block G P e)) (lname l)
                         (inst var_of G P e)).
      { unfold field_tree. apply DF. exact Hee. }
      assert (Hitems' : Den_items var_of tbl
                          (field_trees G P (fs_cons l e rest) ++ [sym "}"])
                          (inst_fields var_of G 0 P (fs_cons l e rest))).
      { cbn [field_trees inst_fields].
        pose proof (DI_field var_of tbl _ _ _ _ _ Hfield Hsep) as Hcons.
        rewrite (lab_lname tbl l Hll) in Hcons. exact Hcons. }
      split; [ exact Hitems' | ].
      cbn [more_field_trees]. simpl. apply DS_more.
      exact Hitems'.
    + intros G P i HG (Hli & Hab & Hv & Hrest) Hl rest0 xs gs b Hr fin.
      assert (Hl' : LabelsOK tbl (lbls G (S P) e ++ lbls_members G P rest)) by exact Hl.
      destruct (IHe G (S P) HG Hv (labelsok_app_l _ _ _ Hl')) as [_ [_ [Hmv _]]].
      assert (Hm : Den_math var_of tbl (block G (S P) e) (inst var_of G (S P) e))
        by exact (Hmv (is_abs_nonlet e Hab)).
      assert (Hdecl : Den_decl var_of tbl (decl_named (gm P i) (block G (S P) e)) (gm P i)
                        (inst var_of G (S P) e)).
      { apply DD_semi. apply D_value. exact Hm. }
      cbn [member_trees flen gnames fvals List.map app].
      eapply DK_hoist;
        [ exact Hdecl | exact (is_fn_decl_abs _ _ _ _ Hab) | reflexivity | ].
      exact (IHmem G P (S i) HG Hrest (labelsok_app_r _ _ _ Hl') rest0 xs gs b Hr _).
  - (* a method field is not a term of the printed fragment *)
    intros l e IHe rest IHrest. split; [ intros G P HG Hs | intros G P i HG Hs ]; destruct Hs.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
Qed.
