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
Open Scope string_scope.
Open Scope list_scope.

(* ---- the bound indices read as the names the printer gave them ---- *)

Fixpoint inst_rec (var_of : string -> termvar) (k D : nat) (e : exp) {struct e} : exp :=
  match e with
  | e_fvar_b i =>
      if Nat.ltb i k then e_fvar_b i else e_fvar_f (var_of (nm (D + k - 1 - i)))
  | e_fvar_f y => e_fvar_f y
  | e_num n => e_num n
  | e_dec d => e_dec d
  | e_true => e_true
  | e_false => e_false
  | e_abs b => e_abs (inst_rec var_of (S k) D b)
  | e_app a b => e_app (inst_rec var_of k D a) (inst_rec var_of k D b)
  | e_let a b => e_let (inst_rec var_of k D a) (inst_rec var_of (S k) D b)
  | e_rec fs => e_rec (inst_fields var_of k D fs)
  | e_proj a l => e_proj (inst_rec var_of k D a) l
  | e_unit => e_unit
  | e_str q => e_str q
  | e_ite a b c => e_ite (inst_rec var_of k D a) (inst_rec var_of k D b) (inst_rec var_of k D c)
  | e_bin a o b => e_bin (inst_rec var_of k D a) o (inst_rec var_of k D b)
  | e_tofloat a => e_tofloat (inst_rec var_of k D a)
  end
with inst_fields (var_of : string -> termvar) (k D : nat) (fs : Goat_ott.fields) {struct fs}
  : Goat_ott.fields :=
  match fs with
  | fs_nil => fs_nil
  | fs_cons l e rest => fs_cons l (inst_rec var_of k D e) (inst_fields var_of k D rest)
  end.

Definition inst (var_of : string -> termvar) (D : nat) (e : exp) : exp :=
  inst_rec var_of 0 D e.

Lemma inst_bvar : forall var_of D i,
  inst var_of D (e_fvar_b i) = e_fvar_f (var_of (nm (D - 1 - i))).
Proof. intros var_of D i. unfold inst. simpl. rewrite Nat.add_0_r. reflexivity. Qed.

(* Closing the variable that stands for the innermost of [S D] binders turns it
   back into the bound index [k], and the other variables are unchanged. *)
Lemma close_inst : forall var_of, names_distinct var_of -> forall D,
  (forall e k, scoped (k + S D) e ->
     close_exp_rec k (var_of (nm D)) (inst_rec var_of k (S D) e)
     = inst_rec var_of (S k) D e) /\
  (forall fs k, scoped_fields (k + S D) fs ->
     close_fields_rec k (var_of (nm D)) (inst_fields var_of k (S D) fs)
     = inst_fields var_of (S k) D fs).
Proof.
  intros var_of Hdist D.
  apply exp_fields_mutind.
  - (* bound index *)
    intros i k Hs. simpl in Hs.
    cbn [inst_rec]. destruct (Nat.ltb i k) eqn:Hik.
    + assert (Hlt : i < k) by (apply Nat.ltb_lt; exact Hik).
      assert (Hlt' : Nat.ltb i (S k) = true) by (apply Nat.ltb_lt; lia).
      cbn [close_exp_rec inst_rec]. rewrite Hlt'. reflexivity.
    + assert (Hge : k <= i) by (apply Nat.ltb_ge; exact Hik).
      cbn [close_exp_rec inst_rec].
      destruct (var_of (nm (S D + k - 1 - i)) == var_of (nm D)) as [Heq | Hne].
      * assert (Hnm : S D + k - 1 - i = D) by (apply Hdist; exact Heq).
        assert (Hik' : i = k) by lia.
        subst i. assert (Hlt' : Nat.ltb k (S k) = true) by (apply Nat.ltb_lt; lia).
        rewrite Hlt'. reflexivity.
      * destruct (Nat.ltb i (S k)) eqn:Hlt'.
        { exfalso. apply Nat.ltb_lt in Hlt'.
          assert (Hik' : i = k) by lia. subst i.
          apply Hne. replace (S D + k - 1 - k) with D by lia. reflexivity. }
        replace (D + S k - 1 - i) with (S D + k - 1 - i) by lia.
        reflexivity.
  - intros y k Hs. destruct Hs.
  - intros n k Hs. reflexivity.
  - intros d k Hs. reflexivity.
  - intros k Hs. reflexivity.
  - intros k Hs. reflexivity.
  - (* abs *)
    intros b IH k Hs. simpl in Hs. simpl.
    rewrite (IH (S k) Hs). reflexivity.
  - (* app *)
    intros a IHa b IHb k [Ha Hb]. simpl.
    rewrite (IHa k Ha), (IHb k Hb). reflexivity.
  - (* let *)
    intros a IHa b IHb k [Ha Hb]. simpl.
    rewrite (IHa k Ha), (IHb (S k) Hb). reflexivity.
  - (* record *)
    intros fs IH k Hs. simpl in *. rewrite (IH k Hs). reflexivity.
  - (* projection *)
    intros a IH l k Hs. simpl in *. rewrite (IH k Hs). reflexivity.
  - intros k Hs. destruct Hs.
  - intros q k Hs. reflexivity.
  - (* conditional *)
    intros a IHa b IHb c IHc k [Ha [Hb Hc]]. simpl.
    rewrite (IHa k Ha), (IHb k Hb), (IHc k Hc). reflexivity.
  - (* operation *)
    intros a IHa o b IHb k [Ha Hb]. simpl.
    rewrite (IHa k Ha), (IHb k Hb). reflexivity.
  - (* coercion: not a term of the printed fragment *)
    intros a IH k Hs. destruct Hs.
  - intros k Hs. reflexivity.
  - intros l e IHe fs IHfs k [He Hfs]. simpl.
    rewrite (IHe k He), (IHfs k Hfs). reflexivity.
Qed.

Lemma close_inst_exp : forall var_of D b,
  names_distinct var_of -> scoped (S D) b ->
  close_exp (var_of (nm D)) (inst var_of (S D) b) = inst_rec var_of 1 D b.
Proof.
  intros var_of D b Hdist Hs. unfold close_exp, inst.
  exact (proj1 (close_inst var_of Hdist D) b 0 Hs).
Qed.

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
  - (* dot call *)
    simpl. eapply DP_dot_call; [ eassumption | ].
    apply IHDen_posts; [ exact Hp | ].
    intros Hstarts Hend. exact (Hcall Hstarts (ends_cons _ _ (ends_cons _ _ Hend))).
  - (* call *)
    simpl. eapply DP_call; [ eassumption | ].
    apply IHDen_posts; [ exact Hp | ].
    intros Hstarts Hend. exact (Hcall Hstarts (ends_cons _ _ Hend)).
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
Lemma callee_not_access : forall P f, ~ ends_in_access (as_callee f (block P f)).
Proof.
  intros P f. destruct f; cbn [as_callee as_operand block paren_kids];
    first
    [ (intros [init [c H]]; destruct init; discriminate H)
    | (apply (ends_access_last [sym "("; Node R_expr _]); intros c Hc; discriminate Hc)
    | (apply (ends_access_last []); intros c Hc; discriminate Hc)
    | (apply ends_access_last; intros c Hc; discriminate Hc) ].
Qed.

Lemma den_pack : forall var_of tbl P e x,
  Den_chain var_of tbl (block P e) x ->
  Den_block var_of tbl (block P e) x /\
  (NonLet e -> Den_math var_of tbl (block P e) x) /\
  (NonLet e -> bin_end e = false -> Den_chain var_of tbl (block P e) x).
Proof.
  intros var_of tbl P e x H. repeat split.
  - apply DB_chain. apply DM_chain. exact H.
  - intros _. apply DM_chain. exact H.
  - intros _ _. exact H.
Qed.

Lemma den_chain_single : forall var_of tbl t e,
  Den var_of tbl t e -> Den_chain var_of tbl [t] e.
Proof. intros var_of tbl t e H. eapply DC_head; [ exact H | apply DP_nil ]. Qed.

Lemma den_chain_paren : forall var_of tbl b e,
  Den_block var_of tbl b e -> Den_chain var_of tbl (paren_kids b) e.
Proof.
  intros var_of tbl b e H. unfold paren_kids.
  eapply DC_paren; [ apply D_expr; exact H | apply DP_nil ].
Qed.

(* ---- the main lemma ---- *)

Lemma print_den : forall var_of tbl, names_distinct var_of ->
  (forall e P, scoped P e -> LabelsOK tbl (lbls e) ->
     Den_block var_of tbl (block P e) (inst var_of P e) /\
     (NonLet e -> Den_math var_of tbl (block P e) (inst var_of P e)) /\
     (NonLet e -> bin_end e = false -> Den_chain var_of tbl (block P e) (inst var_of P e))) /\
  (forall fs P, scoped_fields P fs -> LabelsOK tbl (lbls_fields fs) ->
     Den_items var_of tbl (field_trees P fs ++ [sym "}"]) (inst_fields var_of 0 P fs) /\
     Den_sep var_of tbl (more_field_trees P fs ++ [sym "}"]) (inst_fields var_of 0 P fs)).
Proof.
  intros var_of tbl Hdist.
  apply exp_fields_mutind.
  - (* bound index *)
    intros i P Hs Hl.
    assert (Hchain : Den_chain var_of tbl (block P (e_fvar_b i)) (inst var_of P (e_fvar_b i))).
    { rewrite inst_bvar. apply den_chain_single. apply D_name. }
    apply den_pack; exact Hchain.
  - intros y P Hs. destruct Hs.
  - intros n P Hs Hl.
    assert (Hn : Den var_of tbl (Node R_number [Leaf (TNum (nat_of_z n))]) (e_num n)).
    { rewrite <- (z_of_nat_of_z n Hs) at 2. apply D_num. }
    assert (Hchain : Den_chain var_of tbl (block P (e_num n)) (e_num n))
      by (apply den_chain_single; exact Hn).
    apply den_pack; exact Hchain.
  - intros d P Hs. destruct Hs.
  - intros P Hs Hl.
    assert (Hchain : Den_chain var_of tbl (block P e_true) e_true)
      by (apply den_chain_single; apply D_true).
    apply den_pack; exact Hchain.
  - intros P Hs Hl.
    assert (Hchain : Den_chain var_of tbl (block P e_false) e_false)
      by (apply den_chain_single; apply D_false).
    apply den_pack; exact Hchain.
  - (* program *)
    intros b IH P Hs Hl.
    destruct (IH (S P) Hs Hl) as [Hblock _].
    assert (Hfun : Den var_of tbl (function_tree P (block (S P) b))
                     (curry [var_of (nm P)] (inst var_of (S P) b))).
    { unfold function_tree. eapply D_function with (xs := [nm P]).
      - apply DPa_one.
      - apply D_expr. exact Hblock. }
    assert (Hcurry : curry [var_of (nm P)] (inst var_of (S P) b)
                     = inst var_of P (e_abs b)).
    { simpl. rewrite (close_inst_exp var_of P b Hdist Hs). reflexivity. }
    rewrite Hcurry in Hfun.
    assert (Hchain : Den_chain var_of tbl (block P (e_abs b)) (inst var_of P (e_abs b)))
      by (apply den_chain_single; exact Hfun).
    apply den_pack; exact Hchain.
  - (* call *)
    intros f IHf a IHa P [Hf Ha] Hl.
    destruct (IHf P Hf (labelsok_app_l _ _ _ Hl)) as [Hbf [_ Hcf]].
    destruct (IHa P Ha (labelsok_app_r _ _ _ Hl)) as [Hba _].
    assert (Hop : Den_chain var_of tbl (as_callee f (block P f)) (inst var_of P f)).
    { destruct f; cbn [as_callee as_operand];
        first [ apply den_chain_paren; exact Hbf | exact (Hcf I eq_refl) ]. }
    assert (Hchain : Den_chain var_of tbl (block P (e_app f a)) (inst var_of P (e_app f a))).
    { exact (den_chain_call var_of tbl _ _ _ _ Hop (D_expr _ _ _ _ Hba)
               (callee_not_access P f)). }
    apply den_pack; exact Hchain.
  - (* binding *)
    intros v IHv b IHb P [Hv Hb] Hl.
    destruct (IHv P Hv (labelsok_app_l _ _ _ Hl)) as [Hbv [Hmv _]].
    destruct (IHb (S P) Hb (labelsok_app_r _ _ _ Hl)) as [Hbb _].
    assert (Hval : Den_math var_of tbl (as_value v (block P v)) (inst var_of P v)).
    { destruct v; cbn [as_value];
        first [ (apply DM_chain; apply den_chain_paren; exact Hbv) | exact (Hmv I) ]. }
    assert (Hdecl : Den_decl var_of tbl
                      (decl_tree P (as_value v (block P v))) (nm P) (inst var_of P v)).
    { apply DD_semi. apply D_value. exact Hval. }
    split; [ | split; intros Hn; destruct Hn ].
    assert (Hlet : inst var_of P (e_let v b)
                   = e_let (inst var_of P v) (close_exp (var_of (nm P)) (inst var_of (S P) b))).
    { unfold inst at 1. simpl. rewrite (close_inst_exp var_of P b Hdist Hb). reflexivity. }
    rewrite Hlet. cbn [block].
    eapply DB_decl; [ exact Hdecl | exact Hbb ].
  - (* record *)
    intros fs IH P Hs Hl.
    destruct (IH P Hs Hl) as [Hitems _].
    assert (Hrec : Den var_of tbl
                     (Node R_record ((sym "{" :: field_trees P fs) ++ [sym "}"]))
                     (e_rec (inst_fields var_of 0 P fs))).
    { apply D_record. exact Hitems. }
    assert (Hchain : Den_chain var_of tbl (block P (e_rec fs)) (inst var_of P (e_rec fs)))
      by (apply den_chain_single; exact Hrec).
    apply den_pack; exact Hchain.
  - (* projection *)
    intros f IH l P Hf Hl.
    destruct (IH P Hf (labelsok_app_l _ _ _ Hl)) as [Hbf [_ Hcf]].
    assert (Hop : Den_chain var_of tbl (as_operand f (block P f)) (inst var_of P f)).
    { destruct f; cbn [as_operand];
        first [ apply den_chain_paren; exact Hbf | exact (Hcf I eq_refl) ]. }
    assert (Hchain : Den_chain var_of tbl (block P (e_proj f l)) (inst var_of P (e_proj f l)))
      by exact (den_chain_access var_of tbl _ _ _ Hop (labelsok_app_r _ _ _ Hl)).
    apply den_pack; exact Hchain.
  - (* unit: not a term of the printed fragment *)
    intros P Hs. destruct Hs.
  - (* string *)
    intros q P Hs Hl.
    assert (Hchain : Den_chain var_of tbl (block P (e_str q)) (e_str q))
      by (apply den_chain_single; apply D_str).
    apply den_pack; exact Hchain.
  - (* conditional *)
    intros c IHc a IHa b IHb P [Hc [Ha Hb]] Hl.
    destruct (IHc P Hc (labelsok_app_l _ _ _ Hl)) as [Hbc _].
    destruct (IHa P Ha (labelsok_app_l _ _ _ (labelsok_app_r _ _ _ Hl))) as [Hba _].
    destruct (IHb P Hb (labelsok_app_r _ _ _ (labelsok_app_r _ _ _ Hl))) as [Hbb _].
    assert (Hcond : Den var_of tbl (cond_tree (block P c) (block P a) (block P b))
                      (e_ite (inst var_of P c) (inst var_of P a) (inst var_of P b))).
    { unfold cond_tree. apply D_cond; apply D_expr; assumption. }
    assert (Hchain : Den_chain var_of tbl (block P (e_ite c a b)) (inst var_of P (e_ite c a b)))
      by (apply den_chain_single; exact Hcond).
    apply den_pack; exact Hchain.
  - (* operation *)
    intros a IHa o b IHb P [Ha Hb] Hl.
    destruct (IHa P Ha (labelsok_app_l _ _ _ Hl)) as [Hba [_ Hca]].
    destruct (IHb P Hb (labelsok_app_r _ _ _ Hl)) as [Hbb [_ Hcb]].
    assert (H1 : Den_chain var_of tbl (as_binop a (block P a)) (inst var_of P a)).
    { destruct a; cbn [as_binop];
        first [ apply den_chain_paren; exact Hba | exact (Hca I eq_refl) ]. }
    assert (H2 : Den_chain var_of tbl (as_binop b (block P b)) (inst var_of P b)).
    { destruct b; cbn [as_binop];
        first [ apply den_chain_paren; exact Hbb | exact (Hcb I eq_refl) ]. }
    assert (Hmath : Den_math var_of tbl (block P (e_bin a o b)) (inst var_of P (e_bin a o b))).
    { cbn [block]. exact (DM_bin var_of tbl _ _ o _ _ H1 H2). }
    split; [ apply DB_chain; exact Hmath
           | split; [ intros _; exact Hmath | intros _ Hx; discriminate Hx ] ].
  - (* coercion: not a term of the printed fragment *)
    intros a IH P Hs Hl. destruct Hs.
  - (* no fields *)
    intros P Hs Hl. split.
    + apply DI_end.
    + apply DS_end.
  - (* a field, then the rest *)
    intros l e IHe rest IHrest P [He Hrest] Hl.
    assert (Hl' : LabelsOK tbl (l :: lbls e ++ lbls_fields rest)) by exact Hl.
    assert (Hll : LabelsOK tbl [l]).
    { intros n Hn. apply Hl'. destruct Hn as [<- | []]. left. reflexivity. }
    assert (Hle : LabelsOK tbl (lbls e)).
    { intros n Hn. apply Hl'. right. apply in_or_app. left. exact Hn. }
    assert (Hlrest : LabelsOK tbl (lbls_fields rest)).
    { intros n Hn. apply Hl'. right. apply in_or_app. right. exact Hn. }
    destruct (IHe P He Hle) as [Hbe _].
    destruct (IHrest P Hrest Hlrest) as [Hitems Hsep].
    assert (Hfield : Den_field var_of tbl (field_tree l (block P e)) (lname l) (inst var_of P e)).
    { unfold field_tree. apply DF. apply D_expr. exact Hbe. }
    assert (Hitems' : Den_items var_of tbl
                        (field_trees P (fs_cons l e rest) ++ [sym "}"])
                        (inst_fields var_of 0 P (fs_cons l e rest))).
    { cbn [field_trees inst_fields].
      pose proof (DI_field var_of tbl _ _ _ _ _ Hfield Hsep) as Hcons.
      rewrite (lab_lname tbl l Hll) in Hcons. exact Hcons. }
    split; [ exact Hitems' | ].
    cbn [more_field_trees]. simpl. apply DS_more.
    exact Hitems'.
Qed.
