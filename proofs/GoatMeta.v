(* Metatheory for core goat: the metatheory lemmas of docs/semantics.md
   section 7 (L1-L7), and the Progress, Preservation and Soundness theorems of
   that document, over the hand-written type system of GoatDefs.v and the row
   theory of GoatRows.v.

   Local closure is the computable predicate [lc_at n] ("no dangling de Bruijn
   index >= n"), with [lc := lc_at 0].  This is used in place of the generated
   [lc_exp], whose universal (non-cofinite) binder clause is awkward to
   CONSTRUCT; [lc_at] is equivalent, decidable, and lets [typing_regular] read
   local closure straight off a typing derivation. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.   (* exp_fields_mutind *)
Require Import Goat.GoatRows.
Require Import Goat.GoatNum.
Require Import Goat.GoatDefs.
Require Import Stdlib.Lists.List.
From Stdlib Require Import Lia.

(* ================================================================== *)
(* Locally-nameless infrastructure (LNgen-style, hand-proved).          *)
(* ================================================================== *)

Fixpoint lc_at (n : nat) (e : exp) {struct e} : Prop :=
  match e with
  | e_fvar_b i => i < n
  | e_fvar_f _ => True
  | e_num _ => True
  | e_dec _ => True
  | e_true => True
  | e_false => True
  | e_abs e => lc_at (S n) e
  | e_app a b => lc_at n a /\ lc_at n b
  | e_let a b => lc_at n a /\ lc_at (S n) b
  | e_letrec fs e2 => lcf_at (S n) fs /\ lc_at (S n) e2
  | e_rec fs => lcf_at n fs
  | e_proj e _ => lc_at n e
  | e_unit => True
  | e_str _ => True
  | e_ite a b c => lc_at n a /\ lc_at n b /\ lc_at n c
  | e_bin a _ b => lc_at n a /\ lc_at n b
  | e_tofloat a => lc_at n a
  end
with lcf_at (n : nat) (fs : fields) {struct fs} : Prop :=
  match fs with
  | fs_nil => True
  | fs_cons _ e fs' => lc_at n e /\ lcf_at n fs'
  end.

Definition lc (e : exp) : Prop := lc_at 0 e.
Definition lcf (fs : fields) : Prop := lcf_at 0 fs.

(* monotonicity in the index *)
Lemma lc_at_mono_mut :
  (forall e m n, m <= n -> lc_at m e -> lc_at n e) /\
  (forall fs m n, m <= n -> lcf_at m fs -> lcf_at n fs).
Proof.
  apply exp_fields_mutind.
  - (* fvar_b *) intros i m n Hle H; simpl in *; lia.
  - (* fvar_f *) intros; simpl; auto.
  - (* num *) intros; simpl; auto.
  - (* dec *) intros; simpl; auto.
  - (* true *) intros; simpl; auto.
  - (* false *) intros; simpl; auto.
  - (* abs *) intros e0 IH m n Hle H; simpl in *; apply (IH (S m) (S n)); [ lia | auto ].
  - (* app *) intros a IHa b IHb m n Hle [H1 H2]; simpl; split;
      [ apply (IHa m n) | apply (IHb m n) ]; auto.
  - (* let *) intros a IHa b IHb m n Hle [H1 H2]; simpl; split;
      [ apply (IHa m n Hle H1) | apply (IHb (S m) (S n)); [ lia | auto ] ].
  - (* letrec *) intros fs IHfs e2 IHe2 m n Hle [H1 H2]; simpl; split;
      [ apply (IHfs (S m) (S n)); [ lia | auto ] | apply (IHe2 (S m) (S n)); [ lia | auto ] ].
  - (* rec *) intros fs IH m n Hle H; simpl in *; apply (IH m n Hle H).
  - (* proj *) intros e0 IH l m n Hle H; simpl in *; apply (IH m n Hle H).
  - (* unit *) intros; simpl; auto.
  - (* str *) intros; simpl; auto.
  - (* ite *) intros a IHa b IHb c IHc m n Hle [H1 [H2 H3]]; simpl; repeat split;
      [ apply (IHa m n Hle H1) | apply (IHb m n Hle H2) | apply (IHc m n Hle H3) ].
  - (* bin *) intros a IHa o b IHb m n Hle [H1 H2]; simpl; split;
      [ apply (IHa m n Hle H1) | apply (IHb m n Hle H2) ].
  - (* tofloat *) intros e0 IH m n Hle H; simpl in *; apply (IH m n Hle H).
  - (* fs_nil *) intros; simpl; auto.
  - (* fs_cons *) intros l e0 IHe fs0 IHfs m n Hle [H1 H2]; simpl; split;
      [ apply (IHe m n Hle H1) | apply (IHfs m n Hle H2) ].
Qed.

Lemma lc_at_mono : forall e m n, m <= n -> lc_at m e -> lc_at n e.
Proof. apply lc_at_mono_mut. Qed.

(* opening below the binder level pushes [lc_at] up a level *)
Lemma lc_at_open_inv_mut :
  (forall e n x, lc_at n (open_exp_wrt_exp_rec n (e_fvar_f x) e) -> lc_at (S n) e) /\
  (forall fs n x, lcf_at n (open_fields_wrt_exp_rec n (e_fvar_f x) fs) -> lcf_at (S n) fs).
Proof.
  apply exp_fields_mutind.
  - (* fvar_b *) intros i n x H. cbn in H.
    destruct (lt_eq_lt_dec i n) as [[Hlt|Heq]|Hgt]; cbn in *; lia.
  - (* fvar_f *) intros; simpl; auto.
  - (* num *) intros; simpl; auto.
  - (* dec *) intros; simpl; auto.
  - (* true *) intros; simpl; auto.
  - (* false *) intros; simpl; auto.
  - (* abs *) intros e0 IH n x H; simpl in *; apply (IH (S n) x H).
  - (* app *) intros a IHa b IHb n x H; simpl in *; destruct H as [H1 H2];
      split; [ apply (IHa n x H1) | apply (IHb n x H2) ].
  - (* let *) intros a IHa b IHb n x H; simpl in *; destruct H as [H1 H2];
      split; [ apply (IHa n x H1) | apply (IHb (S n) x H2) ].
  - (* letrec *) intros fs IHfs e2 IHe2 n x H; simpl in *; destruct H as [H1 H2];
      split; [ apply (IHfs (S n) x H1) | apply (IHe2 (S n) x H2) ].
  - (* rec *) intros fs IH n x H; simpl in *; apply (IH n x H).
  - (* proj *) intros e0 IH l n x H; simpl in *; apply (IH n x H).
  - (* unit *) intros; simpl; auto.
  - (* str *) intros; simpl; auto.
  - (* ite *) intros a IHa b IHb c IHc n x H; simpl in *; destruct H as [H1 [H2 H3]];
      repeat split; [ apply (IHa n x H1) | apply (IHb n x H2) | apply (IHc n x H3) ].
  - (* bin *) intros a IHa o b IHb n x H; simpl in *; destruct H as [H1 H2];
      split; [ apply (IHa n x H1) | apply (IHb n x H2) ].
  - (* tofloat *) intros e0 IH n x H; simpl in *; apply (IH n x H).
  - (* fs_nil *) intros; simpl; auto.
  - (* fs_cons *) intros l e0 IHe fs0 IHfs n x H; simpl in *; destruct H as [H1 H2];
      split; [ apply (IHe n x H1) | apply (IHfs n x H2) ].
Qed.

Lemma lc_at_open_inv : forall e n x,
  lc_at n (open_exp_wrt_exp_rec n (e_fvar_f x) e) -> lc_at (S n) e.
Proof. apply lc_at_open_inv_mut. Qed.

Lemma lcf_at_open_inv : forall fs n x,
  lcf_at n (open_fields_wrt_exp_rec n (e_fvar_f x) fs) -> lcf_at (S n) fs.
Proof. apply lc_at_open_inv_mut. Qed.

(* a locally-closed term is unaffected by opening at any index >= its level *)
Lemma lc_at_open_id_mut :
  (forall e n, lc_at n e -> forall k w, n <= k -> open_exp_wrt_exp_rec k w e = e) /\
  (forall fs n, lcf_at n fs -> forall k w, n <= k -> open_fields_wrt_exp_rec k w fs = fs).
Proof.
  apply exp_fields_mutind.
  - (* fvar_b *) intros i n H k w Hle; cbn in H; cbn.
    destruct (lt_eq_lt_dec i k) as [[?|?]|?]; cbn;
      first [ reflexivity | exfalso; lia ].
  - (* fvar_f *) intros; simpl; reflexivity.
  - (* num *) intros; simpl; reflexivity.
  - (* dec *) intros; simpl; reflexivity.
  - (* true *) intros; simpl; reflexivity.
  - (* false *) intros; simpl; reflexivity.
  - (* abs *) intros e0 IH n H k w Hle; simpl in *; f_equal; apply (IH (S n) H (S k) w); lia.
  - (* app *) intros a IHa b IHb n [H1 H2] k w Hle; simpl; f_equal;
      [ apply (IHa n H1 k w Hle) | apply (IHb n H2 k w Hle) ].
  - (* let *) intros a IHa b IHb n [H1 H2] k w Hle; simpl; f_equal;
      [ apply (IHa n H1 k w Hle) | apply (IHb (S n) H2 (S k) w); lia ].
  - (* letrec *) intros fs IHfs e2 IHe2 n [H1 H2] k w Hle; simpl; f_equal;
      [ apply (IHfs (S n) H1 (S k) w); lia | apply (IHe2 (S n) H2 (S k) w); lia ].
  - (* rec *) intros fs IH n H k w Hle; simpl in *; f_equal; apply (IH n H k w Hle).
  - (* proj *) intros e0 IH l n H k w Hle; simpl in *; f_equal; apply (IH n H k w Hle).
  - (* unit *) intros; simpl; reflexivity.
  - (* str *) intros; simpl; reflexivity.
  - (* ite *) intros a IHa b IHb c IHc n [H1 [H2 H3]] k w Hle; simpl; f_equal;
      [ apply (IHa n H1 k w Hle) | apply (IHb n H2 k w Hle) | apply (IHc n H3 k w Hle) ].
  - (* bin *) intros a IHa o b IHb n [H1 H2] k w Hle; simpl; f_equal;
      [ apply (IHa n H1 k w Hle) | apply (IHb n H2 k w Hle) ].
  - (* tofloat *) intros e0 IH n H k w Hle; simpl; f_equal; apply (IH n H k w Hle).
  - (* fs_nil *) intros; simpl; reflexivity.
  - (* fs_cons *) intros l e0 IHe fs0 IHfs n [H1 H2] k w Hle; simpl; f_equal;
      [ apply (IHe n H1 k w Hle) | apply (IHfs n H2 k w Hle) ].
Qed.

Lemma open_lc : forall e w, lc e -> open_exp_wrt_exp e w = e.
Proof.
  intros e w H. unfold open_exp_wrt_exp, lc in *.
  apply (proj1 lc_at_open_id_mut) with (n := 0); [ assumption | lia ].
Qed.

(* Pointwise substitution facts, proved on clean goals so the [eq_dec] case
   split reduces (it does not reduce inside the deeper opening goals, which is
   why those use targeted [cbn [open_exp_wrt_exp_rec]] and rewrite these). *)
Lemma subst_self : forall u x, subst_exp u x (e_fvar_f x) = u.
Proof. intros. simpl. destruct (x == x) as [?|?]; [ reflexivity | contradiction ]. Qed.

Lemma subst_neq : forall u x y, x <> y -> subst_exp u x (e_fvar_f y) = e_fvar_f y.
Proof.
  intros u x y H. simpl. destruct (y == x) as [?|?];
    [ subst; contradiction | reflexivity ].
Qed.

(* substitution introduction: [open e v = (open e x)[x:=v]] when x fresh. *)
Lemma subst_intro_rec_mut :
  (forall e x v k, x `notin` fv_exp e ->
     open_exp_wrt_exp_rec k v e =
     subst_exp v x (open_exp_wrt_exp_rec k (e_fvar_f x) e)) /\
  (forall fs x v k, x `notin` fv_fields fs ->
     open_fields_wrt_exp_rec k v fs =
     subst_fields v x (open_fields_wrt_exp_rec k (e_fvar_f x) fs)).
Proof.
  apply exp_fields_mutind.
  - (* fvar_b *) intros i x v k Hfv. cbn [open_exp_wrt_exp_rec].
    destruct (lt_eq_lt_dec i k) as [[?|?]|?]; try reflexivity.
    rewrite subst_self; reflexivity.
  - (* fvar_f *) intros y x v k Hfv. cbn [open_exp_wrt_exp_rec].
    rewrite subst_neq by (simpl in Hfv; fsetdec). reflexivity.
  - (* num *) intros; reflexivity.
  - (* dec *) intros; reflexivity.
  - (* true *) intros; reflexivity.
  - (* false *) intros; reflexivity.
  - (* abs *) intros e0 IH x v k Hfv; simpl in *; f_equal; apply IH; auto.
  - (* app *) intros a IHa b IHb x v k Hfv; simpl in *; f_equal;
      [ apply IHa | apply IHb ]; fsetdec.
  - (* let *) intros a IHa b IHb x v k Hfv; simpl in *; f_equal;
      [ apply IHa | apply IHb ]; fsetdec.
  - (* letrec *) intros fs IHfs e2 IHe2 x v k Hfv; simpl in *; f_equal;
      [ apply IHfs | apply IHe2 ]; fsetdec.
  - (* rec *) intros fs IH x v k Hfv; simpl in *; f_equal; apply IH; auto.
  - (* proj *) intros e0 IH l x v k Hfv; simpl in *; f_equal; apply IH; auto.
  - (* unit *) intros; reflexivity.
  - (* str *) intros; reflexivity.
  - (* ite *) intros a IHa b IHb c IHc x v k Hfv; simpl in *; f_equal;
      [ apply IHa | apply IHb | apply IHc ]; fsetdec.
  - (* bin *) intros a IHa o b IHb x v k Hfv; simpl in *; f_equal;
      [ apply IHa | apply IHb ]; fsetdec.
  - (* tofloat *) intros e0 IH x v k Hfv; simpl in *; f_equal; apply IH; fsetdec.
  - (* fs_nil *) intros; reflexivity.
  - (* fs_cons *) intros l e0 IHe fs0 IHfs x v k Hfv; simpl in *; f_equal;
      [ apply IHe | apply IHfs ]; fsetdec.
Qed.

Lemma subst_intro : forall e x v,
  x `notin` fv_exp e ->
  open_exp_wrt_exp e v = subst_exp v x (open_exp_wrt_exp e (e_fvar_f x)).
Proof.
  intros. unfold open_exp_wrt_exp. apply (proj1 subst_intro_rec_mut); auto.
Qed.

Lemma subst_intro_fields : forall fs x v,
  x `notin` fv_fields fs ->
  open_fields_wrt_exp fs v = subst_fields v x (open_fields_wrt_exp fs (e_fvar_f x)).
Proof.
  intros. unfold open_fields_wrt_exp. apply (proj2 subst_intro_rec_mut); auto.
Qed.

(* substitution commutes with opening (needs the substituted term lc) *)
Lemma subst_open_rec_mut :
  (forall e u x w k, lc u ->
     subst_exp u x (open_exp_wrt_exp_rec k w e) =
     open_exp_wrt_exp_rec k (subst_exp u x w) (subst_exp u x e)) /\
  (forall fs u x w k, lc u ->
     subst_fields u x (open_fields_wrt_exp_rec k w fs) =
     open_fields_wrt_exp_rec k (subst_exp u x w) (subst_fields u x fs)).
Proof.
  apply exp_fields_mutind.
  - (* fvar_b *) intros i u x w k Hlc. cbn [open_exp_wrt_exp_rec subst_exp].
    destruct (lt_eq_lt_dec i k) as [[?|?]|?];
      cbn [open_exp_wrt_exp_rec subst_exp]; reflexivity.
  - (* fvar_f *) intros y u x w k Hlc. cbn [open_exp_wrt_exp_rec].
    destruct (y == x) as [Hyx|Hyx].
    + subst y. rewrite !subst_self.
      symmetry. unfold lc in Hlc.
      apply (proj1 lc_at_open_id_mut) with (n := 0); [ assumption | lia ].
    + rewrite !subst_neq by congruence.
      cbn [open_exp_wrt_exp_rec]; reflexivity.
  - (* num *) intros; reflexivity.
  - (* dec *) intros; reflexivity.
  - (* true *) intros; reflexivity.
  - (* false *) intros; reflexivity.
  - (* abs *) intros e0 IH u x w k Hlc; simpl; f_equal; apply IH; auto.
  - (* app *) intros a IHa b IHb u x w k Hlc; simpl; f_equal;
      [ apply IHa | apply IHb ]; auto.
  - (* let *) intros a IHa b IHb u x w k Hlc; simpl; f_equal;
      [ apply IHa | apply IHb ]; auto.
  - (* letrec *) intros fs IHfs e2 IHe2 u x w k Hlc; simpl; f_equal;
      [ apply IHfs | apply IHe2 ]; auto.
  - (* rec *) intros fs IH u x w k Hlc; simpl; f_equal; apply IH; auto.
  - (* proj *) intros e0 IH l u x w k Hlc; simpl; f_equal; apply IH; auto.
  - (* unit *) intros; reflexivity.
  - (* str *) intros; reflexivity.
  - (* ite *) intros a IHa b IHb c IHc u x w k Hlc; simpl; f_equal;
      [ apply IHa | apply IHb | apply IHc ]; auto.
  - (* bin *) intros a IHa o b IHb u x w k Hlc; simpl; f_equal;
      [ apply IHa | apply IHb ]; auto.
  - (* tofloat *) intros e0 IH u x w k Hlc; simpl; f_equal; apply IH; auto.
  - (* fs_nil *) intros; reflexivity.
  - (* fs_cons *) intros l e0 IHe fs0 IHfs u x w k Hlc; simpl; f_equal;
      [ apply IHe | apply IHfs ]; auto.
Qed.

Lemma subst_open_var : forall e u x y,
  y <> x -> lc u ->
  subst_exp u x (open_exp_wrt_exp e (e_fvar_f y)) =
  open_exp_wrt_exp (subst_exp u x e) (e_fvar_f y).
Proof.
  intros e u x y Hneq Hlc. unfold open_exp_wrt_exp.
  rewrite (proj1 subst_open_rec_mut) by assumption.
  rewrite subst_neq by congruence. reflexivity.
Qed.

Lemma subst_open_fields_var : forall fs u x y,
  y <> x -> lc u ->
  subst_fields u x (open_fields_wrt_exp fs (e_fvar_f y)) =
  open_fields_wrt_exp (subst_fields u x fs) (e_fvar_f y).
Proof.
  intros fs u x y Hneq Hlc. unfold open_fields_wrt_exp.
  rewrite (proj2 subst_open_rec_mut) by assumption.
  rewrite subst_neq by congruence. reflexivity.
Qed.

(* ================================================================== *)
(* The value restriction is stable under substituting or opening with a  *)
(* syntactic value, and a recursive group stays a group of functions.     *)
(* ================================================================== *)

Lemma is_gen_subst_mut :
  (forall e u x, is_gen_value u = true -> is_gen_value e = true ->
     is_gen_value (subst_exp u x e) = true) /\
  (forall fs u x, is_gen_value u = true -> is_gen_fields fs = true ->
     is_gen_fields (subst_fields u x fs) = true).
Proof.
  apply exp_fields_mutind.
  - (* fvar_b *) intros; reflexivity.
  - (* fvar_f *) intros y u x Hu He. simpl.
    destruct (eq_var y x); [ exact Hu | reflexivity ].
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - (* abs *) intros; reflexivity.
  - (* app *) intros a IHa b IHb u x Hu He; discriminate He.
  - (* let *) intros a IHa b IHb u x Hu He; discriminate He.
  - (* letrec *) intros fs IHfs e2 IHe2 u x Hu He. simpl in He |- *.
    apply andb_prop in He. destruct He as [H1 H2].
    rewrite (IHfs u x Hu H1), (IHe2 u x Hu H2). reflexivity.
  - (* rec *) intros fs IH u x Hu He. simpl in He |- *. apply IH; assumption.
  - (* proj *) intros e0 IH l u x Hu He; discriminate He.
  - intros; reflexivity.
  - intros; reflexivity.
  - (* ite *) intros a IHa b IHb c IHc u x Hu He; discriminate He.
  - (* bin *) intros a IHa o b IHb u x Hu He; discriminate He.
  - (* tofloat *) intros e0 IH u x Hu He. simpl in He |- *. apply IH; assumption.
  - (* fs_nil *) intros; reflexivity.
  - (* fs_cons *) intros l e0 IHe fs0 IHfs u x Hu He. simpl in He |- *.
    apply andb_prop in He. destruct He as [H1 H2].
    rewrite (IHe u x Hu H1), (IHfs u x Hu H2). reflexivity.
Qed.

Lemma is_gen_subst : forall e u x,
  is_gen_value u = true -> is_gen_value e = true ->
  is_gen_value (subst_exp u x e) = true.
Proof. apply is_gen_subst_mut. Qed.

Lemma is_gen_open_mut :
  (forall e u k, is_gen_value u = true -> is_gen_value e = true ->
     is_gen_value (open_exp_wrt_exp_rec k u e) = true) /\
  (forall fs u k, is_gen_value u = true -> is_gen_fields fs = true ->
     is_gen_fields (open_fields_wrt_exp_rec k u fs) = true).
Proof.
  apply exp_fields_mutind.
  - (* fvar_b *) intros i u k Hu He. cbn [open_exp_wrt_exp_rec].
    destruct (lt_eq_lt_dec i k) as [[?|?]|?]; first [ exact Hu | reflexivity ].
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - (* abs *) intros; reflexivity.
  - (* app *) intros a IHa b IHb u k Hu He; discriminate He.
  - (* let *) intros a IHa b IHb u k Hu He; discriminate He.
  - (* letrec *) intros fs IHfs e2 IHe2 u k Hu He. simpl in He |- *.
    apply andb_prop in He. destruct He as [H1 H2].
    rewrite (IHfs u (S k) Hu H1), (IHe2 u (S k) Hu H2). reflexivity.
  - (* rec *) intros fs IH u k Hu He. simpl in He |- *. apply IH; assumption.
  - (* proj *) intros e0 IH l u k Hu He; discriminate He.
  - intros; reflexivity.
  - intros; reflexivity.
  - (* ite *) intros a IHa b IHb c IHc u k Hu He; discriminate He.
  - (* bin *) intros a IHa o b IHb u k Hu He; discriminate He.
  - (* tofloat *) intros e0 IH u k Hu He. simpl in He |- *. apply IH; assumption.
  - (* fs_nil *) intros; reflexivity.
  - (* fs_cons *) intros l e0 IHe fs0 IHfs u k Hu He. simpl in He |- *.
    apply andb_prop in He. destruct He as [H1 H2].
    rewrite (IHe u k Hu H1), (IHfs u k Hu H2). reflexivity.
Qed.

Lemma is_gen_open : forall e u,
  is_gen_value u = true -> is_gen_value e = true ->
  is_gen_value (open_exp_wrt_exp e u) = true.
Proof. intros. apply (proj1 is_gen_open_mut); assumption. Qed.

Lemma is_gen_open_fields : forall fs u,
  is_gen_value u = true -> is_gen_fields fs = true ->
  is_gen_fields (open_fields_wrt_exp fs u) = true.
Proof. intros. apply (proj2 is_gen_open_mut); assumption. Qed.

Lemma fn_group_subst : forall fs u x,
  fn_group fs -> fn_group (subst_fields u x fs).
Proof. induction 1; simpl; constructor; assumption. Qed.

Lemma fn_group_open : forall fs u k,
  fn_group fs -> fn_group (open_fields_wrt_exp_rec k u fs).
Proof. induction 1; simpl; constructor; assumption. Qed.

Lemma fn_group_gen : forall fs, fn_group fs -> is_gen_fields fs = true.
Proof. induction 1; simpl; auto. Qed.

Scheme value_mut := Induction for value Sort Prop
with   rec_value_mut := Induction for rec_value Sort Prop.
Combined Scheme value_rec_value_mutind from value_mut, rec_value_mut.

Lemma value_gen_mut :
  (forall v, value v -> is_gen_value v = true) /\
  (forall fs, rec_value fs -> is_gen_fields fs = true).
Proof.
  apply value_rec_value_mutind; try (intros; reflexivity).
  - intros fs Hrv IH. simpl. exact IH.
  - intros l v fs Hv IHv Hrv IHrv. simpl. rewrite IHv, IHrv. reflexivity.
Qed.

Lemma value_gen : forall v, value v -> is_gen_value v = true.
Proof. apply value_gen_mut. Qed.

(* ================================================================== *)
(* Mutual induction principle for the typing relation.                  *)
(* ================================================================== *)

Scheme typing_mut := Induction for typing Sort Prop
with   field_typing_mut := Induction for field_typing Sort Prop.
Combined Scheme typing_field_mutind from typing_mut, field_typing_mut.

(* ================================================================== *)
(* L4 (part): every typeable term is locally closed (regularity).       *)
(* ================================================================== *)

Lemma typing_regular_mut :
  (forall D G e T, typing D G e T -> lc e) /\
  (forall D G fs R, field_typing D G fs R -> lcf fs).
Proof.
  apply typing_field_mutind; unfold lc, lcf.
  - (* T_Var *) intros; simpl; auto.
  - (* T_Num *) intros; simpl; auto.
  - (* T_Dec *) intros; simpl; auto.
  - (* T_True *) intros; simpl; auto.
  - (* T_False *) intros; simpl; auto.
  - (* T_Abs *) intros L D G e T1 T2 Hpre IH; simpl.
    pick fresh x for L.
    apply (lc_at_open_inv e 0 x). unfold open_exp_wrt_exp in IH. apply IH; auto.
  - (* T_App *) intros D G e1 e2 T1 T2 Hty1 IH1 Hty2 IH2; simpl; split; assumption.
  - (* T_Let *) intros L D G e1 e2 T1 T2 k Hgv Hty1 IH1 Hpre IH2; simpl; split.
    + assumption.
    + pick fresh x for L.
      apply (lc_at_open_inv e2 0 x). unfold open_exp_wrt_exp in IH2. apply IH2; auto.
  - (* T_LetMono *) intros L D G e1 e2 T1 T2 Hty1 IH1 Hpre IH2; simpl; split.
    + assumption.
    + pick fresh x for L.
      apply (lc_at_open_inv e2 0 x). unfold open_exp_wrt_exp in IH2. apply IH2; auto.
  - (* T_Letrec *) intros L D G fs e2 R T k Hfg Hfs IHfs Hpre IH2; simpl; split.
    + pick fresh p for L.
      apply (lcf_at_open_inv fs 0 p). unfold open_fields_wrt_exp in IHfs. apply IHfs; auto.
    + pick fresh p for L.
      apply (lc_at_open_inv e2 0 p). unfold open_exp_wrt_exp in IH2. apply IH2; auto.
  - (* T_Record *) intros D G fs R Hft IH; simpl; assumption.
  - (* T_Proj *) intros D G e l T R Hty IH; simpl; assumption.
  - (* T_Conv *) intros D G e T T' Hty IH Hteq; simpl; assumption.
  - (* T_Unit *) intros; simpl; auto.
  - (* T_Str *) intros; simpl; auto.
  - (* T_If *) intros D G e1 e2 e3 T Ht1 IH1 Ht2 IH2 Ht3 IH3; simpl; auto.
  - (* T_ToFloat *) intros D G e A Ht IH Hs; simpl; assumption.
  - (* T_Bin *) intros D G e1 o e2 A B R Ht1 IH1 Ht2 IH2 Hs; simpl; auto.
  - (* FT_nil *) intros; simpl; auto.
  - (* FT_cons *) intros D G l e T fs R Hty IH1 Hft IH2; simpl; split; assumption.
Qed.

Lemma typing_regular : forall D G e T, typing D G e T -> lc e.
Proof. apply typing_regular_mut. Qed.

Lemma field_typing_regular : forall D G fs R, field_typing D G fs R -> lcf fs.
Proof. apply typing_regular_mut. Qed.

(* ================================================================== *)
(* Record field lookup matches the row's per-label projection: the first *)
(* [l]-field of a well-typed record spine exists exactly when the row     *)
(* carries [l], and its value has the first [l]-field type.  This is the    *)
(* term-level bridge to L3/L7 for the record cases.                        *)
(* ================================================================== *)

Lemma field_lookup_some : forall D G fs R l T rest,
  field_typing D G fs R ->
  pi l R = T :: rest ->
  exists e, lookup_first l fs = Some e /\ typing D G e T.
Proof.
  intros D G fs R l T rest Hft. revert T rest.
  induction Hft as [D0 G0 Hu | D0 G0 lbl e0 T1 fs1 R1 Hty0 Hft1 IH];
    intros T0 rest Hpi.
  - (* FT_nil: R = row_Empty, pi = nil *) simpl in Hpi. discriminate.
  - (* FT_cons lbl e0 T1 fs1 R1 *) simpl in *.
    destruct (Nat.eqb l lbl) eqn:E.
    + (* l = lbl: head matches *)
      inversion Hpi; subst. exists e0. split; [ reflexivity | assumption ].
    + (* l <> lbl: recurse *)
      destruct (IH _ _ Hpi) as [e1 [Hlook Hty]].
      exists e1. split; [ assumption | assumption ].
Qed.

(* ================================================================== *)
(* Inversion through conversion, and canonical forms (L7).              *)
(* ================================================================== *)

(* A value typed at an arrow type is an abstraction.  Holds at any context:
   a variable (T_Var's subject) is never a value, so that case is closed by
   inversion on [value], not by the context being empty. *)
Lemma canon_arrow : forall D G v T1 T2,
  value v -> typing D G v (typ_Arrow T1 T2) -> exists e, v = e_abs e.
Proof.
  intros D G v T1 T2 Hval Hty.
  remember (typ_Arrow T1 T2) as T eqn:HT.
  revert T1 T2 HT Hval.
  induction Hty; intros T1' T2' HT Hval;
    try discriminate;
    try solve [ subst; simpl in *; discriminate ];
    try solve [ inversion Hval ].
  - (* T_Abs *) eexists; reflexivity.
  - (* T_Conv *) subst.
    match goal with
    | H : teq ?A (typ_Arrow _ _) |- _ =>
        apply teq_sym in H; apply teq_Arrow_inv in H;
        destruct H as [A' [B' [HeqT0 [? ?]]]]
    end.
    eapply IHHty; eauto.
Qed.

(* A value typed at a record type is a record value, and its natural row is
   equivalent to the record type's row (L7, record case). *)
Lemma canon_record : forall D G v R,
  value v -> typing D G v (typ_Record R) ->
  exists fs R0, v = e_rec fs /\ rec_value fs /\ field_typing D G fs R0 /\ req R0 R.
Proof.
  intros D G v R Hval Hty.
  remember (typ_Record R) as T eqn:HT.
  revert R HT Hval.
  induction Hty; intros R0 HT Hval;
    try discriminate;
    try solve [ subst; simpl in *; discriminate ];
    try solve [ inversion Hval ].
  - (* T_Record *)
    inversion HT; subst.
    inversion Hval; subst.
    exists fs, R0. repeat split; auto using req_refl.
  - (* T_Conv *) subst.
    match goal with
    | H : teq ?A (typ_Record _) |- _ =>
        apply teq_sym in H; apply teq_Record_inv in H;
        destruct H as [R' [HeqT0 Hreq]]
    end.
    destruct (IHHty R' HeqT0 Hval)
      as [fs [R1 [Hv [Hrv [Hft Hreq1]]]]].
    exists fs, R1. repeat split; auto.
    apply req_trans with (R2 := R'); auto.
Qed.

(* A value at (a type equal to) a base type is a literal of that type. *)
Lemma canon_base : forall D G v T,
  value v -> typing D G v T ->
  (teq T typ_Int -> exists n, v = e_num n) /\
  (teq T typ_Float -> (exists n, v = e_num n) \/ (exists d, v = e_dec d)) /\
  (teq T typ_String -> exists q, v = e_str q) /\
  (teq T typ_Bool -> v = e_true \/ v = e_false).
Proof.
  intros D G v T Hval Hty. revert Hval.
  induction Hty; intros Hval; try solve [ inversion Hval ];
    (* a literal, a function or a record: the head type decides every clause *)
    try solve [ repeat apply conj; intros Hq; apply teq_thead in Hq; simpl in Hq;
      first [ discriminate | (eexists; reflexivity) | (left; eexists; reflexivity)
            | (right; eexists; reflexivity) | (left; reflexivity) | (right; reflexivity) ] ].
  - (* T_Num: the type is Int, Float or a Literal variable *)
    destruct T; simpl in *; try discriminate;
      repeat apply conj; intros Hq; apply teq_thead in Hq; simpl in Hq;
      first [ discriminate | (eexists; reflexivity) | (left; eexists; reflexivity) ].
  - (* T_Conv *) destruct (IHHty Hval) as [A [B [C E]]].
    repeat apply conj; intros Hq;
      [ apply A | apply B | apply C | apply E ];
      (eapply teq_trans; [ eassumption | exact Hq ]).
Qed.

(* A value at a type variable is a numeral: only [T_Num] types a value there. *)
Lemma canon_var : forall D G v T a,
  value v -> typing D G v T -> teq T (typ_Var a) -> exists n, v = e_num n.
Proof.
  intros D G v T a Hval Hty. revert Hval.
  induction Hty; intros Hval Hq; try solve [ inversion Hval ];
    try solve [ apply teq_thead in Hq; simpl in Hq; discriminate ].
  - (* T_Num *) eexists; reflexivity.
  - (* T_Conv *) apply IHHty; auto. eapply teq_trans; eassumption.
Qed.

(* A value of a Numeric type is a numeral or a decimal. *)
Lemma canon_numeric : forall D G v A,
  value v -> typing D G v A -> sat D k_Numeric A ->
  (exists n, v = e_num n) \/ (exists d, v = e_dec d).
Proof.
  intros D G v A Hv Hty Hs. destruct A; simpl in Hs; try discriminate.
  - destruct (canon_base _ _ _ _ Hv Hty) as [C _]. left. exact (C (teq_refl _)).
  - destruct (canon_base _ _ _ _ Hv Hty) as [_ [C _]]. exact (C (teq_refl _)).
  - left. exact (canon_var _ _ _ _ _ Hv Hty (teq_refl _)).
Qed.

(* Two numerals add, subtract or multiply as [Int]s, or the result is out of
   range and traps. *)
Lemma ring_nums : forall o a b,
  kind o = k_ring ->
  (exists v, bin_step o (e_num a) (e_num b) v) \/
  (exists k, bin_trap o (e_num a) (e_num b) k).
Proof.
  intros o a b Hk. destruct (in_int (ring_Z o a b)) eqn:Hr.
  - left. eexists. apply bs_ring_int; assumption.
  - right. exists trap_overflow. apply bt_ring_overflow; assumption.
Qed.

(* An operator applied to two values of the types its signature wants either
   computes a value or raises a defined error. *)
Lemma bin_progress : forall D G o v1 v2 A B R,
  bin_sig D o A B R -> value v1 -> value v2 ->
  typing D G v1 A -> typing D G v2 B ->
  (exists v, bin_step o v1 v2 v) \/ (exists k, bin_trap o v1 v2 k).
Proof.
  intros D G o v1 v2 A B R Hs Hv1 Hv2 H1 H2.
  assert (Hint : forall v, value v -> typing D G v typ_Int -> exists a, v = e_num a)
    by (intros v Hv Hty; destruct (canon_base _ _ _ _ Hv Hty) as [C _]; exact (C (teq_refl _))).
  assert (Hflt : forall v, value v -> typing D G v typ_Float ->
                 (exists n, v = e_num n) \/ (exists d, v = e_dec d))
    by (intros v Hv Hty; destruct (canon_base _ _ _ _ Hv Hty) as [_ [C _]]; exact (C (teq_refl _))).
  destruct Hs as [ D0 o A Hk Hsat | D0 | D0 o Hk | D0 o B Hk HB ].
  - (* [+ - *] on two numbers of one Numeric type *)
    destruct A; simpl in Hsat; try discriminate.
    + (* Int: in range it steps, out of range it traps *)
      destruct (Hint _ Hv1 H1) as [a ->]. destruct (Hint _ Hv2 H2) as [b ->].
      apply ring_nums; assumption.
    + (* Float: two numerals step as Ints; with a decimal, any Float *)
      destruct (Hflt _ Hv1 H1) as [[a ->] | [x ->]]; destruct (Hflt _ Hv2 H2) as [[b ->] | [y ->]].
      * apply ring_nums; assumption.
      * left. exists (e_dec 0). apply bs_float; [ left; assumption | constructor ].
      * left. exists (e_dec 0). apply bs_float; [ left; assumption | constructor ].
      * left. exists (e_dec 0). apply bs_float; [ left; assumption | constructor ].
    + (* a Numeric variable: a value there is a numeral *)
      destruct (canon_var _ _ _ _ _ Hv1 H1 (teq_refl _)) as [n1 ->].
      destruct (canon_var _ _ _ _ _ Hv2 H2 (teq_refl _)) as [n2 ->].
      apply ring_nums; assumption.
  - (* [/] on two Floats: any Float, a zero divisor included *)
    destruct (Hflt _ Hv1 H1) as [[a ->] | [x ->]]; destruct (Hflt _ Hv2 H2) as [[b ->] | [y ->]];
      left; exists (e_dec 0).
    + apply bs_quot_num; reflexivity.
    + apply bs_float; [ right; reflexivity | constructor ].
    + apply bs_float; [ right; reflexivity | constructor ].
    + apply bs_float; [ right; reflexivity | constructor ].
  - (* [//] and [%]: a zero divisor traps, and so does a quotient out of range *)
    destruct (Hint _ Hv1 H1) as [a ->]. destruct (Hint _ Hv2 H2) as [b ->].
    destruct (z_is_zero b) eqn:Hz.
    + right. exists trap_div_zero. apply bt_div_zero; assumption.
    + destruct (in_int (whole_Z o a b)) eqn:Hr.
      * left. eexists. apply bs_whole; assumption.
      * right. exists trap_overflow. apply bt_whole_overflow; assumption.
  - (* a comparison of two Ints, Floats, strings or booleans *)
    inversion HB; subst.
    + destruct (Hint _ Hv1 H1) as [a ->]. destruct (Hint _ Hv2 H2) as [b ->].
      left. eexists. apply bs_cmp_int; assumption.
    + destruct (Hflt _ Hv1 H1) as [[a ->] | [x ->]]; destruct (Hflt _ Hv2 H2) as [[b ->] | [y ->]];
        left.
      * eexists. apply bs_cmp_int; assumption.
      * exists (of_bool true). apply bs_cmp_float; [ assumption | constructor ].
      * exists (of_bool true). apply bs_cmp_float; [ assumption | constructor ].
      * exists (of_bool true). apply bs_cmp_float; [ assumption | constructor ].
    + destruct (canon_base _ _ _ _ Hv1 H1) as [_ [_ [C1 _]]]. destruct (C1 (teq_refl _)) as [p ->].
      destruct (canon_base _ _ _ _ Hv2 H2) as [_ [_ [C2 _]]]. destruct (C2 (teq_refl _)) as [q ->].
      left. eexists. apply bs_cmp_str; assumption.
    + destruct (canon_base _ _ _ _ Hv1 H1) as [_ [_ [_ C1]]].
      destruct (canon_base _ _ _ _ Hv2 H2) as [_ [_ [_ C2]]].
      destruct (C1 (teq_refl _)) as [-> | ->]; destruct (C2 (teq_refl _)) as [-> | ->];
        (left; eexists; eapply bs_cmp_bool; [ exact Hk | reflexivity | reflexivity ]).
Qed.

(* ================================================================== *)
(* Progress (docs/semantics.md section 7).                              *)
(*                                                                        *)
(* NEW TO THIS PROOF?  The overview of the whole soundness argument is at *)
(* the top of GoatSound.v.  Short version: soundness says a program that  *)
(* passes the type checker never gets stuck.  It splits into PROGRESS     *)
(* (this section: a well-typed program is finished, can step, or stops    *)
(* with a defined runtime error) and PRESERVATION (GoatSound.v: a step    *)
(* keeps the program well typed).                                         *)
(*                                                                        *)
(* WHAT PROGRESS SAYS: if [e] has some type in the EMPTY context (a       *)
(* closed program: no variables left over from outside), then [e] is      *)
(* either a [value] (a finished result: number, bool, function, record    *)
(* of values), or there is some [e'] it can [step] to, or it [traps]: it  *)
(* raises a defined error, which today is integer division by zero.       *)
(* Never stuck.                                                           *)
(*                                                                        *)
(* HOW THE PROOF GOES: we prove it for every typing derivation, one       *)
(* typing rule at a time, assuming the claim for the sub-terms (the       *)
(* induction hypotheses [IH], [IH1], ...).  In each case ask:        *)
(* is the term already finished?  If not, which step can it take?         *)
(*  - Literals and functions are values already.                          *)
(*  - A variable cannot occur: the context is empty, nothing to look up.  *)
(*  - A call [e1 e2]: first make [e1] finish, then [e2], then the call    *)
(*    can run.  The key fact is "canonical forms": a finished value of    *)
(*    function type really is a function ([canon_arrow]); a finished      *)
(*    value of record type really is a record ([canon_record]).  Without  *)
(*    that, a call could be applied to, say, a number, and be stuck.      *)
(*  - [let], records, and field access work the same way.                 *)
(*  - An operator on two values computes ([bin_step]) or raises an error  *)
(*    ([bin_trap]); [bin_progress] shows one of the two always applies.   *)
(*  - If a sub-term traps, so does the whole term.                        *)
(* The statement carries [G = nil] so the induction can be run over       *)
(* derivations whose context is a variable; at the end we supply nil.     *)
(* ================================================================== *)

Lemma progress_mut :
  (forall D G e T, typing D G e T -> G = nil ->
     value e \/ (exists e', step e e') \/ (exists k, traps e k)) /\
  (forall D G fs R, field_typing D G fs R -> G = nil ->
     rec_value fs \/ (exists fs', step_fields fs fs') \/ (exists k, traps_fields fs k)).
Proof.
  (* Induction over typing derivations: one case per typing rule. *)
  apply typing_field_mutind.
  - (* Case: a variable.  Impossible here: the context is empty, so there is
       nothing for the variable to be bound to.  We show that by looking at
       the claim that [x] is in an empty list, which has no way to hold. *)
    intros D G x s T Hu Hb Hi HG; subst. inversion Hb.
  - (* T_Num: numbers are values (the left side of the "value or can step"
       claim). *)
    intros; left; auto.
  - (* T_Dec *) intros; left; auto.
  - (* T_True *) intros; left; auto.
  - (* T_False *) intros; left; auto.
  - (* Case: a function.  Functions are values: we do not run the body until
       the function is called. *)
    intros L D G e T1 T2 Hbody IH HG; subst. left; auto.
  - (* Case: a call [e1 e2].  A call is never a value.  Look at the function
       part [e1] first:
         - either it is finished, then we look at [e2];
         - or it can step, and then the whole call steps (st_app1);
         - or it traps, and then so does the call (tr_app1). *)
    intros D G e1 e2 T1 T2 Hty1 IH1 Hty2 IH2 HG; subst.
    right. destruct (IH1 eq_refl) as [Hv1 | [[e1' Hs1] | [k Hk1]]].
    + (* [e1] is a finished value with a function type, so by canonical forms
         it is literally [fun x => e0]. *)
      destruct (canon_arrow _ _ _ _ _ Hv1 Hty1) as [e0 Hev]; subst.
      destruct (IH2 eq_refl) as [Hv2 | [[e2' Hs2] | [k Hk2]]].
      * (* Argument is finished too: perform the call, plugging [e2] into the
           body (st_beta). *)
        left. exists (open_exp_wrt_exp e0 e2). apply st_beta; auto.
      * (* Argument can still step: step it (st_app2). *)
        left. exists (e_app (e_abs e0) e2'). apply st_app2; auto.
      * right. exists k. apply tr_app2; auto.
    + left. exists (e_app e1' e2). apply st_app1; auto.
    + right. exists k. apply tr_app1; auto.
  - (* Case: [let x = e1 in e2].  If [e1] is finished, plug it into [e2]
       (st_letv); otherwise step [e1] (st_let1) or propagate its trap. *)
    intros L D G e1 e2 T1 T2 kf Hgv Hty1 IH1 Hbody IH2 HG; subst.
    right. destruct (IH1 eq_refl) as [Hv1 | [[e1' Hs1] | [k Hk]]].
    + left. exists (open_exp_wrt_exp e2 e1). apply st_letv; auto.
    + left. exists (e_let e1' e2). apply st_let1; auto.
    + right. exists k. apply tr_let1; auto.
  - (* T_LetMono: the same, the binding is just not generalized. *)
    intros L D G e1 e2 T1 T2 Hty1 IH1 Hbody IH2 HG; subst.
    right. destruct (IH1 eq_refl) as [Hv1 | [[e1' Hs1] | [k Hk]]].
    + left. exists (open_exp_wrt_exp e2 e1). apply st_letv; auto.
    + left. exists (e_let e1' e2). apply st_let1; auto.
    + right. exists k. apply tr_let1; auto.
  - (* Case: a recursive group.  Never a value; it unrolls at once
       (st_letrec), because its members are functions. *)
    intros L D G fs e2 R T kf Hfg Hfs IHfs Hbody IH2 HG; subst.
    right; left. eexists. apply st_letrec; exact Hfg.
  - (* Case: a record.  Finished if every field is; otherwise a field steps
       or traps.  The field list has its own companion claim (second half of
       the statement), which [IH] provides. *)
    intros D G fs R Hft IH HG; subst.
    destruct (IH eq_refl) as [Hrv | [[fs' Hs] | [k Hk]]].
    + left; auto.
    + right; left. exists (e_rec fs'). apply st_rec; auto.
    + right; right. exists k. apply tr_rec; auto.
  - (* Case: field access [e.l].  If [e] is not finished, step it.  If it is,
       canonical forms says it is a record, and its type says field [l]
       exists, so we can look the field up and take it (st_projrec). *)
    intros D G e l T R Hty IH HG; subst.
    right. destruct (IH eq_refl) as [Hv | [[e' Hs] | [k Hk]]].
    + destruct (canon_record _ _ _ _ Hv Hty) as [fs [R0 [Hev [Hrv [Hft Hreq]]]]]; subst.
      apply req_surface in Hreq. destruct Hreq as [T0 [rest [Hpi Hteq]]].
      destruct (field_lookup_some _ _ _ _ _ _ _ Hft Hpi) as [e0 [Hlook Hty0]].
      left. exists e0. apply st_projrec; auto.
    + left. exists (e_proj e' l). apply st_proj; auto.
    + right. exists k. apply tr_proj; auto.
  - (* Case: a conversion (T_Conv): the same term viewed at an equal type.
       Whether it is finished or can step does not depend on the type, so
       the induction hypothesis already answers it. *)
    intros D G e T T' Hty IH Hteq HG; subst.
    exact (IH eq_refl).
  - (* T_Unit *) intros; left; auto.
  - (* T_Str *) intros; left; auto.
  - (* Case: [if e1 then e2 else e3].  Never a value.  If [e1] is finished,
       canonical forms says it is [true] or [false], and the matching branch
       is taken; otherwise [e1] steps or traps. *)
    intros D G e1 e2 e3 T Ht1 IH1 Ht2 IH2 Ht3 IH3 HG; subst.
    right. destruct (IH1 eq_refl) as [Hv | [[e1' Hs] | [k Hk]]].
    + destruct (canon_base _ _ _ _ Hv Ht1) as [_ [_ [_ C]]].
      destruct (C (teq_refl _)) as [-> | ->].
      * left. exists e2. apply st_ite_true.
      * left. exists e3. apply st_ite_false.
    + left. exists (e_ite e1' e2 e3). apply st_ite1; auto.
    + right. exists k. apply tr_ite1; auto.
  - (* Case: a coercion [float(e)].  If [e] is finished, canonical forms says
       it is a whole number, and the coercion steps to a Float (st_tofloat);
       otherwise [e] steps or traps. *)
    intros D G e A Ht IH Hsat HG; subst.
    right. destruct (IH eq_refl) as [Hv | [[e' Hs] | [k Hk]]].
    + destruct (canon_numeric _ _ _ _ Hv Ht Hsat) as [[a ->] | [d ->]].
      * left. exists (e_dec 0). apply st_tofloat.
      * left. exists (e_dec d). apply st_tofloat_dec.
    + left. exists (e_tofloat e'). apply st_tofloat1; auto.
    + right. exists k. apply tr_tofloat; auto.
  - (* Case: an operator [e1 o e2].  Evaluate [e1], then [e2]; then the
       operator computes a value or raises its error ([bin_progress]). *)
    intros D G e1 o e2 A B R Ht1 IH1 Ht2 IH2 Hs HG; subst.
    right. destruct (IH1 eq_refl) as [Hv1 | [[e1' Hs1] | [k Hk1]]].
    + destruct (IH2 eq_refl) as [Hv2 | [[e2' Hs2] | [k Hk2]]].
      * destruct (bin_progress _ _ _ _ _ _ _ _ Hs Hv1 Hv2 Ht1 Ht2)
          as [[v Hb] | [k Hb]].
        -- left. exists v. apply st_bin; auto.
        -- right. exists k. apply tr_bin; auto.
      * left. exists (e_bin e1 o e2'). apply st_bin2; auto.
      * right. exists k. apply tr_bin2; auto.
    + left. exists (e_bin e1' o e2). apply st_bin1; auto.
    + right. exists k. apply tr_bin1; auto.
  - (* FT_nil *) intros; left; auto.
  - (* FT_cons *) intros D G l e T fs R Hty IH1 Hft IH2 HG; subst.
    destruct (IH1 eq_refl) as [Hv | [[e' Hs] | [k Hk]]].
    + destruct (IH2 eq_refl) as [Hrv | [[fs' Hs'] | [k Hk']]].
      * left; auto.
      * right; left. exists (fs_cons l e fs'). apply stf_cons; auto.
      * right; right. exists k. apply trf_cons; auto.
    + right; left. exists (fs_cons l e' fs). apply stf_here; auto.
    + right; right. exists k. apply trf_here; auto.
Qed.

(* Progress, in its final form: a closed, well-typed program is a value, can
   take a step, or stops with a defined runtime error. *)
Theorem progress : forall D e T,
  typing D nil e T ->
  value e \/ (exists e', step e e') \/ (exists k, traps e k).
Proof. intros D e T H. apply (proj1 progress_mut D nil e T H). reflexivity. Qed.

(* ================================================================== *)
(* Typing inversion up to conversion (the T-Conv "induction tax",       *)
(* docs/semantics.md section 9).  Each lemma peels any trailing          *)
(* conversions off a derivation whose subject has a known head.          *)
(* ================================================================== *)

(* Inversion for a call, up to conversion. *)
Lemma app_inv : forall D G e1 e2 T,
  typing D G (e_app e1 e2) T ->
  exists A B, typing D G e1 (typ_Arrow A B) /\ typing D G e2 A /\ teq B T.
Proof.
  intros D G e1 e2 T H. remember (e_app e1 e2) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_App *) inversion He; subst. exists T1, T2.
    repeat split; auto using teq_refl.
  - (* T_Conv *) destruct (IHtyping He) as [A [B [Hty1 [Hty2 Hb]]]].
    exists A, B. repeat split; try assumption. eauto using teq_trans.
Qed.

Lemma abs_inv : forall D G e T,
  typing D G (e_abs e) T ->
  exists (L : vars) T1 T2,
    (forall x, x `notin` L ->
       typing D ((x ~ sch_mono T1) ++ G) (open_exp_wrt_exp e (e_fvar_f x)) T2) /\
    teq (typ_Arrow T1 T2) T.
Proof.
  intros D G e T H. remember (e_abs e) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Abs *) inversion He; subst. exists L, T1, T2.
    split; auto using teq_refl.
  - (* T_Conv *) destruct (IHtyping He) as [L [T1 [T2 [Hbody Hteq]]]].
    exists L, T1, T2. split; try assumption. eauto using teq_trans.
Qed.

(* A [let] is typed either with its binding generalized (it is a syntactic
   value) or monomorphic. *)
Lemma let_inv : forall D G e1 e2 T,
  typing D G (e_let e1 e2) T ->
  exists (L : vars) T1 T2,
    ((is_gen_value e1 = true /\ exists (k : sort_fn),
      typing (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx G)) k) G e1 T1 /\
      forall x, x `notin` L ->
        typing D ((x ~ gen G T1 k) ++ G) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) \/
     (typing D G e1 T1 /\
      forall x, x `notin` L ->
        typing D ((x ~ sch_mono T1) ++ G) (open_exp_wrt_exp e2 (e_fvar_f x)) T2)) /\
    teq T2 T.
Proof.
  intros D G e1 e2 T H. remember (e_let e1 e2) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Let *) inversion He; subst. exists L, T1, T2.
    split; [ left; split; [ assumption | exists k; auto ] | apply teq_refl ].
  - (* T_LetMono *) inversion He; subst. exists L, T1, T2.
    split; [ right; auto | apply teq_refl ].
  - (* T_Conv *) destruct (IHtyping He) as [L [T1 [T2 [Hbody Hteq]]]].
    exists L, T1, T2. split; [ assumption | eauto using teq_trans ].
Qed.

Lemma letrec_inv : forall D G fs e2 T,
  typing D G (e_letrec fs e2) T ->
  exists (L : vars) R T2 (k : sort_fn),
    fn_group fs /\
    (forall p, p `notin` L ->
       field_typing (ext D (AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G)) k)
         ((p ~ sch_mono (typ_Record R)) ++ G)
         (open_fields_wrt_exp fs (e_fvar_f p)) R) /\
    (forall p, p `notin` L ->
       typing D ((p ~ gen G (typ_Record R) k) ++ G) (open_exp_wrt_exp e2 (e_fvar_f p)) T2) /\
    teq T2 T.
Proof.
  intros D G fs e2 T H. remember (e_letrec fs e2) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Letrec *) inversion He; subst. exists L, R, T, k.
    repeat split; auto using teq_refl.
  - (* T_Conv *) destruct (IHtyping He) as [L [R [T2 [kk [Hfg [Hfs [Hbody Hteq]]]]]]].
    exists L, R, T2, kk. repeat split; try assumption. eauto using teq_trans.
Qed.

Lemma proj_inv : forall D G e l T,
  typing D G (e_proj e l) T ->
  exists T0 R, typing D G e (typ_Record (row_Ext l T0 R)) /\ teq T0 T.
Proof.
  intros D G e l T H. remember (e_proj e l) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Proj *) inversion He; subst. exists T, R.
    split; auto using teq_refl.
  - (* T_Conv *) destruct (IHtyping He) as [T0 [R [Hty Hteq]]].
    exists T0, R. split; try assumption. eauto using teq_trans.
Qed.

Lemma rec_inv : forall D G fs T,
  typing D G (e_rec fs) T ->
  exists R, field_typing D G fs R /\ teq (typ_Record R) T.
Proof.
  intros D G fs T H. remember (e_rec fs) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Record *) inversion He; subst. exists R.
    split; auto using teq_refl.
  - (* T_Conv *) destruct (IHtyping He) as [R [Hft Hteq]].
    exists R. split; try assumption. eauto using teq_trans.
Qed.

Lemma ite_inv : forall D G e1 e2 e3 T,
  typing D G (e_ite e1 e2 e3) T ->
  exists T', typing D G e1 typ_Bool /\ typing D G e2 T' /\ typing D G e3 T' /\ teq T' T.
Proof.
  intros D G e1 e2 e3 T H. remember (e_ite e1 e2 e3) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Conv *) destruct (IHtyping He) as [T0 [A [B [C E]]]].
    exists T0. repeat split; try assumption. eauto using teq_trans.
  - (* T_If *) inversion He; subst. eexists. repeat split; try eassumption; apply teq_refl.
Qed.

Lemma tofloat_inv : forall D G e T,
  typing D G (e_tofloat e) T ->
  exists A, typing D G e A /\ sat D k_Numeric A /\ teq typ_Float T.
Proof.
  intros D G e T H. remember (e_tofloat e) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Conv *) destruct (IHtyping He) as [A [B [C E]]].
    exists A. repeat split; [ exact B | exact C | eauto using teq_trans ].
  - (* T_ToFloat *) inversion He; subst. exists A. repeat split; auto using teq_refl.
Qed.

(* A numeral's type is a Literal type, through any conversion: the equivalence
   moves only the shape of a record or an arrow, never a base type or a
   variable. *)
Lemma teq_sat_iff : forall T T', teq T T' -> forall D k, sat D k T <-> sat D k T'.
Proof.
  induction 1; intros D kk; try (simpl; tauto).
  - rewrite (IHteq1 D kk). apply IHteq2.
  - symmetry. apply IHteq.
Qed.

Lemma teq_sat : forall T T' D k, teq T T' -> sat D k T -> sat D k T'.
Proof. intros T T' D k H. apply (teq_sat_iff _ _ H). Qed.

Lemma num_inv : forall D G n T, typing D G (e_num n) T -> sat D k_Literal T.
Proof.
  intros D G n T H. remember (e_num n) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Num *) inversion He; subst. assumption.
  - (* T_Conv *) eapply teq_sat; [ exact H0 | apply IHtyping; exact He ].
Qed.

Lemma bin_inv : forall D G e1 o e2 T,
  typing D G (e_bin e1 o e2) T ->
  exists A B R, typing D G e1 A /\ typing D G e2 B /\ bin_sig D o A B R /\ teq R T.
Proof.
  intros D G e1 o e2 T H. remember (e_bin e1 o e2) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Conv *) destruct (IHtyping He) as [A [B [R [H1 [H2 [H3 H4]]]]]].
    exists A, B, R. repeat split; try assumption. eauto using teq_trans.
  - (* T_Bin *) inversion He; subst. exists A, B, R. repeat split; auto using teq_refl.
Qed.

(* Term substitution (L6a/L6b), preservation and soundness are proved in
   GoatSubst.v, after the type/row-substitution theory (L5) they depend on.
   This file supplies the inversion lemmas above and [progress]. *)
