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
Require Import Goat.GoatDefs.
Require Import Coq.Lists.List.
Require Import Lia.

(* ================================================================== *)
(* Locally-nameless infrastructure (LNgen-style, hand-proved).          *)
(* ================================================================== *)

Fixpoint lc_at (n : nat) (e : exp) {struct e} : Prop :=
  match e with
  | e_fvar_b i => i < n
  | e_fvar_f _ => True
  | e_num _ => True
  | e_true => True
  | e_false => True
  | e_abs e => lc_at (S n) e
  | e_app a b => lc_at n a /\ lc_at n b
  | e_let a b => lc_at n a /\ lc_at (S n) b
  | e_rec fs => lcf_at n fs
  | e_proj e _ => lc_at n e
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
  - (* true *) intros; simpl; auto.
  - (* false *) intros; simpl; auto.
  - (* abs *) intros e0 IH m n Hle H; simpl in *; apply (IH (S m) (S n)); [ lia | auto ].
  - (* app *) intros a IHa b IHb m n Hle [H1 H2]; simpl; split;
      [ apply (IHa m n) | apply (IHb m n) ]; auto.
  - (* let *) intros a IHa b IHb m n Hle [H1 H2]; simpl; split;
      [ apply (IHa m n Hle H1) | apply (IHb (S m) (S n)); [ lia | auto ] ].
  - (* rec *) intros fs IH m n Hle H; simpl in *; apply (IH m n Hle H).
  - (* proj *) intros e0 IH l m n Hle H; simpl in *; apply (IH m n Hle H).
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
  - (* true *) intros; simpl; auto.
  - (* false *) intros; simpl; auto.
  - (* abs *) intros e0 IH n x H; simpl in *; apply (IH (S n) x H).
  - (* app *) intros a IHa b IHb n x H; simpl in *; destruct H as [H1 H2];
      split; [ apply (IHa n x H1) | apply (IHb n x H2) ].
  - (* let *) intros a IHa b IHb n x H; simpl in *; destruct H as [H1 H2];
      split; [ apply (IHa n x H1) | apply (IHb (S n) x H2) ].
  - (* rec *) intros fs IH n x H; simpl in *; apply (IH n x H).
  - (* proj *) intros e0 IH l n x H; simpl in *; apply (IH n x H).
  - (* fs_nil *) intros; simpl; auto.
  - (* fs_cons *) intros l e0 IHe fs0 IHfs n x H; simpl in *; destruct H as [H1 H2];
      split; [ apply (IHe n x H1) | apply (IHfs n x H2) ].
Qed.

Lemma lc_at_open_inv : forall e n x,
  lc_at n (open_exp_wrt_exp_rec n (e_fvar_f x) e) -> lc_at (S n) e.
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
  - (* true *) intros; simpl; reflexivity.
  - (* false *) intros; simpl; reflexivity.
  - (* abs *) intros e0 IH n H k w Hle; simpl in *; f_equal; apply (IH (S n) H (S k) w); lia.
  - (* app *) intros a IHa b IHb n [H1 H2] k w Hle; simpl; f_equal;
      [ apply (IHa n H1 k w Hle) | apply (IHb n H2 k w Hle) ].
  - (* let *) intros a IHa b IHb n [H1 H2] k w Hle; simpl; f_equal;
      [ apply (IHa n H1 k w Hle) | apply (IHb (S n) H2 (S k) w); lia ].
  - (* rec *) intros fs IH n H k w Hle; simpl in *; f_equal; apply (IH n H k w Hle).
  - (* proj *) intros e0 IH l n H k w Hle; simpl in *; f_equal; apply (IH n H k w Hle).
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
  - (* true *) intros; reflexivity.
  - (* false *) intros; reflexivity.
  - (* abs *) intros e0 IH x v k Hfv; simpl in *; f_equal; apply IH; auto.
  - (* app *) intros a IHa b IHb x v k Hfv; simpl in *; f_equal;
      [ apply IHa | apply IHb ]; fsetdec.
  - (* let *) intros a IHa b IHb x v k Hfv; simpl in *; f_equal;
      [ apply IHa | apply IHb ]; fsetdec.
  - (* rec *) intros fs IH x v k Hfv; simpl in *; f_equal; apply IH; auto.
  - (* proj *) intros e0 IH l x v k Hfv; simpl in *; f_equal; apply IH; auto.
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
  - (* true *) intros; reflexivity.
  - (* false *) intros; reflexivity.
  - (* abs *) intros e0 IH u x w k Hlc; simpl; f_equal; apply IH; auto.
  - (* app *) intros a IHa b IHb u x w k Hlc; simpl; f_equal;
      [ apply IHa | apply IHb ]; auto.
  - (* let *) intros a IHa b IHb u x w k Hlc; simpl; f_equal;
      [ apply IHa | apply IHb ]; auto.
  - (* rec *) intros fs IH u x w k Hlc; simpl; f_equal; apply IH; auto.
  - (* proj *) intros e0 IH l u x w k Hlc; simpl; f_equal; apply IH; auto.
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
  (forall G e T, typing G e T -> lc e) /\
  (forall G fs R, field_typing G fs R -> lcf fs).
Proof.
  apply typing_field_mutind; unfold lc, lcf.
  - (* T_Var *) intros; simpl; auto.
  - (* T_Num *) intros; simpl; auto.
  - (* T_True *) intros; simpl; auto.
  - (* T_False *) intros; simpl; auto.
  - (* T_Abs *) intros L G e T1 T2 Hpre IH; simpl.
    pick fresh x for L.
    apply (lc_at_open_inv e 0 x). unfold open_exp_wrt_exp in IH. apply IH; auto.
  - (* T_App *) intros G e1 e2 T1 T2 Hty1 IH1 Hty2 IH2; simpl; split; assumption.
  - (* T_Let *) intros L G e1 e2 T1 T2 Hty1 IH1 Hpre IH2; simpl; split.
    + assumption.
    + pick fresh x for L.
      apply (lc_at_open_inv e2 0 x). unfold open_exp_wrt_exp in IH2. apply IH2; auto.
  - (* T_Record *) intros G fs R Hft IH; simpl; assumption.
  - (* T_Proj *) intros G e l T R Hty IH; simpl; assumption.
  - (* T_Conv *) intros G e T T' Hty IH Hteq; simpl; assumption.
  - (* FT_nil *) intros; simpl; auto.
  - (* FT_cons *) intros G l e T fs R Hty IH1 Hft IH2; simpl; split; assumption.
Qed.

Lemma typing_regular : forall G e T, typing G e T -> lc e.
Proof. apply typing_regular_mut. Qed.

Lemma field_typing_regular : forall G fs R, field_typing G fs R -> lcf fs.
Proof. apply typing_regular_mut. Qed.

(* ================================================================== *)
(* Record field lookup matches the row's per-label projection: the first *)
(* [l]-field of a well-typed record spine exists exactly when the row     *)
(* carries [l], and its value has the first [l]-field type.  This is the    *)
(* term-level bridge to L3/L7 for the record cases.                        *)
(* ================================================================== *)

Lemma field_lookup_some : forall G fs R l T rest,
  field_typing G fs R ->
  pi l R = T :: rest ->
  exists e, lookup_first l fs = Some e /\ typing G e T.
Proof.
  intros G fs R l T rest Hft. revert T rest.
  induction Hft as [G0 Hu | G0 lbl e0 T1 fs1 R1 Hty0 Hft1 IH];
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
Lemma canon_arrow : forall G v T1 T2,
  value v -> typing G v (typ_Arrow T1 T2) -> exists e, v = e_abs e.
Proof.
  intros G v T1 T2 Hval Hty.
  remember (typ_Arrow T1 T2) as T eqn:HT.
  revert T1 T2 HT Hval.
  induction Hty; intros T1' T2' HT Hval;
    try discriminate;
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
Lemma canon_record : forall G v R,
  value v -> typing G v (typ_Record R) ->
  exists fs R0, v = e_rec fs /\ rec_value fs /\ field_typing G fs R0 /\ req R0 R.
Proof.
  intros G v R Hval Hty.
  remember (typ_Record R) as T eqn:HT.
  revert R HT Hval.
  induction Hty; intros R0 HT Hval;
    try discriminate;
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

(* ================================================================== *)
(* Progress (docs/semantics.md section 7).                              *)
(* ================================================================== *)

Lemma progress_mut :
  (forall G e T, typing G e T -> G = nil -> value e \/ exists e', step e e') /\
  (forall G fs R, field_typing G fs R -> G = nil ->
     rec_value fs \/ exists fs', step_fields fs fs').
Proof.
  apply typing_field_mutind.
  - (* T_Var *) intros G x s T Hu Hb Hi HG; subst. inversion Hb.
  - (* T_Num *) intros; left; auto.
  - (* T_True *) intros; left; auto.
  - (* T_False *) intros; left; auto.
  - (* T_Abs *) intros L G e T1 T2 Hbody IH HG; subst. left; auto.
  - (* T_App *) intros G e1 e2 T1 T2 Hty1 IH1 Hty2 IH2 HG; subst.
    right. destruct (IH1 eq_refl) as [Hv1 | [e1' Hs1]].
    + destruct (canon_arrow _ _ _ _ Hv1 Hty1) as [e0 Hev]; subst.
      destruct (IH2 eq_refl) as [Hv2 | [e2' Hs2]].
      * exists (open_exp_wrt_exp e0 e2). apply st_beta; auto.
      * exists (e_app (e_abs e0) e2'). apply st_app2; auto.
    + exists (e_app e1' e2). apply st_app1; auto.
  - (* T_Let *) intros L G e1 e2 T1 T2 Hty1 IH1 Hbody IH2 HG; subst.
    right. destruct (IH1 eq_refl) as [Hv1 | [e1' Hs1]].
    + exists (open_exp_wrt_exp e2 e1). apply st_letv; auto.
    + exists (e_let e1' e2). apply st_let1; auto.
  - (* T_Record *) intros G fs R Hft IH HG; subst.
    destruct (IH eq_refl) as [Hrv | [fs' Hs]].
    + left; auto.
    + right. exists (e_rec fs'). apply st_rec; auto.
  - (* T_Proj *) intros G e l T R Hty IH HG; subst.
    right. destruct (IH eq_refl) as [Hv | [e' Hs]].
    + destruct (canon_record _ _ _ Hv Hty) as [fs [R0 [Hev [Hrv [Hft Hreq]]]]]; subst.
      apply req_surface in Hreq. destruct Hreq as [T0 [rest [Hpi Hteq]]].
      destruct (field_lookup_some _ _ _ _ _ _ Hft Hpi) as [e0 [Hlook Hty0]].
      exists e0. apply st_projrec; auto.
    + exists (e_proj e' l). apply st_proj; auto.
  - (* T_Conv *) intros G e T T' Hty IH Hteq HG; subst.
    destruct (IH eq_refl) as [Hv | [e' Hs]]; [ left; auto | right; eauto ].
  - (* FT_nil *) intros; left; auto.
  - (* FT_cons *) intros G l e T fs R Hty IH1 Hft IH2 HG; subst.
    destruct (IH1 eq_refl) as [Hv | [e' Hs]].
    + destruct (IH2 eq_refl) as [Hrv | [fs' Hs']].
      * left; auto.
      * right. exists (fs_cons l e fs'). apply stf_cons; auto.
    + right. exists (fs_cons l e' fs). apply stf_here; auto.
Qed.

Theorem progress : forall e T,
  typing nil e T -> value e \/ exists e', step e e'.
Proof. intros e T H. apply (proj1 progress_mut nil e T H). reflexivity. Qed.

(* ================================================================== *)
(* Typing inversion up to conversion (the T-Conv "induction tax",       *)
(* docs/semantics.md section 9).  Each lemma peels any trailing          *)
(* conversions off a derivation whose subject has a known head.          *)
(* ================================================================== *)

Lemma app_inv : forall G e1 e2 T,
  typing G (e_app e1 e2) T ->
  exists A B, typing G e1 (typ_Arrow A B) /\ typing G e2 A /\ teq B T.
Proof.
  intros G e1 e2 T H. remember (e_app e1 e2) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_App *) inversion He; subst. exists T1, T2.
    repeat split; auto using teq_refl.
  - (* T_Conv *) destruct (IHtyping He) as [A [B [Hty1 [Hty2 Hb]]]].
    exists A, B. repeat split; try assumption. eauto using teq_trans.
Qed.

Lemma abs_inv : forall G e T,
  typing G (e_abs e) T ->
  exists (L : vars) T1 T2,
    (forall x, x `notin` L ->
       typing ((x ~ sch_mono T1) ++ G) (open_exp_wrt_exp e (e_fvar_f x)) T2) /\
    teq (typ_Arrow T1 T2) T.
Proof.
  intros G e T H. remember (e_abs e) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Abs *) inversion He; subst. exists L, T1, T2.
    split; auto using teq_refl.
  - (* T_Conv *) destruct (IHtyping He) as [L [T1 [T2 [Hbody Hteq]]]].
    exists L, T1, T2. split; try assumption. eauto using teq_trans.
Qed.

Lemma let_inv : forall G e1 e2 T,
  typing G (e_let e1 e2) T ->
  exists (L : vars) T1 T2,
    typing G e1 T1 /\
    (forall x, x `notin` L ->
       typing ((x ~ gen G T1) ++ G) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) /\
    teq T2 T.
Proof.
  intros G e1 e2 T H. remember (e_let e1 e2) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Let *) inversion He; subst. exists L, T1, T2.
    repeat split; auto using teq_refl.
  - (* T_Conv *) destruct (IHtyping He) as [L [T1 [T2 [Hty1 [Hbody Hteq]]]]].
    exists L, T1, T2. repeat split; try assumption. eauto using teq_trans.
Qed.

Lemma proj_inv : forall G e l T,
  typing G (e_proj e l) T ->
  exists T0 R, typing G e (typ_Record (row_Ext l T0 R)) /\ teq T0 T.
Proof.
  intros G e l T H. remember (e_proj e l) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Proj *) inversion He; subst. exists T, R.
    split; auto using teq_refl.
  - (* T_Conv *) destruct (IHtyping He) as [T0 [R [Hty Hteq]]].
    exists T0, R. split; try assumption. eauto using teq_trans.
Qed.

Lemma rec_inv : forall G fs T,
  typing G (e_rec fs) T ->
  exists R, field_typing G fs R /\ teq (typ_Record R) T.
Proof.
  intros G fs T H. remember (e_rec fs) as e0 eqn:He.
  induction H; try discriminate He.
  - (* T_Record *) inversion He; subst. exists R.
    split; auto using teq_refl.
  - (* T_Conv *) destruct (IHtyping He) as [R [Hft Hteq]].
    exists R. split; try assumption. eauto using teq_trans.
Qed.

(* ================================================================== *)
(* L6 -- term substitution.  These two are the only ADMITTED results in  *)
(* the development.  Each is the standard Hindley-Milner substitution     *)
(* lemma; neither is weakened in statement.  Their rigorous mechanization *)
(* needs type/row-substitution preservation (L5) together with weakening  *)
(* under binders, and the let case of each turns on generalization        *)
(* commuting with type substitution -- which requires capture-avoidance   *)
(* over the nat-indexed quantifier sets (docs/semantics.md section 10     *)
(* names L6b's interaction with L5 as the subtlest case, and ADR 0008     *)
(* budgets this HM substitution theory separately).                       *)
(*                                                                        *)
(* Progress toward closing these (issue #151) lives in GoatSubst.v, built *)
(* after this file.  Proved there, assumption-free: the type/row-subst    *)
(* algebra (ap_typ_ext/comp, inst_mono_eq); teq_ap (equivalence closed    *)
(* under substitution, i.e. L5's T-Conv case); L4 in two forms --         *)
(* typing_sch_equiv_ctx and typing_ftv_mono (the latter is exactly L6a's  *)
(* let case: dropping x makes gen more general with fewer free vars); and *)
(* typing_rename (L5 for any BIJECTIVE type/row-variable renaming, via    *)
(* inst_ren and gen_ren).                                                 *)
(*                                                                        *)
(* What remains before these two admits close:                           *)
(*  - General weakening under binders.  The var case of L6a/L6b needs the *)
(*    substituted value re-typed in the larger context; its let case must *)
(*    first freshen the let-generalized variables away from the inserted  *)
(*    context's free variables (otherwise generalization silently shrinks *)
(*    and the derivation breaks).  That freshening is a typing_rename by a *)
(*    bijection fixing a finite variable set -- a sub-development of its   *)
(*    own.  With weakening, L6a closes via typing_ftv_mono + inst_mono_eq. *)
(*  - For L6b additionally: L5 for a GENERAL instantiating substitution    *)
(*    (not a renaming), used to retype the value at an instance of its    *)
(*    generalization (the V cap ftv(G) = emptyset side condition makes the *)
(*    substitution fix G).  Because a scheme's quantifier sets are         *)
(*    arbitrary Props -- not decidable -- capture-avoiding substitution of *)
(*    an arbitrary context is not computable here, so this does not reduce *)
(*    to the renaming case.  A decidable (finite-list / metalib-atom-set)  *)
(*    quantifier-set representation -- the nat->atom refinement ADR 0008   *)
(*    flags as a later step -- would remove that obstruction.             *)
(* ================================================================== *)

(* L6a: monomorphic term substitution (for ST-Beta). *)
Lemma typing_subst : forall G x U e T u,
  typing ((x ~ sch_mono U) ++ G) e T ->
  typing G u U ->
  typing G (subst_exp u x e) T.
Admitted.

(* L6b: polymorphic term substitution (for ST-LetV); the side condition
   V \cap ftv(G) = emptyset of docs/semantics.md L6b holds because [gen]
   quantifies exactly ftv(T1) \ ftv(G). *)
Lemma typing_subst_poly : forall G x T1 e T2 v,
  typing ((x ~ gen G T1) ++ G) e T2 ->
  typing G v T1 ->
  typing G (subst_exp v x e) T2.
Admitted.

(* ================================================================== *)
(* Preservation (docs/semantics.md section 7).                          *)
(* ================================================================== *)

Scheme step_mut := Induction for step Sort Prop
with   step_fields_mut := Induction for step_fields Sort Prop.
Combined Scheme step_step_fields_mutind from step_mut, step_fields_mut.

Lemma preservation_mut :
  (forall e e', step e e' -> forall G T, typing G e T -> typing G e' T) /\
  (forall fs fs', step_fields fs fs' ->
     forall G R, field_typing G fs R -> field_typing G fs' R).
Proof.
  apply step_step_fields_mutind.
  - (* st_beta: (abs e) v --> open e v *)
    intros e v Hv G T Hty.
    apply app_inv in Hty. destruct Hty as [A [B [Habs [Harg Hbt]]]].
    apply abs_inv in Habs. destruct Habs as [L [A' [B' [Hbody Harr]]]].
    apply teq_Arrow_inv in Harr. destruct Harr as [A2 [B2 [Heq [HA HB]]]].
    inversion Heq; subst.
    pick fresh x for (L \u fv_exp e).
    assert (HxL : x `notin` L) by fsetdec.
    assert (Hxe : x `notin` fv_exp e) by fsetdec.
    (* v : A', by converting its A-typing along teq A A' *)
    assert (Hv' : typing G v A') by (eapply T_Conv; [ exact Harg | apply teq_sym; exact HA ]).
    assert (Hopen : typing G (subst_exp v x (open_exp_wrt_exp e (e_fvar_f x))) B')
      by (eapply typing_subst; [ apply Hbody; exact HxL | exact Hv' ]).
    rewrite <- subst_intro in Hopen by exact Hxe.
    eapply T_Conv; [ exact Hopen | ].
    eapply teq_trans; [ exact HB | exact Hbt ].
  - (* st_app1 *)
    intros e1 e1' e2 Hstep IH G T Hty.
    apply app_inv in Hty. destruct Hty as [A [B [Hty1 [Hty2 Hbt]]]].
    eapply T_Conv; [ eapply T_App; [ apply IH; exact Hty1 | exact Hty2 ] | exact Hbt ].
  - (* st_app2 *)
    intros v e2 e2' Hv Hstep IH G T Hty.
    apply app_inv in Hty. destruct Hty as [A [B [Hty1 [Hty2 Hbt]]]].
    eapply T_Conv; [ eapply T_App; [ exact Hty1 | apply IH; exact Hty2 ] | exact Hbt ].
  - (* st_letv: (let v e2) --> open e2 v *)
    intros v e2 Hv G T Hty.
    apply let_inv in Hty. destruct Hty as [L [T1 [T2 [Hty1 [Hbody Hteq]]]]].
    pick fresh x for (L \u fv_exp e2).
    assert (HxL : x `notin` L) by fsetdec.
    assert (Hxe : x `notin` fv_exp e2) by fsetdec.
    assert (Hopen : typing G (subst_exp v x (open_exp_wrt_exp e2 (e_fvar_f x))) T2)
      by (eapply typing_subst_poly; [ apply Hbody; exact HxL | exact Hty1 ]).
    rewrite <- subst_intro in Hopen by exact Hxe.
    eapply T_Conv; [ exact Hopen | exact Hteq ].
  - (* st_let1 *)
    intros e1 e1' e2 Hstep IH G T Hty.
    apply let_inv in Hty. destruct Hty as [L [T1 [T2 [Hty1 [Hbody Hteq]]]]].
    eapply T_Conv; [ eapply T_Let with (L := L) (T1 := T1);
                     [ apply IH; exact Hty1 | exact Hbody ] | exact Hteq ].
  - (* st_proj *)
    intros e e' l Hstep IH G T Hty.
    apply proj_inv in Hty. destruct Hty as [T0 [R [Hty0 Hteq]]].
    eapply T_Conv; [ eapply T_Proj; apply IH; exact Hty0 | exact Hteq ].
  - (* st_projrec *)
    intros fs l v Hrv Hlook G T Hty.
    apply proj_inv in Hty. destruct Hty as [T0 [R [Hrec Hteq]]].
    apply rec_inv in Hrec. destruct Hrec as [R' [Hft Hreq]].
    apply teq_Record_inv in Hreq. destruct Hreq as [R2 [Heq Hreq]].
    inversion Heq; subst.
    apply req_surface in Hreq. destruct Hreq as [T1 [rest [Hpi Hteq1]]].
    destruct (field_lookup_some _ _ _ _ _ _ Hft Hpi) as [v0 [Hlook0 Hty0]].
    assert (v0 = v) by congruence. subst v0.
    eapply T_Conv; [ exact Hty0 | ].
    eapply teq_trans; [ exact Hteq1 | exact Hteq ].
  - (* st_rec *)
    intros fs fs' Hstep IHf G T Hty.
    apply rec_inv in Hty. destruct Hty as [R [Hft Hteq]].
    eapply T_Conv; [ eapply T_Record; apply IHf; exact Hft | exact Hteq ].
  - (* stf_here *)
    intros l e e' fs Hstep IH G R Hft.
    inversion Hft; subst.
    eapply FT_cons; [ apply IH; eassumption | eassumption ].
  - (* stf_cons *)
    intros l v fs fs' Hv Hstep IHf G R Hft.
    inversion Hft; subst.
    eapply FT_cons; [ eassumption | apply IHf; eassumption ].
Qed.

Theorem preservation : forall G e e' T,
  typing G e T -> step e e' -> typing G e' T.
Proof. intros G e e' T Hty Hstep. eapply (proj1 preservation_mut); eauto. Qed.

(* ================================================================== *)
(* Soundness (docs/semantics.md section 7): a well-typed closed term     *)
(* never reaches a stuck state.                                           *)
(* ================================================================== *)

Theorem soundness : forall e T e',
  typing nil e T -> multistep e e' -> value e' \/ exists e'', step e' e''.
Proof.
  intros e T e' Hty Hms. revert T Hty.
  induction Hms as [ e | e1 e2 e3 Hstep Hms IH ]; intros T Hty.
  - (* refl *) apply progress with (T := T); exact Hty.
  - (* step *) apply IH with (T := T). eapply preservation; eauto.
Qed.

Corollary soundness_not_stuck : forall e T e',
  typing nil e T -> multistep e e' -> ~ stuck e'.
Proof.
  intros e T e' Hty Hms [Hnv Hns].
  destruct (soundness _ _ _ Hty Hms) as [Hv | [e'' Hstep]].
  - contradiction.
  - eapply Hns; exact Hstep.
Qed.
