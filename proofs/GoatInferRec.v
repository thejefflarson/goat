(* What algorithm W needs to be sound at a recursive group (GoatInfer.v,
   [e_letrec]): the group is inferred with its name bound monomorphically to a
   row of fresh variables, the members' types are unified with those variables
   one by one ([unify_pw]), and the group's name is generalized for the body.
   These lemmas carry a derivation of the members across the unifier, across
   the renaming that generalizes, and across the name the body opens with. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatHM.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferTyp.
Require Import Goat.GoatInferRen.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferGen.
Require Import Stdlib.Lists.List.
Import ListNotations.

Lemma EvR_Empty : EvR row_Empty.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Lemma EvR_group_row : forall fs n, EvR (group_row fs n).
Proof.
  induction fs as [|l e rest IH]; intros n; simpl.
  - apply EvR_Empty.
  - apply EvR_ext; [ apply EvT_var, ev_ea | apply IH ].
Qed.

Lemma is_fn_group_sound : forall fs, is_fn_group fs = true -> fn_group fs.
Proof.
  induction fs as [|l e rest IH]; intros H; simpl in H.
  - constructor.
  - destruct e; try discriminate. constructor. apply IH. exact H.
Qed.

(* ---- unifying a group's members ---- *)

Inductive pw_teq : row -> row -> Prop :=
 | pw_nil : pw_teq row_Empty row_Empty
 | pw_cons : forall l T T' R R',
     teq T T' -> pw_teq R R' -> pw_teq (row_Ext l T R) (row_Ext l T' R').

Lemma pw_conv : forall G fs R R',
  field_typing G fs R -> pw_teq R R' -> field_typing G fs R'.
Proof.
  intros G fs R R' H. revert R'. induction H; intros R' Hp; inversion Hp; subst.
  - apply FT_nil. assumption.
  - eapply FT_cons; [ eapply T_Conv; eauto | eauto ].
Qed.

Lemma unify_pw_sound : forall f R1 R2 n s n',
  unify_pw f R1 R2 n = Some (s, n') -> EvR R1 -> EvR R2 ->
  OkS s /\ pw_teq (apR s R1) (apR s R2).
Proof.
  induction f as [|f IH]; intros R1 R2 n s n' H H1 H2; [discriminate|].
  cbn [unify_pw] in H.
  destruct R1 as [|r|l T R1']; destruct R2 as [|r2|l2 T2 R2']; try discriminate H.
  - inversion H; subst. split; [apply OkS_id | rewrite apR_id; apply pw_nil].
  - destruct (Nat.eqb l l2) eqn:Hl; [|discriminate].
    apply Nat.eqb_eq in Hl; subst l2.
    destruct (unify_t f T T2 n) as [[s1 n1]|] eqn:E1; [|discriminate].
    destruct (unify_pw f (apR s1 R1') (apR s1 R2') n1) as [[s2 n2]|] eqn:E2; [|discriminate].
    inversion H; subst; clear H.
    destruct (EvR_ext_inv _ _ _ H1) as [HT HR1].
    destruct (EvR_ext_inv _ _ _ H2) as [HT2 HR2].
    destruct ((proj1 (unify_sound f)) _ _ _ _ _ E1 HT HT2) as [Hs1 Hteq].
    destruct (IH _ _ _ _ _ E2 (EvR_ap s1 _ Hs1 HR1) (EvR_ap s1 _ Hs1 HR2)) as [Hs2 Hpw].
    split; [ apply OkS_comp; assumption | ].
    rewrite !apR_Ext. rewrite <- !apT_comp, <- !apR_comp.
    apply pw_cons; [ apply teq_apT; exact Hteq | exact Hpw ].
Qed.

(* ---- members under a substitution ---- *)

(* The members' derivation, in a context that binds the group's name to a
   monotype, survives a substitution of the algorithm. *)
Lemma fields_ap : forall s G p T0 fs R,
  OkS s -> WfCtx G ->
  field_typing ((p ~ sch_mono T0) ++ G) fs R ->
  field_typing ((p ~ sch_mono (apT s T0)) ++ apC s G) fs (apR s R).
Proof.
  intros s G p T0 fs R Hs HG Hty.
  pose proof (proj2 typing_uniq_mut _ _ _ Hty) as Hu0.
  apply uniq_cons_iff in Hu0. destruct Hu0 as [Hu Hp].
  pose proof Hs as Hs0. destruct Hs as [[A Hsup] _].
  apply (proj2 typing_tsubst_gen_mut _ fs R Hty (sT s) (sR s)
           ((p ~ sch_mono (apT s T0)) ++ apC s G) A).
  - constructor; [ apply uniq_apC; exact Hu | rewrite dom_apC; exact Hp ].
  - apply ctx_subst_cons; [ apply sch_subst_mono | ].
    intros x sc Hb. exists (apS s sc). split.
    + apply binds_apC; exact Hb.
    + apply sch_subst_apS; [ exact Hs0 | exact ((proj2 HG) _ _ Hb) ].
  - exact Hsup.
  - apply tr_compat_cons_mono. apply tr_compat_apC; [ exact Hs0 | exact HG ].
Qed.

(* A substitution that leaves the context alone, applied to the group's row. *)
Lemma fields_tsubst_fix : forall G p R fs st sr,
  field_typing ((p ~ sch_mono (typ_Record R)) ++ G) fs R ->
  (forall a, a `in` ftv_ctx G -> st a = typ_Var a) ->
  (forall r, r `in` frv_ctx G -> sr r = row_Var r) ->
  field_typing ((p ~ sch_mono (typ_Record (ap_row st sr R))) ++ G) fs (ap_row st sr R).
Proof.
  intros G p R fs st sr Hty Hfa Hfr.
  set (T := typ_Record R).
  set (st0 := fun a => if AtomSetImpl.mem a (ftv_typ T) then st a else typ_Var a).
  set (sr0 := fun r => if AtomSetImpl.mem r (frv_typ T) then sr r else row_Var r).
  assert (Heq : ap_typ st0 sr0 T = ap_typ st sr T).
  { apply ap_typ_ext.
    - intros a Ha. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ T)) eqn:Em;
        [reflexivity | apply AtomSetFacts.not_mem_iff in Em; contradiction].
    - intros r Hr. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ T)) eqn:Em;
        [reflexivity | apply AtomSetFacts.not_mem_iff in Em; contradiction]. }
  pose proof (proj2 typing_uniq_mut _ _ _ Hty) as Hu0.
  apply uniq_cons_iff in Hu0. destruct Hu0 as [Hu Hp].
  subst T. simpl in Heq. injection Heq as Heq.
  rewrite <- Heq.
  assert (HG : tr_compat st0 sr0 G G).
  { unfold tr_compat. repeat split.
    + intros a Ha. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ (typ_Record R))) eqn:Em.
      * rewrite (Hfa a Ha). simpl. fsetdec.
      * simpl. fsetdec.
    + intros a Ha. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ (typ_Record R))) eqn:Em.
      * rewrite (Hfa a Ha). simpl. fsetdec.
      * simpl. fsetdec.
    + intros r Hr. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ (typ_Record R))) eqn:Em.
      * rewrite (Hfr r Hr). simpl. fsetdec.
      * simpl. fsetdec.
    + intros r Hr. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ (typ_Record R))) eqn:Em.
      * rewrite (Hfr r Hr). simpl. fsetdec.
      * simpl. fsetdec. }
  assert (Hrow : ap_typ st0 sr0 (typ_Record R) = typ_Record (ap_row st0 sr0 R)) by reflexivity.
  pose proof (proj2 typing_tsubst_gen_mut _ fs R Hty st0 sr0
                ((p ~ sch_mono (ap_typ st0 sr0 (typ_Record R))) ++ G)
                (ftv_typ (typ_Record R) `union` frv_typ (typ_Record R))) as H.
  rewrite Hrow in H.
  apply H.
  - constructor; [ exact Hu | exact Hp ].
  - apply ctx_subst_cons; [ rewrite <- Hrow; apply sch_subst_mono | ].
    apply ctx_subst_fix.
    + intros a Ha. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ (typ_Record R)));
        [ apply Hfa; auto | reflexivity ].
    + intros r Hr. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ (typ_Record R)));
        [ apply Hfr; auto | reflexivity ].
  - split.
    + intros a Ha. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ (typ_Record R))) eqn:Em;
        [ apply AtomSetFacts.mem_iff in Em; exfalso; fsetdec | reflexivity ].
    + intros r Hr. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ (typ_Record R))) eqn:Em;
        [ apply AtomSetFacts.mem_iff in Em; exfalso; fsetdec | reflexivity ].
  - rewrite <- Hrow. apply tr_compat_cons_mono. exact HG.
Qed.

(* The renaming that generalizes the group's type, applied to its members. *)
Lemma fields_gen_ren : forall G p R fs,
  field_typing ((p ~ sch_mono (typ_Record R)) ++ G) fs R ->
  field_typing
    ((p ~ sch_mono (s_body (gen_ren G (typ_Record R)))) ++ G) fs
    (ap_row (rename_t (gen_vars_t G (typ_Record R))) (rename_r (gen_vars_r G (typ_Record R))) R).
Proof.
  intros G p R fs Hty.
  rewrite gen_body. simpl.
  apply fields_tsubst_fix; [ exact Hty | | ].
  - intros a Ha. unfold rename_t. destruct (in_dec Atom.eq_dec a (gen_vars_t G (typ_Record R))) as [Hin|Hin];
      [ apply In_la in Hin; destruct Hin as [_ Hin]; contradiction | reflexivity ].
  - intros a Ha. unfold rename_r. destruct (in_dec Atom.eq_dec a (gen_vars_r G (typ_Record R))) as [Hin|Hin];
      [ apply In_lr in Hin; destruct Hin as [_ Hin]; contradiction | reflexivity ].
Qed.

(* The members derived with the group's name opened at one fresh name hold at
   any other. *)
Lemma fields_rename_var : forall G x y sc fs R,
  field_typing ((x ~ sc) ++ G) (open_fields_wrt_exp fs (e_fvar_f x)) R ->
  x `notin` fv_fields fs -> y `notin` dom G -> y <> x ->
  field_typing ((y ~ sc) ++ G) (open_fields_wrt_exp fs (e_fvar_f y)) R.
Proof.
  intros G x y sc fs R Hty Hx Hy Hne.
  pose proof (proj2 (typing_rename_var_mut x y sc G) _ _ _ Hty nil eq_refl) as H.
  simpl in H. rewrite (subst_intro_fields fs x (e_fvar_f y) Hx).
  apply H. simpl. fsetdec.
Qed.
