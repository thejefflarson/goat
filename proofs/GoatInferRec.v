(* What algorithm W needs to be sound at a recursive group (GoatInfer.v,
   [e_letrec]): the group is inferred with its name bound monomorphically to a
   row of fresh variables, the members' types are unified with those variables
   one by one ([unify_grp]), and the group's name is generalized for the body.
   These lemmas carry a derivation of the members across the unifier, across
   the renaming that generalizes, and across the name the body opens with. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatHM.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferTyp.
Require Import Goat.GoatInferRen.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferGen.
Require Import Stdlib.Lists.List.
From Stdlib Require Import Lia.
Import ListNotations.

Lemma EvR_Empty : EvR row_Empty.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Lemma EvR_group_row : forall fs n, EvR (group_row fs n).
Proof.
  induction fs as [|l e rest IH|l e rest IH]; intros n; simpl.
  - apply EvR_Empty.
  - apply EvR_ext; [ apply EvT_var, ev_ea | apply IH ].
  - apply EvR_ext; [ apply EvT_var, ev_ea | apply IH ].
Qed.

Lemma is_fn_group_sound : forall fs, is_fn_group fs = true -> fn_group fs.
Proof.
  induction fs as [|l e rest IH|l e rest IH]; intros H; simpl in H.
  - constructor.
  - destruct e; try discriminate. constructor. apply IH. exact H.
  - discriminate.
Qed.

(* ---- unifying a group's members ---- *)

Inductive pw_teq : row -> row -> Prop :=
 | pw_nil : pw_teq row_Empty row_Empty
 | pw_cons : forall l T T' R R',
     teq T T' -> pw_teq R R' -> pw_teq (row_Ext l T R) (row_Ext l T' R').

Lemma pw_conv : forall D G fs R R',
  field_typing D G fs R -> pw_teq R R' -> field_typing D G fs R'.
Proof.
  intros D G fs R R' H. revert R'. induction H; intros R' Hp; inversion Hp; subst.
  - apply FT_nil. assumption.
  - eapply FT_cons; [ eapply T_Conv; eauto | eauto ].
  - eapply FT_meth; [ eapply T_Conv; eauto | eauto ].
Qed.

(* ---- members under a substitution ---- *)

(* The members' derivation, in a context that binds the group's name to a
   monotype, survives a substitution of the algorithm. *)
Lemma fields_ap : forall D D' s G p T0 fs R,
  OkS s -> WfCtx G -> (exists S, supp_ok D S) -> (exists S', supp_ok D' S') ->
  kres D D' (sT s) ->
  field_typing D ((p ~ sch_mono T0) ++ G) fs R ->
  field_typing D' ((p ~ sch_mono (apT s T0)) ++ apC s G) fs (apR s R).
Proof.
  intros D D' s G p T0 fs R Hs HG [S HS] [S' HS'] Hk Hty.
  pose proof (proj2 typing_uniq_mut _ _ _ _ Hty) as Hu0.
  apply uniq_cons_iff in Hu0. destruct Hu0 as [Hu Hp].
  pose proof Hs as Hs0. destruct Hs as [[A Hsup] _].
  apply (proj2 typing_tsubst_gen_mut D _ fs R Hty (sT s) (sR s)
           ((p ~ sch_mono (apT s T0)) ++ apC s G) D' A S S').
  - constructor; [ apply uniq_apC; exact Hu | rewrite dom_apC; exact Hp ].
  - exact HS.
  - exact HS'.
  - exact Hk.
  - apply ctx_subst_cons; [ apply sch_subst_mono | ].
    intros x sc Hb. exists (apS s sc). split.
    + apply binds_apC; exact Hb.
    + apply sch_subst_apS; [ exact Hs0 | exact ((proj2 HG) _ _ Hb) ].
  - exact Hsup.
  - apply tr_compat_cons_mono. apply tr_compat_apC; [ exact Hs0 | exact HG ].
Qed.

(* The same for fields typed in a context with no binding of their own. *)
Lemma fields_ap0 : forall D D' s G fs R,
  OkS s -> WfCtx G -> (exists S, supp_ok D S) -> (exists S', supp_ok D' S') ->
  kres D D' (sT s) ->
  field_typing D G fs R -> field_typing D' (apC s G) fs (apR s R).
Proof.
  intros D D' s G fs R Hs [Hu Hw] [S HS] [S' HS'] Hk Hty.
  pose proof Hs as Hs0.
  destruct Hs as [[A Hsup] [Ht [Hrw [Hfx Hfxr]]]].
  apply (proj2 typing_tsubst_gen_mut D G fs R Hty (sT s) (sR s) (apC s G) D' A S S').
  - apply uniq_apC; exact Hu.
  - exact HS.
  - exact HS'.
  - exact Hk.
  - intros x sc Hb. exists (apS s sc). split.
    + apply binds_apC; exact Hb.
    + apply sch_subst_apS; [exact Hs0 | exact (Hw _ _ Hb)].
  - exact Hsup.
  - apply tr_compat_apC; [ exact Hs0 | exact (conj Hu Hw) ].
Qed.

(* A substitution that leaves the context alone, applied to the group's row. *)
Lemma fields_tsubst_fix : forall D D' S S' G p R fs st sr,
  field_typing D ((p ~ sch_mono (typ_Record R)) ++ G) fs R ->
  supp_ok D S -> supp_ok D' S' -> kres D D' st -> kres D D' idt ->
  (forall a, a `in` ftv_ctx G -> st a = typ_Var a) ->
  (forall r, r `in` frv_ctx G -> sr r = row_Var r) ->
  lc_sub st sr ->
  field_typing D' ((p ~ sch_mono (typ_Record (ap_row st sr R))) ++ G) fs (ap_row st sr R).
Proof.
  intros D D' S S' G p R fs st sr Hty HS HS' Hk Hid Hfa Hfr Hlc.
  set (T := typ_Record R).
  set (st0 := fun a => if AtomSetImpl.mem a (ftv_typ T) then st a else typ_Var a).
  set (sr0 := fun r => if AtomSetImpl.mem r (frv_typ T) then sr r else row_Var r).
  assert (Heq : ap_typ st0 sr0 T = ap_typ st sr T).
  { apply ap_typ_ext.
    - intros a Ha. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ T)) eqn:Em;
        [reflexivity | apply AtomSetFacts.not_mem_iff in Em; contradiction].
    - intros r Hr. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ T)) eqn:Em;
        [reflexivity | apply AtomSetFacts.not_mem_iff in Em; contradiction]. }
  assert (Hlc0 : lc_sub st0 sr0).
  { split.
    - intros a. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ T)); [ exact (proj1 Hlc a) | exact I ].
    - intros r. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ T)); [ exact (proj2 Hlc r) | exact I ]. }
  pose proof (proj2 typing_uniq_mut _ _ _ _ Hty) as Hu0.
  apply uniq_cons_iff in Hu0. destruct Hu0 as [Hu Hp].
  assert (Hk0 : kres D D' st0).
  { intros a. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ T)); [ apply Hk | apply Hid ]. }
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
  pose proof (proj2 typing_tsubst_gen_mut D _ fs R Hty st0 sr0
                ((p ~ sch_mono (ap_typ st0 sr0 (typ_Record R))) ++ G) D'
                (ftv_typ (typ_Record R) `union` frv_typ (typ_Record R)) S S') as H.
  rewrite Hrow in H.
  apply H.
  - constructor; [ exact Hu | exact Hp ].
  - exact HS.
  - exact HS'.
  - exact Hk0.
  - apply ctx_subst_cons; [ rewrite <- Hrow; apply sch_subst_mono | ].
    apply ctx_subst_fix; [ | | exact Hlc0 ].
    + intros a Ha. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ (typ_Record R)));
        [ apply Hfa; auto | reflexivity ].
    + intros r Hr. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ (typ_Record R)));
        [ apply Hfr; auto | reflexivity ].
  - split; [ | split; [ | exact Hlc0 ] ].
    + intros a Ha. unfold st0. destruct (AtomSetImpl.mem a (ftv_typ (typ_Record R))) eqn:Em;
        [ apply AtomSetFacts.mem_iff in Em; exfalso; fsetdec | reflexivity ].
    + intros r Hr. unfold sr0. destruct (AtomSetImpl.mem r (frv_typ (typ_Record R))) eqn:Em;
        [ apply AtomSetFacts.mem_iff in Em; exfalso; fsetdec | reflexivity ].
  - rewrite <- Hrow. apply tr_compat_cons_mono. exact HG.
Qed.

(* Extending the environment on odd atoms only refines it. *)
Lemma kres_ext_odd : forall D n V k,
  DOk D n -> (forall a, a `in` V -> od a) -> kres D (ext D V k) idt.
Proof.
  intros D n V k HD Hodd a. unfold idt. simpl.
  destruct (AtomSetImpl.mem a V) eqn:Em.
  - apply AtomSetFacts.mem_iff in Em. rewrite (ext_in _ _ _ _ Em).
    rewrite (DOk_odd D n a HD (Hodd a Em)). apply finer_any.
  - rewrite ext_out; [ apply finer_refl | apply AtomSetFacts.not_mem_iff; exact Em ].
Qed.

(* The renaming that generalizes the group's type, applied to its members. *)
Lemma fields_gen_ren : forall D n G p R fs,
  DOk D n ->
  field_typing D ((p ~ sch_mono (typ_Record R)) ++ G) fs R ->
  field_typing (ext D (s_tq (gen_ren D G (typ_Record R))) (s_sk (gen_ren D G (typ_Record R))))
    ((p ~ sch_mono (s_body (gen_ren D G (typ_Record R)))) ++ G) fs
    (ap_row (rename_t (gen_vars_t G (typ_Record R))) (rename_r (gen_vars_r G (typ_Record R))) R).
Proof.
  intros D n G p R fs HD Hty.
  rewrite gen_body. simpl.
  destruct (DOk_supp D n HD) as [S HS].
  apply fields_tsubst_fix with (D := D) (S := S) (S' := S `union` s_tq (gen_ren D G (typ_Record R))).
  - exact Hty.
  - exact HS.
  - apply supp_ok_ext_set. exact HS.
  - apply (kres_rename D G (typ_Record R) n HD).
  - apply (kres_ext_odd D n). exact HD. intros a Ha. exact (gen_ren_od_t D G (typ_Record R) a Ha).
  - intros a Ha. unfold rename_t. destruct (in_dec Atom.eq_dec a (gen_vars_t G (typ_Record R))) as [Hin|Hin];
      [ apply In_la in Hin; destruct Hin as [_ Hin]; contradiction | reflexivity ].
  - intros a Ha. unfold rename_r. destruct (in_dec Atom.eq_dec a (gen_vars_r G (typ_Record R))) as [Hin|Hin];
      [ apply In_lr in Hin; destruct Hin as [_ Hin]; contradiction | reflexivity ].
  - apply lc_sub_rename.
Qed.

(* The members derived with the group's name opened at one fresh name hold at
   any other. *)
Lemma fields_rename_var : forall D G x y sc fs R,
  field_typing D ((x ~ sc) ++ G) (open_fields_wrt_exp fs (e_fvar_f x)) R ->
  x `notin` fv_fields fs -> y `notin` dom G -> y <> x ->
  field_typing D ((y ~ sc) ++ G) (open_fields_wrt_exp fs (e_fvar_f y)) R.
Proof.
  intros D G x y sc fs R Hty Hx Hy Hne.
  pose proof (proj2 (typing_rename_var_mut x y sc G) _ _ _ _ Hty nil eq_refl) as H.
  simpl in H. rewrite (subst_intro_fields fs x (e_fvar_f y) Hx).
  apply H. simpl. fsetdec.
Qed.
