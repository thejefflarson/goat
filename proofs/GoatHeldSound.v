(* The discharge of held equations is sound, and the library of statements the
   algorithm's soundness proof is built from (ADR 0033 amendment, issue 667).

   [dis_sound]: a run of [dis] is a [Good] step whose substitution solves the
   equations it was given.

   [V Gs D n e T H] says [e] has type [T] in every extension of the algorithm's
   state [(D, n)] by a [Good] step [S] that solves the equations [H] still held.
   The algorithm's soundness statement for a subterm is a [V]: a type is
   derivable once the held equations are solved, and not before.  Each lemma
   below states a typing rule or a proof step of the soundness proof over [V],
   so that a later substitution enters as a bound variable. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatHeld.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferTyp.
Require Import Goat.GoatInferRen.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferGen.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatInferW.
Require Import Goat.GoatInferSound.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Equations under substitution                                         *)
(* ------------------------------------------------------------------ *)

(* Every type an equation mentions is even: what [unify_tD_sound] asks of the
   two sides it unifies. *)
Definition HOk (H : list heq) : Prop :=
  Forall (fun h => EvT (h_pres h) /\ EvT (h_fld h) /\ EvT (h_val h) /\ EvR (h_rest h)) H.

Lemma HOk_ap : forall s H, OkS s -> HOk H -> HOk (apH s H).
Proof.
  intros s H Hs. unfold HOk, apH. rewrite Forall_map. apply Forall_impl.
  intros h (H1 & H2 & H3 & H4). cbn [apE h_pres h_fld h_val h_rest].
  exact (conj (EvT_ap s _ Hs H1) (conj (EvT_ap s _ Hs H2) (conj (EvT_ap s _ Hs H3) (EvR_ap s _ Hs H4)))).
Qed.

Lemma apE_comp : forall s2 s1 h, apE s2 (apE s1 h) = apE (scomp s2 s1) h.
Proof.
  intros s2 s1 [l p y T R]. unfold apE; cbn [h_lbl h_pres h_fld h_val h_rest].
  rewrite !apT_comp, apR_comp. reflexivity.
Qed.

Lemma apH_comp : forall s2 s1 H, apH s2 (apH s1 H) = apH (scomp s2 s1) H.
Proof.
  intros s2 s1 H. unfold apH. rewrite map_map. apply map_ext. intros h. apply apE_comp.
Qed.

Lemma apH_app : forall s H1 H2, apH s (H1 ++ H2) = apH s H1 ++ apH s H2.
Proof. intros. unfold apH. apply map_app. Qed.

Lemma Sol_app : forall D S H1 H2, Sol D S (H1 ++ H2) <-> Sol D S H1 /\ Sol D S H2.
Proof. intros. unfold Sol. apply Forall_app. Qed.

Lemma Sol_nil : forall D S, Sol D S nil.
Proof. intros. constructor. Qed.

(* The equations solved by [S] stay solved under the same step applied to the
   equations: [S] solves [apH t H] exactly when [S o t] solves [H]. *)
Lemma Sol_apH : forall D S t H, Sol D S (apH t H) <-> Sol D (scomp S t) H.
Proof.
  intros D S t H. unfold Sol, apH. rewrite Forall_map. split; apply Forall_impl;
    intros h Hh; [ rewrite <- apE_comp; exact Hh | rewrite apE_comp; exact Hh ].
Qed.

Lemma solves1_ap : forall D n s D' n' h, Good D n s D' n' -> solves1 D h -> solves1 D' (apE s h).
Proof.
  intros D n s D' n' h Hg [Hb | Ht]; unfold solves1; cbn [apE h_pres h_fld h_val].
  - left. rewrite Hb. reflexivity.
  - right. exact (lift_teqD _ _ _ _ _ _ _ Hg Ht).
Qed.

Lemma Sol_ap : forall D n s D' n' S H, Good D n s D' n' -> Sol D S H -> Sol D' (scomp s S) H.
Proof.
  intros D n s D' n' S H Hg. unfold Sol. apply Forall_impl. intros h Hh.
  rewrite <- apE_comp. exact (solves1_ap _ _ _ _ _ _ Hg Hh).
Qed.

Lemma is_bool_true : forall T, is_bool T = true -> T = typ_Bool.
Proof. intros T H. destruct T; try discriminate H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The discharge is sound                                               *)
(* ------------------------------------------------------------------ *)

Lemma bool_sub_var : forall p, apT (bool_sub (p :: nil)) (typ_Var p) = typ_Bool.
Proof.
  intros p. unfold apT, bool_sub, scomp, sbT; simpl. unfold tcomp.
  destruct (Atom.eq_dec p p) as [_|N]; [ reflexivity | exfalso; apply N; reflexivity ].
Qed.

Lemma dis_nil : forall k f D n, dis (S k) f D nil n = Some (sid, D, n).
Proof. reflexivity. Qed.

Lemma dis_top_nil : forall f D T n, dis_top f D T nil n = Some (D, T).
Proof. reflexivity. Qed.

Lemma dis_sound : forall k f D H n d D' n',
  dis k f D H n = Some (d, D', n') -> DOk D n -> HOk H ->
  Good D n d D' n' /\ Sol D' d H.
Proof.
  induction k as [|k IH]; intros f D H n d D' n' E HD HH.
  - cbn [dis] in E. destruct H; [ | discriminate E ]. inversion E; subst.
    exact (conj (Good_id _ _ HD) (Sol_nil _ _)).
  - cbn [dis] in E. destruct H as [|h H']; [ inversion E; subst; exact (conj (Good_id _ _ HD) (Sol_nil _ _)) | ].
    inversion HH as [|? ? Hh HH']; subst.
    destruct Hh as (Hp & Hy & Hv & Hr).
    destruct (is_bool (h_pres h)) eqn:Eb.
    + destruct (IH _ _ _ _ _ _ _ E HD HH') as (Hg & Hs).
      refine (conj Hg (Forall_cons _ _ Hs)).
      left. cbn [apE h_pres]. rewrite (is_bool_true _ Eb). reflexivity.
    + destruct (unify_tD f D (h_fld h) (h_val h) n) as [[[s1 D1] n1]|] eqn:Eu.
      * destruct (dis k f D1 (apH s1 H') n1) as [[[s2 D2] n2]|] eqn:Ed; [ | discriminate E ].
        inversion E; subst; clear E.
        destruct ((proj1 (unify_tD_sound f)) _ _ _ _ _ _ _ Eu HD Hy Hv) as (Hs1 & Ht1 & Hg1).
        pose proof (GoodU_Good _ _ _ _ _ HD Hg1) as Gd1.
        destruct (IH _ _ _ _ _ _ _ Ed (Good_dok _ _ _ _ _ Gd1) (HOk_ap s1 _ Hs1 HH')) as (Gd2 & Hsol2).
        refine (conj (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) _).
        apply Forall_cons.
        -- right. cbn [apE h_fld h_val].
           pose proof (lift_teqD _ _ _ _ _ _ _ Gd2 Ht1) as Ht2.
           rewrite !apT_comp in Ht2. exact Ht2.
        -- apply Sol_apH in Hsol2. exact Hsol2.
      * destruct (h_pres h) as [| | | | | | | p | | | ] eqn:Ep; try discriminate E.
        destruct (clash_d D (h_fld h) (h_val h) && sat_b D (D p) typ_Bool && rlacksD D (h_lbl h) (h_rest h))
          eqn:Ec; [ | discriminate E ].
        apply Bool.andb_true_iff in Ec as [Ec _]. apply Bool.andb_true_iff in Ec as [_ Hsat].
        destruct (dis k f D (apH (bool_sub (p :: nil)) H') n) as [[[s2 D2] n2]|] eqn:Ed; [ | discriminate E ].
        inversion E; subst; clear E.
        assert (Hev : forall q, In q (p :: nil) -> ev q).
        { intros q [<-|[]]. destruct Hp as [Hp _]. apply Hp. simpl. fsetdec. }
        destruct (bool_sub_ok D (p :: nil) Hev ltac:(cbn [forallb]; rewrite Hsat; reflexivity)) as (Hs0 & Hk0 & _).
        pose proof (Good_unify D n _ n Hs0 Hk0 (le_n n) HD) as Gd1.
        destruct (IH _ _ _ _ _ _ _ Ed HD (HOk_ap _ _ Hs0 HH')) as (Gd2 & Hsol2).
        refine (conj (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) _).
        apply Forall_cons.
        -- left. cbn [apE h_pres]. rewrite Ep.
           rewrite <- apT_comp. change (apT s2 (apT (bool_sub (p :: nil)) (typ_Var p)) = typ_Bool). rewrite bool_sub_var. reflexivity.
        -- apply Sol_apH in Hsol2. exact Hsol2.
Qed.
