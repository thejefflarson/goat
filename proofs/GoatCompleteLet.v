(* Completeness of algorithm W, stage 7.5, part L1: [gen_mono_let], the scheme
   comparison at a [let] as the induction states it (docs/design/phase7-proof-plan.md).

   The derivation's [T_Let] generalizes [S2 T'] over [pin_ctx Tm Gd] at the sorts
   [k] and kinds [rk]; the algorithm generalizes [T'] over [pin_ctx] of what
   [let_pin] gives, taken over its own context [Ga] (GoatInfer.v).  Given that
   [S2] respects the sorts and kinds ([kres], [rkres], with the environment the
   derivation's first premise lives in), sends the variables [Ga] keeps free
   to types over those [Gd] keeps free, and that the derivation's
   [lit_pinned] premise holds, the derivation's scheme is an instance of
   [S2] applied to the algorithm's. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatCompleteInst.
Require Import Goat.GoatCompleteMono.
Require Import Stdlib.Lists.List.
Import ListNotations.

Lemma let_pin_ftv : forall D e T a, a `in` ftv_typ (let_pin D e T) -> a `in` ftv_typ T.
Proof.
  intros D e T a H. unfold let_pin in H. destruct (let_open e); [ simpl in H; fsetdec | ].
  apply ftv_pin_of in H. apply lit_vars_in in H. tauto.
Qed.

Lemma let_pin_frv : forall D e T a, a `notin` frv_typ (let_pin D e T).
Proof.
  intros D e T a. unfold let_pin. destruct (let_open e); [ simpl; fsetdec | apply frv_pin_of ].
Qed.

Theorem gen_mono_let : forall (D Dal : denv) (S2 : sub) (Ga Gd : ctx) (Tm T' : typ) e
  (k : sort_fn) (rk : rkind_fn),
  OkS S2 -> frozen S2 Ga Gd -> even_ctx Ga -> EvT T' ->
  lit_pinned e (AtomSetImpl.diff (ftv_typ (apT S2 T')) (ftv_ctx (pin_ctx Tm Gd))) k ->
  kres Dal (extr (ext D (AtomSetImpl.diff (ftv_typ (apT S2 T')) (ftv_ctx (pin_ctx Tm Gd))) k)
                 (AtomSetImpl.diff (frv_typ (apT S2 T')) (frv_ctx (pin_ctx Tm Gd))) rk) (sT S2) ->
  rkres Dal (extr (ext D (AtomSetImpl.diff (ftv_typ (apT S2 T')) (ftv_ctx (pin_ctx Tm Gd))) k)
                  (AtomSetImpl.diff (frv_typ (apT S2 T')) (frv_ctx (pin_ctx Tm Gd))) rk) (sR S2) ->
  sch_le D (gen (pin_ctx Tm Gd) (apT S2 T') k rk)
           (apS S2 (gen_ren Dal (pin_ctx (let_pin Dal e T') Ga) T')).
Proof.
  intros D Dal S2 Ga Gd Tm T' e k rk HOk Hfz Hev HevT Hlit Hk Hr.
  pose proof (ftv_pin_ctx (let_pin Dal e T') Ga) as A1.
  pose proof (frv_pin_ctx (let_pin Dal e T') Ga) as A2.
  apply gen_mono; [ exact HOk | | | exact Hk | exact Hr ].
  - apply frozen_pin; [ exact Hfz | | ].
    + intros a Ha. destruct (let_open e) eqn:Eo.
      * unfold let_pin in Ha. rewrite Eo in Ha. simpl in Ha. fsetdec.
      * exact (let_pin_frozen D Dal S2 _ e T' k rk Eo Hlit Hk a Ha).
    + intros r Hr0. exfalso. apply (let_pin_frv Dal e T' r Hr0).
  - destruct HevT as [E1 E2]. destruct Hev as [H1 H2]. split.
    + intros a Ha. assert (Hu : a `in` ftv_typ (let_pin Dal e T') \/ a `in` ftv_ctx Ga) by fsetdec.
      destruct Hu as [Hu|Hu]; [ exact (E1 a (let_pin_ftv _ _ _ _ Hu)) | exact (H1 a Hu) ].
    + intros a Ha. assert (Hu : a `in` frv_typ (let_pin Dal e T') \/ a `in` frv_ctx Ga) by fsetdec.
      destruct Hu as [Hu|Hu]; [ exfalso; exact (let_pin_frv Dal e T' a Hu) | exact (H2 a Hu) ].
Qed.
