(* Completeness of algorithm W, stage 7.5, part L1: [gen_mono_let], the scheme
   comparison at a [let] as the induction states it (docs/design/phase7-proof-plan.md).

   The derivation's [T_Let] generalizes [S2 T'] over [pin_ctx Tm Gd] at the sorts
   [k] and kinds [rk]; the algorithm generalizes [T'] over [pin_ctx] of what
   [let_pin] gives, taken over its own context [Ga] (GoatInfer.v).  Given that
   [S2] respects the sorts and kinds ([sat], [rkok], with the environment the
   derivation's first premise lives in) at the atoms of [T'], fixes the atoms the
   algorithm quantifies, sends the variables [Ga] keeps free to types over those
   [Gd] keeps free, and that the derivation's [lit_pinned] premise holds, the
   derivation's scheme is an instance of [S2] applied to the algorithm's.  The
   comparison carries [PEv] with it: an instance whose images are [PEv] is an
   instance of the algorithm's scheme whose images are [PEv]. *)

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

(* The variables the algorithm keeps free at a [let], the context's and the
   pin's, go to variables the derivation keeps free. *)
Lemma let_frozen : forall (D Dal : denv) (S2 : sub) (Ga Gd : ctx) (Tm T' : typ) e
  (k : sort_fn) (rk : rkind_fn),
  frozen S2 Ga Gd ->
  lit_pinned e (AtomSetImpl.diff (ftv_typ (apT S2 T')) (ftv_ctx (pin_ctx Tm Gd))) k ->
  (forall b, b `in` ftv_typ T' ->
     sat (extr (ext D (AtomSetImpl.diff (ftv_typ (apT S2 T')) (ftv_ctx (pin_ctx Tm Gd))) k)
               (AtomSetImpl.diff (frv_typ (apT S2 T')) (frv_ctx (pin_ctx Tm Gd))) rk) (dsort Dal b) (sT S2 b)) ->
  frozen S2 (pin_ctx (let_pin Dal e T') Ga) (pin_ctx Tm Gd).
Proof.
  intros D Dal S2 Ga Gd Tm T' e k rk Hfz Hlit Hk.
  apply frozen_pin; [ exact Hfz | | ].
  - intros a Ha. destruct (let_open e) eqn:Eo.
    + unfold let_pin in Ha. rewrite Eo in Ha. simpl in Ha. fsetdec.
    + exact (let_pin_frozen D Dal S2 _ e T' k rk Eo Hlit Hk a Ha).
  - intros r Hr0. exfalso. apply (let_pin_frv Dal e T' r Hr0).
Qed.

Theorem gen_mono_let : forall (D Dal : denv) (S2 : sub) (Ga Gd : ctx) (Tm T' : typ) e
  (k : sort_fn) (rk : rkind_fn),
  frozen S2 Ga Gd ->
  (forall b, b `in` s_tq (gen_ren Dal (pin_ctx (let_pin Dal e T') Ga) T') -> sT S2 b = typ_Var b) ->
  (forall r, r `in` s_rq (gen_ren Dal (pin_ctx (let_pin Dal e T') Ga) T') -> sR S2 r = row_Var r) ->
  (forall a, a `in` ftv_ctx (pin_ctx (let_pin Dal e T') Ga) -> EvT (sT S2 a)) ->
  (forall r, r `in` frv_ctx (pin_ctx (let_pin Dal e T') Ga) -> EvR (sR S2 r)) ->
  (forall a, a `in` ftv_typ T' -> PEv (sT S2 a)) ->
  (forall r, r `in` frv_typ T' -> EvR (sR S2 r) /\ lcr 0 (sR S2 r)) ->
  lit_pinned e (AtomSetImpl.diff (ftv_typ (apT S2 T')) (ftv_ctx (pin_ctx Tm Gd))) k ->
  (forall b, b `in` ftv_typ T' ->
     sat (extr (ext D (AtomSetImpl.diff (ftv_typ (apT S2 T')) (ftv_ctx (pin_ctx Tm Gd))) k)
               (AtomSetImpl.diff (frv_typ (apT S2 T')) (frv_ctx (pin_ctx Tm Gd))) rk) (dsort Dal b) (sT S2 b)) ->
  (forall r, r `in` frv_typ T' ->
     rkok (extr (ext D (AtomSetImpl.diff (ftv_typ (apT S2 T')) (ftv_ctx (pin_ctx Tm Gd))) k)
                (AtomSetImpl.diff (frv_typ (apT S2 T')) (frv_ctx (pin_ctx Tm Gd))) rk) (drk Dal r) (sR S2 r)) ->
  sch_leP D (gen (pin_ctx Tm Gd) (apT S2 T') k rk)
            (apS S2 (gen_ren Dal (pin_ctx (let_pin Dal e T') Ga) T')).
Proof.
  intros D Dal S2 Ga Gd Tm T' e k rk Hfz HFt HFr HEt HEr HPt HPr Hlit Hk Hr.
  refine (gen_mono D Dal S2 _ _ T' k rk _ HFt HFr HEt HEr HPt HPr Hk Hr).
  exact (let_frozen D Dal S2 Ga Gd Tm T' e k rk Hfz Hlit Hk).
Qed.
