(* Toward closing the two canonical HM lemmas (issue #151): the capture-avoiding
   type/row substitution of a scheme, and its central property -- substituting a
   scheme capture-avoidingly preserves its instance set ([casch_inst]).  This is
   the re-chosen-instance step that the L5 [T-Var] leaf and instantiation turn
   on, and the piece GoatBij's freshening was building toward.

   Like GoatBij, this file is a building block and does NOT by itself discharge
   either admit in GoatSubst.v.  The remaining obstruction is [T-Let]: closing it
   needs the let-generalized variables to be fresh with respect to the other
   context schemes' quantifiers (so that generalization commutes with the
   substitution), which the deterministic [gen] over a set-of-atoms scheme
   representation does not supply on its own -- it needs a derivation-level
   freshness/well-formedness invariant (or a cofinite [T-Let]).  See the report
   on #151 for the detailed analysis. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatBij.
Require Import Coq.Lists.List.
Import ListNotations.

(* ap_typ by a substitution that fixes a type's free variables is the identity. *)
Lemma ap_typ_fix : forall st sr T,
  (forall a, a `in` ftv_typ T -> st a = typ_Var a) ->
  (forall r, r `in` frv_typ T -> sr r = row_Var r) ->
  ap_typ st sr T = T.
Proof.
  intros st sr T Ht Hr.
  transitivity (ap_typ idt idr T).
  - apply ap_typ_ext; auto.
  - apply ap_typ_pointwise_id; reflexivity.
Qed.

Lemma ap_row_fix : forall st sr R,
  (forall a, a `in` ftv_row R -> st a = typ_Var a) ->
  (forall r, r `in` frv_row R -> sr r = row_Var r) ->
  ap_row st sr R = R.
Proof.
  intros st sr R Ht Hr.
  transitivity (ap_row idt idr R).
  - apply (proj2 ap_ext_mut); auto.
  - apply (proj2 ap_pointwise_id_mut); reflexivity.
Qed.

(* Capture-avoiding type/row substitution of a scheme by [st,sr], using an
   involutive renaming [g,gr] that moves the scheme's quantifiers to atoms
   fresh for the substitution (so [st,sr] fix them and never capture into
   them).  The body is the substituted, quantifier-renamed monotype. *)
Definition casch (st:tsub) (sr:rsub) (g gr:atom->atom) (s:scheme) : scheme :=
  Sch (amap g (s_tq s)) (amap gr (s_rq s))
      (ap_typ st sr (ren_typ g gr (s_body s))).

(* The key lemma: capture-avoiding substitution preserves instances. *)
Lemma casch_inst : forall st sr g gr s,
  (forall a, g (g a) = a) -> (forall r, gr (gr r) = r) ->
  (forall a, a `in` ftv_sch s -> g a = a) ->
  (forall r, r `in` frv_sch s -> gr r = r) ->
  (forall a, a `in` amap g (s_tq s) -> st a = typ_Var a) ->
  (forall r, r `in` amap gr (s_rq s) -> sr r = row_Var r) ->
  (forall a b, b `in` ftv_sch s -> a `in` amap g (s_tq s) -> a `notin` ftv_typ (st b)) ->
  (forall a r, r `in` frv_sch s -> a `in` amap g (s_tq s) -> a `notin` ftv_row (sr r)) ->
  (forall p b, b `in` ftv_sch s -> p `in` amap gr (s_rq s) -> p `notin` frv_typ (st b)) ->
  (forall p r, r `in` frv_sch s -> p `in` amap gr (s_rq s) -> p `notin` frv_row (sr r)) ->
  forall W, inst W s -> inst (ap_typ st sr W) (casch st sr g gr s).
Proof.
  intros st sr g gr s Hgi Hgri Hgf Hgrf Hfx1 Hfx2 Hnc1 Hnc2 Hnc3 Hnc4 W [pt [pr [Hpt [Hpr HW]]]].
  exists (fun b => if AtomSetImpl.mem b (amap g (s_tq s)) then ap_typ st sr (pt (g b)) else typ_Var b),
         (fun p => if AtomSetImpl.mem p (amap gr (s_rq s)) then ap_row st sr (pr (gr p)) else row_Var p).
  split; [| split].
  - intros a Ha. cbn [casch s_tq] in Ha.
    destruct (AtomSetImpl.mem a (amap g (s_tq s))) eqn:Em;
      [ apply AtomSetFacts.mem_iff in Em; contradiction | reflexivity ].
  - intros p Hp. cbn [casch s_rq] in Hp.
    destruct (AtomSetImpl.mem p (amap gr (s_rq s))) eqn:Em;
      [ apply AtomSetFacts.mem_iff in Em; contradiction | reflexivity ].
  - cbn [casch s_body]. rewrite HW. unfold ren_typ. rewrite !ap_typ_comp.
    apply ap_typ_ext.
    + intros a Ha. unfold tcomp, rt. cbn [ap_typ].
      destruct (AtomSetImpl.mem a (s_tq s)) eqn:Eq.
      * apply AtomSetFacts.mem_iff in Eq.
        assert (Hga : g a `in` amap g (s_tq s)) by (apply amap_in; exists a; auto).
        rewrite (Hfx1 (g a) Hga). cbn [ap_typ].
        destruct (AtomSetImpl.mem (g a) (amap g (s_tq s))) eqn:Em.
        -- rewrite Hgi. reflexivity.
        -- apply AtomSetFacts.not_mem_iff in Em. contradiction.
      * apply AtomSetFacts.not_mem_iff in Eq.
        assert (Hafsch : a `in` ftv_sch s) by (unfold ftv_sch; apply AtomSetImpl.diff_3; auto).
        rewrite (Hpt a Eq). cbn [ap_typ]. rewrite (Hgf a Hafsch).
        symmetry. apply ap_typ_fix.
        -- intros b Hb. destruct (AtomSetImpl.mem b (amap g (s_tq s))) eqn:Em; [|reflexivity].
           apply AtomSetFacts.mem_iff in Em. exfalso. apply (Hnc1 b a Hafsch Em). exact Hb.
        -- intros q Hq. destruct (AtomSetImpl.mem q (amap gr (s_rq s))) eqn:Em; [|reflexivity].
           apply AtomSetFacts.mem_iff in Em. exfalso. apply (Hnc3 q a Hafsch Em). exact Hq.
    + intros r Hr. unfold rcomp, rr. cbn [ap_row].
      destruct (AtomSetImpl.mem r (s_rq s)) eqn:Eq.
      * apply AtomSetFacts.mem_iff in Eq.
        assert (Hgr : gr r `in` amap gr (s_rq s)) by (apply amap_in; exists r; auto).
        rewrite (Hfx2 (gr r) Hgr). cbn [ap_row].
        destruct (AtomSetImpl.mem (gr r) (amap gr (s_rq s))) eqn:Em.
        -- rewrite Hgri. reflexivity.
        -- apply AtomSetFacts.not_mem_iff in Em. contradiction.
      * apply AtomSetFacts.not_mem_iff in Eq.
        assert (Hrfsch : r `in` frv_sch s) by (unfold frv_sch; apply AtomSetImpl.diff_3; auto).
        rewrite (Hpr r Eq). cbn [ap_row]. rewrite (Hgrf r Hrfsch).
        symmetry. apply ap_row_fix.
        -- intros b Hb. destruct (AtomSetImpl.mem b (amap g (s_tq s))) eqn:Em; [|reflexivity].
           apply AtomSetFacts.mem_iff in Em. exfalso. apply (Hnc2 b r Hrfsch Em). exact Hb.
        -- intros q Hq. destruct (AtomSetImpl.mem q (amap gr (s_rq s))) eqn:Em; [|reflexivity].
           apply AtomSetFacts.mem_iff in Em. exfalso. apply (Hnc4 q r Hrfsch Em). exact Hq.
Qed.
