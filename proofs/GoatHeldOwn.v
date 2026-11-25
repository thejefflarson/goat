(* A [let] whose bound term holds an equation on a presence of the context
   (ADR 0033 amendment, issue 667).

   The presence of such an equation is settled by a later statement of the
   enclosing function, so the [let] cannot decide it.  The algorithm
   generalizes the bound term as if every such presence were absent, and holds
   [absent_req] in place of the equations: a requirement that the presence end
   up [Bool].  [V_let_own] proves the [let]: for a step that satisfies the
   requirements, the presences are [Bool] already, so the bound term is typed
   after the substitution [t] that makes them so ([bool_sub]), at a state where
   its equations are vacuous, and generalizing there is the generalization the
   algorithm computed. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
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
Require Import Goat.GoatInferRec.
Require Import Goat.GoatElab.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatClose.
Require Import Goat.GoatInferW.
Require Import Goat.GoatInferSound.
Require Import Goat.GoatHeldSound.
Require Import Goat.GoatHeldV.
Require Import Goat.GoatHeldLet.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Small facts                                                          *)
(* ------------------------------------------------------------------ *)

Lemma apT_agree : forall s s' T,
  (forall a, sT s a = sT s' a) -> (forall r, sR s r = sR s' r) -> apT s T = apT s' T.
Proof.
  intros s s' T Ht Hr. unfold apT. apply ap_typ_ext; [ intros a _; apply Ht | intros r _; apply Hr ].
Qed.

Lemma apC_agree : forall s s' G,
  (forall a, sT s a = sT s' a) -> (forall r, sR s r = sR s' r) -> apC s G = apC s' G.
Proof.
  intros s s' G Ht Hr. unfold apC. apply map_ext. intros [x sc]. cbn [fst snd].
  rewrite (apT_agree s s' _ Ht Hr). reflexivity.
Qed.

(* A step that makes the listed presences [Bool] is unchanged by first
   making them [Bool]. *)
Lemma bool_sub_absorbed : forall Sg ps,
  (forall p, In p ps -> sT Sg p = typ_Bool) ->
  (forall a, sT (scomp Sg (bool_sub ps)) a = sT Sg a) /\
  (forall r, sR (scomp Sg (bool_sub ps)) r = sR Sg r).
Proof.
  intros Sg ps H. destruct (bool_sub_agree Sg ps H) as [Ht Hr]. split.
  - intros a. symmetry. exact (Ht a).
  - intros r. symmetry. exact (Hr r).
Qed.

Lemma apT_Bool_inv : forall s T, apT s T = typ_Bool -> T = typ_Bool \/ exists a, T = typ_Var a /\ sT s a = typ_Bool.
Proof.
  intros s T H. destruct T; cbn [apT ap_typ] in H; try discriminate H.
  - left. reflexivity.
  - right. exists a. split; [ reflexivity | exact H ].
Qed.

Lemma sat_Bool_b : forall D D' k, sat D k typ_Bool -> sat_b D' k typ_Bool = true.
Proof. intros D D' k H. cbn [sat] in H. destruct H as [-> | ->]; reflexivity. Qed.

Lemma OkS_bool_sub : forall ps, (forall p, In p ps -> ev p) -> OkS (bool_sub ps).
Proof.
  induction ps as [|p ps IH]; intros Hev; cbn [bool_sub].
  - exact OkS_id.
  - exact (OkS_comp _ _ (IH (fun q Hq => Hev q (or_intror Hq)))
             (OkS_sbT p typ_Bool (Hev p (or_introl eq_refl)) EvT_Bool I)).
Qed.

Lemma own_atoms_ev : forall H, HOk H -> forall p, In p (own_atoms H) -> ev p.
Proof.
  intros H HH p Hp. unfold own_atoms in Hp. apply in_flat_map in Hp as (h & Hh & Hp).
  unfold HOk in HH. rewrite Forall_forall in HH. destruct (HH h Hh) as (Hpe & _).
  destruct (h_pres h) as [| | | | | | | a | | | ] eqn:Ep; try (destruct Hp; fail).
  destruct Hp as [<- | []]. destruct Hpe as [Hpe _]. apply Hpe. simpl. fsetdec.
Qed.

Lemma own_sub_OkS : forall d Ho, OkS d -> HOk Ho -> OkS (own_sub d Ho).
Proof.
  intros d Ho Hd HH. unfold own_sub. apply OkS_bool_sub. exact (own_atoms_ev _ (HOk_ap _ _ Hd HH)).
Qed.

Lemma HOk_filter : forall (P : heq -> bool) H, HOk H -> HOk (filter P H).
Proof.
  intros P H. unfold HOk. rewrite !Forall_forall. intros HH h Hh.
  apply filter_In in Hh as [Hh _]. exact (HH h Hh).
Qed.

Lemma HOk_absent_req : forall H, HOk H -> HOk (map absent_req H).
Proof.
  intros H. unfold HOk. rewrite !Forall_forall. intros HH h' Hh'.
  apply in_map_iff in Hh' as [h [<- Hh]].
  destruct (HH h Hh) as (Hp & _ & _ & _). cbn [absent_req h_pres h_fld h_val h_rest].
  refine (conj Hp (conj EvT_Bool (conj EvT_Unit _))).
  apply EvR_ext; [ exact EvT_Unit | exact EvR_Empty ].
Qed.

(* ------------------------------------------------------------------ *)
(* The [let] over a bound term with owned equations                     *)
(* ------------------------------------------------------------------ *)

Lemma V_let_own : forall k f D n G us1 T1 H1 d D1 n1 x e2 s2 D2 n2 T2 H2,
  V G D n us1 T1 H1 ->
  dis k f D (filter (fun h => negb (owned_h G h)) H1) n = Some (d, D1, n1) ->
  HOk H1 -> WfCtx G -> DOk D n -> EvT T1 -> is_gen_value us1 = true ->
  x `notin` dom G -> lce 0 e2 -> Good D1 n1 s2 D2 n2 ->
  V (apC s2 ((x ~ gen_ren D1 (pin_ctx (let_pin D1 us1 (apT (own_sub d (filter (owned_h G) H1)) (apT d T1)))
                                      (apC (own_sub d (filter (owned_h G) H1)) (apC d G)))
                             (apT (own_sub d (filter (owned_h G) H1)) (apT d T1))) ++ apC d G))
    D2 n2 e2 T2 H2 ->
  V (apC s2 (apC d G)) D2 n2 (e_let us1 (cl 0 x e2)) T2
    (apH s2 (map absent_req (apH d (filter (owned_h G) H1))) ++ H2).
Proof.
  intros k f D n G us1 T1 H1 d D1 n1 x e2 s2 D2 n2 T2 H2 HV Ed HH HG HD HT1 Hgv Hx Hlc Gd2 HV2 S D'' n'' Hg Hs.
  set (Ho := filter (owned_h G) H1) in *.
  set (Hq := apH d Ho) in *.
  set (t := own_sub d Ho) in *.
  assert (Ht : t = bool_sub (own_atoms Hq)) by reflexivity.
  apply Sol_app in Hs as [Hsq Hs2].
  assert (HHf : HOk (filter (fun h => negb (owned_h G h)) H1)) by (apply HOk_filter; exact HH).
  destruct (dis_sound k f D _ n d D1 n1 Ed HD HHf) as (Gdd & Hsold).
  pose proof Gdd as (_ & Hsd & HD1 & _).
  pose proof (Good_comp _ _ _ _ _ _ _ _ Gd2 Hg) as Gsg.
  set (sg := scomp S s2) in *.
  assert (HHq : HOk Hq) by (apply HOk_ap; [ exact Hsd | apply HOk_filter; exact HH ]).
  (* the step satisfies the requirements *)
  apply Sol_apH in Hsq. change (scomp S s2) with sg in Hsq.
  assert (Hreq : forall h, In h Hq -> apT sg (h_pres h) = typ_Bool).
  { intros h Hh. unfold Sol in Hsq. rewrite Forall_forall in Hsq.
    destruct (Hsq (absent_req h) (in_map _ _ _ Hh)) as [Hb | Hc].
    - exact Hb.
    - cbn [apE absent_req h_fld h_val] in Hc.
      change (apT sg typ_Bool) with typ_Bool in Hc. change (apT sg typ_Unit) with typ_Unit in Hc.
      apply teqD_Bool_inv in Hc. discriminate Hc. }
  assert (Hat : forall p, In p (own_atoms Hq) -> sT sg p = typ_Bool).
  { intros p Hp. unfold own_atoms in Hp. apply in_flat_map in Hp as (h & Hh & Hp).
    destruct (h_pres h) as [| | | | | | | a | | | ] eqn:Ep; try (destruct Hp; fail).
    destruct Hp as [<- | []]. pose proof (Hreq h Hh) as E. rewrite Ep in E. exact E. }
  assert (Hev : forall p, In p (own_atoms Hq) -> ev p) by exact (own_atoms_ev _ HHq).
  (* t is a step from the state where the equations were discharged *)
  assert (Hsat : forallb (fun p => sat_b D1 (D1 p) typ_Bool) (own_atoms Hq) = true).
  { rewrite forallb_forall. intros p Hp.
    pose proof (Good_kres _ _ _ _ _ Gsg p) as Hk. rewrite (Hat p Hp) in Hk.
    exact (sat_Bool_b _ _ _ Hk). }
  destruct (bool_sub_ok D1 (own_atoms Hq) Hev Hsat) as (Hs0 & Hk0 & _).
  pose proof (Good_unify D1 n1 t n1 Hs0 Hk0 (le_n n1) HD1) as Gt.
  pose proof (Good_comp _ _ _ _ _ _ _ _ Gdd Gt) as Gtd.
  (* the bound term solves its equations at the composite *)
  assert (Hsol : Sol D1 (scomp t d) H1).
  { unfold Sol. rewrite Forall_forall. intros h Hh.
    destruct (owned_h G h) eqn:Eo.
    - left. cbn [apE h_pres]. rewrite <- apT_comp.
      assert (HIn : In (apE d h) Hq) by (apply in_map; apply filter_In; split; assumption).
      pose proof (Hreq _ HIn) as Hb. cbn [apE h_pres] in Hb.
      change (apT t (apT d (h_pres h)) = typ_Bool).
      destruct (apT_Bool_inv sg _ Hb) as [E | (a & E & Ea)].
      + rewrite E. reflexivity.
      + rewrite E. cbn [apT ap_typ]. change (sT t a = typ_Bool).
        apply bool_sub_in. unfold own_atoms. apply in_flat_map. exists (apE d h). split; [ exact HIn | ].
        cbn [apE h_pres]. rewrite E. left. reflexivity.
    - unfold Sol in Hsold. rewrite Forall_forall in Hsold.
      assert (HInf : In h (filter (fun h => negb (owned_h G h)) H1)).
      { apply filter_In. split; [ exact Hh | rewrite Eo; reflexivity ]. }
      rewrite <- apE_comp. exact (solves1_ap _ _ _ _ _ _ Gt (Hsold h HInf)). }
  pose proof (HV (scomp t d) D1 n1 Gtd Hsol) as Hty1.
  rewrite <- apC_comp, <- apT_comp in Hty1.
  (* generalize at that state, apply the later step *)
  pose proof (WfCtx_ap d _ Hsd HG) as HGd.
  pose proof (WfCtx_ap t _ Hs0 HGd) as HGt.
  pose proof (EvT_ap t _ Hs0 (EvT_ap d _ Hsd HT1)) as HT1t.
  assert (Hxt : x `notin` dom (apC t (apC d G))).
  { pose proof (dom_apC t (apC d G)). pose proof (dom_apC d G). fsetdec. }
  pose proof (HV2 S D'' n'' Hg Hs2) as Hty2. rewrite apC_comp in Hty2. change (scomp S s2) with sg in Hty2.
  rewrite apC_app, apC_single in Hty2.
  assert (Hag : apC sg (apC t (apC d G)) = apC sg (apC d G)).
  { rewrite apC_comp. apply apC_agree; [ intros a | intros r ];
      [ exact (proj1 (bool_sub_absorbed sg _ Hat) a) | exact (proj2 (bool_sub_absorbed sg _ Hat) r) ]. }
  assert (Hty2' : typing D'' (apC sg ((x ~ gen_ren D1 (pin_ctx (let_pin D1 us1 (apT t (apT d T1)))
                                                        (apC t (apC d G))) (apT t (apT d T1)))
                                       ++ apC t (apC d G))) e2 (apT S T2)).
  { rewrite apC_app, apC_single, Hag. exact Hty2. }
  pose proof (let_typing_gen D1 n1 (apC t (apC d G)) us1 (apT t (apT d T1)) x e2 sg D'' n'' (apT S T2)
                HGt HD1 HT1t Hgv Hxt Hty1 Hlc Gsg Hty2') as Hres.
  rewrite Hag in Hres. rewrite apC_comp. exact Hres.
Qed.
