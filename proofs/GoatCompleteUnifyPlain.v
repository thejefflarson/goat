(* Completeness of algorithm W, stage 7.6j: the plain unifier ([unify_t],
   [unify_r]) on the closed fragment (docs/design/phase7-proof-plan.md).

   The tag-group arm of [unify_tD] hands the payload to the plain unifier, so
   completeness of [unify_tD] on a group needs completeness of [unify_t] on its
   payload.  The fragment, the substitutions ([Res]) and the induction are
   those of [GoatCompleteUnify.v], with [drop_abs] where the environment-reading
   unifier has [nfR D]: on a closed row of plain fields there is no absent entry
   to drop, so [drop_abs] is the identity and the proof is the same.  The
   hypotheses are plain: [teq] of the images, not [teqD].

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatCompleteFuel.
Require Import Goat.GoatCompleteRows.
Require Import Goat.GoatCompleteUnify.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Lists.List.
Import ListNotations.

Lemma drop_abs_crow : forall b R, crow b R -> drop_abs R = R.
Proof.
  intros b R. induction R; simpl; try tauto. intros [_ HR]. rewrite (IHR HR). reflexivity.
Qed.

Lemma unify_t_var_nonvar : forall b S (D D1 : denv) a T (n : nat),
  (b = true -> forall c, D c = k_Any) -> kres D D1 (sT S) ->
  cp b T -> (forall v, T <> typ_Var v) -> teq (sT S a) (apT S T) ->
  exists s, Res b S s /\ Stable (fun f => unify_t f D (typ_Var a) T n = Some (s, D, n)).
Proof.
  intros b S D D1 a T n Hs Hk HT Hv Heq.
  pose proof (bind_prop_complete b S D D1 a T n Hs Hk HT Hv Heq) as E.
  exists (scomp (sbT a T) (scomp sid sid)). split; [ exact (Res_bind b S a T HT Heq) | ].
  exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  destruct T; try (exfalso; exact (Hv _ eq_refl)); exact E.
Qed.

Lemma unify_t_nonvar_var : forall b S (D D1 : denv) a T (n : nat),
  (b = true -> forall c, D c = k_Any) -> kres D D1 (sT S) ->
  cp b T -> (forall v, T <> typ_Var v) -> teq (apT S T) (sT S a) ->
  exists s, Res b S s /\ Stable (fun f => unify_t f D T (typ_Var a) n = Some (s, D, n)).
Proof.
  intros b S D D1 a T n Hs Hk HT Hv Heq.
  apply teq_sym in Heq.
  pose proof (bind_prop_complete b S D D1 a T n Hs Hk HT Hv Heq) as E.
  exists (scomp (sbT a T) (scomp sid sid)). split; [ exact (Res_bind b S a T HT Heq) | ].
  exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
  destruct T; try (exfalso; exact (Hv _ eq_refl)); exact E.
Qed.

Lemma unify_t_var_var : forall b S (D : denv) a a' (n : nat), teq (sT S a) (sT S a') ->
  exists s, Res b S s /\ Stable (fun f => unify_t f D (typ_Var a) (typ_Var a') n = Some (s, D, n)).
Proof.
  intros b S D a a' n Heq. destruct (Atom.eq_dec a a') as [->|Hne].
  - exists sid. split; [ apply Res_sid | exists 1; intros f Hf; destruct f as [|f]; [ lia | ] ].
    cbn [unify_t]. destruct (Atom.eq_dec a' a'); [ reflexivity | congruence ].
  - destruct (finer_b (D a') (D a)) eqn:Ef.
    + exists (sbT a (typ_Var a')). split; [ exact (Res_sbT b S a (typ_Var a') I Heq) | ].
      exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
      cbn [unify_t]. destruct (Atom.eq_dec a a'); [ congruence | ]. rewrite Ef. reflexivity.
    + exists (sbT a' (typ_Var a)). split; [ exact (Res_sbT b S a' (typ_Var a) I (teq_sym _ _ Heq)) | ].
      exists 1. intros f Hf. destruct f as [|f]; [ lia | ].
      cbn [unify_t]. destruct (Atom.eq_dec a a'); [ congruence | ]. rewrite Ef. reflexivity.
Qed.

Lemma unify_t_scalar_same : forall b S (D : denv) c (n : nat),
  (c = typ_Int \/ c = typ_Float \/ c = typ_Bool \/ c = typ_Unit \/ c = typ_String) ->
  exists s, Res b S s /\ Stable (fun f => unify_t f D c c n = Some (s, D, n)).
Proof.
  intros b S D c n Hc. exists sid. split; [ apply Res_sid | exists 1; intros f Hf ].
  destruct f as [|f]; [ lia | ].
  destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; reflexivity.
Qed.

(* A type of the fragment is its own normal form: it has no presence entry to
   drop, whatever the environment. *)
Ltac nv := intros ? E; discriminate E.

Theorem unify_t_complete_aux : forall b S (D D1 : denv),
  (b = true -> forall c, D c = k_Any) -> kres D D1 (sT S) -> forall m,
  (forall T1 T2 n, cp b T1 -> cp b T2 -> tsz (apT S T1) < m ->
     teq (apT S T1) (apT S T2) ->
     exists s, Res b S s /\ Stable (fun f => unify_t f D T1 T2 n = Some (s, D, n))) /\
  (forall R1 R2 n, crow b R1 -> crow b R2 -> rsz (apR S R1) < m ->
     req (apR S R1) (apR S R2) ->
     exists s, Res b S s /\ Stable (fun f => unify_r f D R1 R2 n = Some (s, D, n))).
Proof.
  intros b S D D1 Hs Hk. induction m as [|m IH]; [ split; intros; lia | ].
  destruct IH as [IHt IHr]. split.
  - (* types *)
    intros T1 T2 n C1 C2 Hlt Hteq.
    destruct T1 as [ | | | | | A B | R | a | i | B1 | w A1 ]; try (simpl in C1; contradiction);
    destruct T2 as [ | | | | | A' B' | R' | a' | i' | B1' | w' A1' ];
      try (simpl in C2; contradiction);
    try (exfalso; pose proof (teq_thead _ _ Hteq) as Ht; unfold apT in Ht;
         cbn [ap_typ thead_tag] in Ht; discriminate Ht).
    all: try (apply unify_t_scalar_same; tauto).
    all: try (apply unify_t_var_nonvar with (D1 := D1); [ exact Hs | exact Hk | exact C2 | nv | exact Hteq ]).
    all: try (apply unify_t_nonvar_var with (D1 := D1); [ exact Hs | exact Hk | exact C1 | nv | exact Hteq ]).
    + (* Arrow, Arrow *)
      destruct C1 as [CA CB], C2 as [CA' CB'].
      rewrite apT_Arrow in Hlt. simpl in Hlt.
      rewrite !apT_Arrow in Hteq.
      destruct (teq_Arrow_inv _ _ _ Hteq) as (X & Y & EX & H1 & H2).
      injection EX as <- <-.
      destruct (IHt A A' n CA CA' ltac:(lia) H1) as (s1 & Hr1 & E1).
      destruct Hr1 as [Hc1 Hf1]. pose proof (conj Hc1 Hf1 : Res b S s1) as Hr1.
      pose proof (fac_ap b S s1 Hc1 Hf1) as [FT _].
      pose proof (FT B CB) as FB. pose proof (FT B' CB') as FB'.
      destruct (IHt (apT s1 B) (apT s1 B') n
                  ((proj1 (cp_ap b s1 Hc1)) _ CB) ((proj1 (cp_ap b s1 Hc1)) _ CB')
                  ltac:(rewrite <- (teq_tsz _ _ FB); lia)
                  (teq_trans _ _ _ (teq_sym _ _ FB) (teq_trans _ _ _ H2 FB')))
        as (s2 & Hr2 & E2).
      exists (scomp s2 s1). split; [ exact (Res_comp b S s1 s2 Hr1 Hr2) | ].
      eapply Stable_mono; [ | exact (Stable_below _ (Stable_and _ _ E1 E2)) ].
      intros [|f] Hf; [ contradiction | ]. destruct Hf as [Ha Hb].
      cbn [unify_t]. rewrite Ha, Hb. reflexivity.
    + (* Record, Record *)
      destruct C1 as [Hb CR], C2 as [_ CR'].
      rewrite apT_Record in Hlt. simpl in Hlt.
      rewrite !apT_Record in Hteq.
      destruct (teq_Record_inv _ _ Hteq) as (X & EX & H1). injection EX as <-.
      destruct (IHr R R' n CR CR' ltac:(lia) H1) as (s & Hr & E).
      exists s. split; [ exact Hr | ].
      eapply Stable_mono; [ | exact (Stable_below _ E) ].
      intros [|f] Hf; [ contradiction | ]. cbn [unify_t].
      rewrite (drop_abs_crow b R CR), (drop_abs_crow b R' CR'). exact Hf.
    + (* Var, Var *)
      apply unify_t_var_var. exact Hteq.
  - (* rows *)
    intros R1 R2 n C1 C2 Hlt Hreq.
    destruct R1 as [ | r | l T R1' | l P T R1' ]; try (simpl in C1; contradiction);
    destruct R2 as [ | q | l2 T2 R2' | l2 P2 T2 R2' ]; try (simpl in C2; contradiction).
    + (* Empty, Empty *)
      exists sid. split; [ apply Res_sid | exists 1; intros f Hf; destruct f as [|f]; [ lia | reflexivity ] ].
    + (* Empty, Ext *)
      exfalso. pose proof (req_pi _ _ Hreq l2) as H. rewrite pi_apR_ext in H.
      change (apR S row_Empty) with (row_Empty) in H. simpl in H. inversion H.
    + (* Ext, Empty *)
      exfalso. pose proof (req_pi _ _ Hreq l) as H. rewrite pi_apR_ext in H.
      change (apR S row_Empty) with (row_Empty) in H. simpl in H. inversion H.
    + (* Ext, Ext *)
      destruct C1 as [CT CR1], C2 as [CT2 CR2].
      remember (row_Ext l2 T2 R2') as R2 eqn:ER2.
      assert (CR2f : crow b R2) by (subst R2; simpl; tauto).
      assert (Hx2 : cext R2) by exact (crow_cext b R2 CR2f).
      assert (HxY : cext (apR S R2)) by exact (cext_ap S R2 Hx2).
      assert (Hx1 : cext R1') by exact (crow_cext b R1' CR1).
      pose proof (req_pi _ _ Hreq l) as Hpl. rewrite pi_apR_ext in Hpl.
      destruct (pi l (apR S R2)) as [|B rest] eqn:Epi; [ inversion Hpl | ].
      inversion Hpl as [|? ? ? ? Hh Ht].
      destruct (get_l l (apR S R2)) as [B0|] eqn:Eg;
        [ | pose proof (pi_get_none _ _ HxY Eg) as Hn; rewrite Hn in Epi; discriminate Epi ].
      destruct (pi_get_some _ _ _ HxY Eg) as [Hp Hm]. rewrite Hp in Epi.
      injection Epi as EB Hrest. subst B0.
      rewrite (get_l_ap S l R2 Hx2) in Eg.
      destruct (get_l l R2) as [T'|] eqn:Eg2; [ | discriminate Eg ].
      simpl in Eg. injection Eg as <-.
      pose proof (crow_get b l R2 T' CR2f Eg2) as CT'.
      pose proof (crow_rm b l R2 CR2f) as CRm.
      assert (Hpi_aux : forall k, k <> l -> Forall2 teq (pi k (apR S R1')) (pi k (apR S R2))).
      { intros k Hne. pose proof (req_pi _ _ Hreq k) as Hq. rewrite apR_Ext in Hq. cbn [pi] in Hq.
        destruct (Nat.eqb k l) eqn:E; [ apply Nat.eqb_eq in E; congruence | exact Hq ]. }
      assert (Hrq : req (apR S R1') (apR S (rm_l l R2))).
      { apply req_of_pi; [ exact (cext_ap S _ Hx1) | exact (cext_ap S _ (cext_rm l R2 Hx2)) | ].
        rewrite <- (rm_l_ap S l R2 Hx2). intros k. destruct (Nat.eq_dec k l) as [->|Hne].
        - rewrite Hrest. exact Ht.
        - rewrite (Hm k Hne). exact (Hpi_aux k Hne). }
      rewrite apR_Ext in Hlt. simpl in Hlt.
      destruct (IHt T T' n CT CT' ltac:(lia) Hh) as (s1 & [Hc1 Hf1] & E1).
      pose proof (conj Hc1 Hf1 : Res b S s1) as Hr1.
      pose proof (fac_ap b S s1 Hc1 Hf1) as [_ FR].
      pose proof (FR R1' CR1) as FR1. pose proof (FR (rm_l l R2) CRm) as FR2.
      destruct (IHr (apR s1 R1') (apR s1 (rm_l l R2)) n
                  (proj2 (cp_ap b s1 Hc1) _ CR1) (proj2 (cp_ap b s1 Hc1) _ CRm)
                  ltac:(rewrite <- (req_rsz _ _ FR1); lia)
                  (req_trans _ _ _ (req_sym _ _ FR1) (req_trans _ _ _ Hrq FR2)))
        as (s2 & Hr2 & E3).
      exists (scomp s2 (scomp s1 (scomp sid sid))). split.
      { apply Res_comp; [ apply Res_comp; [ apply Res_comp; apply Res_sid | exact Hr1 ] | exact Hr2 ]. }
      assert (E0 : Stable (fun f => unify_t f D (apT sid typ_Unit) typ_Unit n = Some (sid, D, n))).
      { exists 1. intros [|f] Hf; [ lia | ]. rewrite apT_id. reflexivity. }
      assert (E1' : Stable (fun f => unify_t f D (apT sid (apT sid T)) (apT sid T') n = Some (s1, D, n))).
      { eapply Stable_mono; [ | exact E1 ]. intros f Hf. rewrite !apT_id. exact Hf. }
      assert (E3' : Stable (fun f => unify_r f D (drop_abs (apR s1 (apR sid (apR sid R1'))))
                                       (drop_abs (apR s1 (apR sid (rm_l l R2)))) n = Some (s2, D, n))).
      { eapply Stable_mono; [ | exact E3 ]. intros f Hf. rewrite !apR_id.
        rewrite (drop_abs_crow b _ (proj2 (cp_ap b s1 Hc1) _ CR1)),
                (drop_abs_crow b _ (proj2 (cp_ap b s1 Hc1) _ CRm)). exact Hf. }
      eapply Stable_mono; [ | exact (Stable_below _ (Stable_and _ _ E0 (Stable_and _ _ E1' E3'))) ].
      intros [|f] Hf; [ contradiction | ]. destruct Hf as (Hu0 & Hu1 & Hu3).
      pose proof (rewrite_row_found l (side_av (row_Ext l T R1')) D R2 n T' Hx2 Eg2) as Erw.
      subst R2. cbn [unify_r row_head]. rewrite Erw. cbn iota beta. rewrite Hu0. cbn iota beta.
      rewrite Hu1. cbn iota beta. rewrite Hu3. reflexivity.
Qed.

Theorem unify_t_complete : forall b S (D D1 : denv) T1 T2 n,
  (b = true -> forall c, D c = k_Any) -> kres D D1 (sT S) ->
  cp b T1 -> cp b T2 -> teq (apT S T1) (apT S T2) ->
  exists s, Res b S s /\ Stable (fun f => unify_t f D T1 T2 n = Some (s, D, n)).
Proof.
  intros b S D D1 T1 T2 n Hs Hk C1 C2 Hteq.
  exact (proj1 (unify_t_complete_aux b S D D1 Hs Hk (Datatypes.S (tsz (apT S T1))))
           T1 T2 n C1 C2 (Nat.lt_succ_diag_r _) Hteq).
Qed.

Theorem unify_r_complete : forall b S (D D1 : denv) R1 R2 n,
  (b = true -> forall c, D c = k_Any) -> kres D D1 (sT S) ->
  crow b R1 -> crow b R2 -> req (apR S R1) (apR S R2) ->
  exists s, Res b S s /\ Stable (fun f => unify_r f D R1 R2 n = Some (s, D, n)).
Proof.
  intros b S D D1 R1 R2 n Hs Hk C1 C2 Hreq.
  exact (proj2 (unify_t_complete_aux b S D D1 Hs Hk (Datatypes.S (rsz (apR S R1))))
           R1 R2 n C1 C2 (Nat.lt_succ_diag_r _) Hreq).
Qed.
