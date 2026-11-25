(* The recursive types algorithm W builds are guarded (phase 5, stage 4,
   part 4; ADR 0037, decision 3).

   [infer_guarded]: every recursive type inside a type the algorithm returns
   has a guarded body ([mg], GoatGuard.v).  A guarded body is what [fold] and
   [unfold] ask ([T_Fold], [T_Unfold]) and what makes the unfoldings of a
   recursive type a regular tree, so the types W returns can be read as the
   checker's recursive types and compared to them.

   The proof follows the algorithm.  Every substitution it builds has [mg]
   images and closed ones ([gsub]).  The knot-tying unifier gets that by
   construction: [bind_k] checks the type it binds, so [unify_k_gsub] needs no
   hypothesis on its arguments.  [unify_t] binds only what it is given, so
   [unify_t_gsub] asks its arguments to be [mg], and so does every use of it:
   the types in the context, and every type the algorithm builds from them,
   stay [mg]. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatUnrollEqb.
Require Import Goat.GoatKnot.
Require Import Goat.GoatGuard.
Require Import Goat.GoatInferKnot.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatInferW.
Require Import Stdlib.Lists.List.
Import ListNotations.

Definition mg_ctx (G : ctx) : Prop :=
  forall x s, In (x, s) G -> mg (s_body s).

Lemma mg_apC : forall s G, gsub s -> mg_ctx G -> mg_ctx (apC s G).
Proof.
  intros s G Hs HG x sc Hin. unfold apC in Hin.
  apply in_map_iff in Hin. destruct Hin as [[y sc0] [Heq Hin]].
  injection Heq as <- <-. simpl. apply mg_apT; [ exact Hs | exact (HG y sc0 Hin) ].
Qed.

Lemma mg_cons : forall x sc G, mg (s_body sc) -> mg_ctx G -> mg_ctx ((x, sc) :: G).
Proof.
  intros x sc G H HG y s Hin. destruct Hin as [Heq | Hin].
  - injection Heq as <- <-. exact H.
  - exact (HG y s Hin).
Qed.

(* ---- the knot-tying unifier ---- *)

Lemma gsub_meet : forall a b, gsub (meet_float a b).
Proof. intros a b. exact (gs_comp _ _ (gs_sbT b typ_Float I I) (gs_sbT a typ_Float I I)). Qed.

Lemma push_sort_gsub : forall l D k n s D' n', push_sort D k l n = (s, D', n') -> gsub s.
Proof.
  induction l as [|b l IH]; intros D k n s D' n' H; cbn [push_sort] in H.
  - inversion H; subst; clear H. exact gs_id.
  - destruct (finer_b (D b) k).
    + exact (IH _ _ _ _ _ _ H).
    + destruct (finer_b k (D b));
        [ | destruct (push_sort D k l n) as [[s1 D1] n1] eqn:E1; inversion H; subst; clear H;
            exact (gs_comp _ _ (IH _ _ _ _ _ _ E1) (gs_sbT b typ_Float I I)) ].
      destruct (push_sort (upd D (ea n) k) k l (S n)) as [[s1 D1] n1] eqn:E.
      inversion H; subst; clear H.
      exact (gs_comp _ _ (IH _ _ _ _ _ _ E) (gs_sbT b (typ_Var (ea n)) I I)).
Qed.

Lemma push_sort_r_gsub : forall l D k n s D' n', push_sort_r D k l n = (s, D', n') -> gsub s.
Proof.
  induction l as [|b l IH]; intros D k n s D' n' H; cbn [push_sort_r] in H.
  - inversion H; subst; clear H. exact gs_id.
  - destruct (finer_b (rk_sort (drk D b)) k).
    + exact (IH _ _ _ _ _ _ H).
    + destruct (finer_b k (rk_sort (drk D b))); [ | exact (IH _ _ _ _ _ _ H) ].
      destruct (push_sort_r (rupd D (ea n) (RK k (rk_lacks (drk D b)))) k l (S n)) as [[s1 D1] n1] eqn:E.
      inversion H; subst; clear H.
      exact (gs_comp _ _ (IH _ _ _ _ _ _ E) (gs_sbR b (row_Var (ea n)) I I)).
Qed.

Lemma bind_prop0_gsub : forall D a T n s D' n',
  bind_prop0 D a T n = Some (s, D', n') -> mg T -> gsub s.
Proof.
  intros D a T n s D' n' H HT. unfold bind_prop0 in H.
  destruct (occT a T); [ discriminate | ].
  destruct (push_sort D (D a) (AtomSetImpl.elements (ftv_live T)) n) as [[sp D1] n1] eqn:Ep.
  destruct (push_sort_r D1 (D1 a) (AtomSetImpl.elements (frv_live T)) n1) as [[sr D2] n2] eqn:Epr.
  cbn zeta in H. destruct (occT a (apT sr (apT sp T))) eqn:Eo; [ discriminate | ].
  destruct (sat_b D2 (D2 a) (apT sr (apT sp T))); [ | discriminate ]. inversion H; subst; clear H.
  pose proof (push_sort_gsub _ _ _ _ _ _ _ Ep) as Hsp.
  pose proof (push_sort_r_gsub _ _ _ _ _ _ _ Epr) as Hsr.
  exact (gs_comp _ _ (gs_sbT _ _ (proj2 (occT_false _ _ Eo)) (mg_apT _ _ Hsr (mg_apT _ _ Hsp HT)))
           (gs_comp _ _ Hsr Hsp)).
Qed.

Lemma gs_bool_sub : forall ps, gsub (bool_sub ps).
Proof.
  induction ps as [|p ps IH]; cbn [bool_sub]; [ exact gs_id | ].
  exact (gs_comp _ _ IH (gs_sbT p typ_Bool I I)).
Qed.

Lemma bind_prop_gsub : forall D a T n s D' n',
  bind_prop D a T n = Some (s, D', n') -> mg T -> gsub s.
Proof.
  intros D a T n s D' n' H HT. unfold bind_prop in H.
  destruct (bind_prop0 D a T n) as [r|] eqn:E0.
  - inversion H; subst; clear H. exact (bind_prop0_gsub _ _ _ _ _ _ _ E0 HT).
  - destruct (occT a T); [ discriminate | ].
    destruct (forced (D a) T) as [|p0 ps0]; [ discriminate | ].
    destruct (forallb (fun p => sat_b D (D p) typ_Bool) (p0 :: ps0)); [ | discriminate ].
    destruct (bind_prop0 D a (apT (bool_sub (p0 :: ps0)) T) n) as [[[s1 D1] n1]|] eqn:E1; [ | discriminate ].
    injection H as <- <- <-.
    change (gsub (scomp s1 (bool_sub (p0 :: ps0)))).
    exact (gs_comp _ _ (bind_prop0_gsub _ _ _ _ _ _ _ E1 (mg_apT _ _ (gs_bool_sub _) HT)) (gs_bool_sub _)).
Qed.

Lemma bind_k_gsub : forall D a T n s D' n',
  bind_k D a T n = Some (s, D', n') -> gsub s.
Proof.
  intros D a T n s D' n' H. unfold bind_k in H.
  destruct (lcb 0 T) eqn:Elc; cbn [negb] in H; [ | discriminate ].
  destruct (mgb T) eqn:Emg; cbn [negb] in H; [ | discriminate ].
  assert (Hlc : lct 0 T) by (apply lcb_lct; exact Elc).
  assert (Hmg : mg T) by (apply mgb_mg; exact Emg).
  destruct (AtomSetImpl.mem a (ftv_typ T)) eqn:Emem.
  - destruct (gdb false false a T && sat_b D (D a) (knot a T)) eqn:Eg; [ | discriminate ].
    inversion H; subst; clear H.
    apply Bool.andb_true_iff in Eg as [Hg _].
    apply gs_sbT; [ apply knot_lc; exact Hlc | apply mg_knot; assumption ].
  - exact (bind_prop_gsub _ _ _ _ _ _ _ H Hmg).
Qed.

Lemma rewrite_row_gsub : forall l av D R n P T R' s D' n',
  rewrite_row l av D R n = Some (P, T, R', s, D', n') -> gsub s.
Proof.
  intros l av D R. induction R as [|r|l' T' R'' IH|l' P' T' R'' IH]; intros n P T R' s D' n' H; simpl in H.
  - injection H as <- <- <- <- <- <-. exact gs_id.
  - destruct (AtomSetImpl.mem r av); [discriminate|].
    destruct (rk_lacks (drk D r) l); injection H as <- <- <- <- <- <-;
      apply gs_sbR; repeat (split || exact I).
  - destruct (Nat.eqb l l'); [ injection H as <- <- <- <- <- <-; exact gs_id | ].
    destruct (rewrite_row l av D R'' n) as [[[[[[P0 T0] R3] s0] D1] n1]|] eqn:E; [|discriminate].
    injection H as <- <- <- <- <- <-. exact (IH _ _ _ _ _ _ _ E).
  - destruct (Nat.eqb l l'); [ injection H as <- <- <- <- <- <-; exact gs_id | ].
    destruct (rewrite_row l av D R'' n) as [[[[[[P0 T0] R3] s0] D1] n1]|] eqn:E; [|discriminate].
    injection H as <- <- <- <- <- <-. exact (IH _ _ _ _ _ _ _ E).
Qed.

Lemma bind_row_fin_gsub : forall r R sq D0 n0 s D' n',
  bind_row_fin r R sq D0 n0 = Some (s, D', n') -> gsub sq -> mgr R -> gsub s.
Proof.
  intros r R sq D0 n0 s D' n' H Hsq HR. unfold bind_row_fin in H.
  destruct (push_sort D0 (rk_sort (drk D0 r)) (AtomSetImpl.elements (ftv_row (apR sq R))) n0)
    as [[sp D1] n1] eqn:Ep.
  cbn zeta in H.
  destruct (occR r (apR sp (apR sq R))) eqn:Eo; [ discriminate | ].
  destruct (rsat_b D1 (rk_sort (drk D1 r)) (apR sp (apR sq R))
            && lacks_ok (drk D1 r) (apR sp (apR sq R))); [ | discriminate ].
  inversion H; subst; clear H.
  pose proof (push_sort_gsub _ _ _ _ _ _ _ Ep) as Hsp.
  exact (gs_comp _ _ (gs_sbR _ _ (proj2 (occR_false _ _ Eo)) (mg_apR _ _ Hsp (mg_apR _ _ Hsq HR)))
           (gs_comp _ _ Hsp Hsq)).
Qed.

Lemma bind_row_core_gsub : forall D r R n s D' n',
  bind_row_core D r R n = Some (s, D', n') -> mgr R -> gsub s.
Proof.
  intros D r R n s D' n' H HR. unfold bind_row_core in H.
  destruct (occR r R); [ discriminate | ].
  destruct (row_tail R) as [q|].
  - exact (bind_row_fin_gsub _ _ _ _ _ _ _ _ H (gs_sbR q (row_Var (ea n)) I I) HR).
  - exact (bind_row_fin_gsub _ _ _ _ _ _ _ _ H gs_id HR).
Qed.

Lemma bind_row0_gsub : forall D r R n s D' n',
  bind_row0 D r R n = Some (s, D', n') -> mgr R -> gsub s.
Proof.
  intros D r R n s D' n' H HR. unfold bind_row0 in H. cbn zeta in H.
  destruct (forallb (fun p => sat_b D (D p) typ_Bool) (abs_vars (drk D r) R)); [ | discriminate ].
  destruct (occR r (apR (bool_sub (abs_vars (drk D r) R)) R)); [ discriminate | ].
  destruct (push_sort_r D (rk_sort (drk D r))
              (AtomSetImpl.elements (frv_row (apR (bool_sub (abs_vars (drk D r) R)) R))) n)
    as [[sr D1] n1] eqn:Ep.
  destruct (bind_row_core D1 r (apR sr (apR (bool_sub (abs_vars (drk D r) R)) R)) n1)
    as [[[s1 D2] n2]|] eqn:E; [ | discriminate ].
  inversion H; subst; clear H.
  pose proof (push_sort_r_gsub _ _ _ _ _ _ _ Ep) as Hsr.
  pose proof (gs_bool_sub (abs_vars (drk D r) R)) as Hs0.
  exact (gs_comp _ _ (bind_row_core_gsub _ _ _ _ _ _ _ E (mg_apR _ _ Hsr (mg_apR _ _ Hs0 HR)))
           (gs_comp _ _ Hsr Hs0)).
Qed.

Lemma bind_row_gsub : forall D r R n s D' n',
  bind_row D r R n = Some (s, D', n') -> mgr R -> gsub s.
Proof.
  intros D r R n s D' n' H HR. unfold bind_row in H.
  destruct (bind_row0 D r R n) as [x|] eqn:E0.
  - inversion H; subst; clear H. exact (bind_row0_gsub _ _ _ _ _ _ _ E0 HR).
  - destruct (forced_row (rk_sort (drk D r)) R) as [|p0 ps0]; [ discriminate | ].
    destruct (forallb (fun p => sat_b D (D p) typ_Bool) (p0 :: ps0)); [ | discriminate ].
    destruct (bind_row0 D r (apR (bool_sub (p0 :: ps0)) R) n) as [[[s1 D1] n1]|] eqn:E1; [ | discriminate ].
    injection H as <- <- <-.
    change (gsub (scomp s1 (bool_sub (p0 :: ps0)))).
    exact (gs_comp _ _ (bind_row0_gsub _ _ _ _ _ _ _ E1 (mg_apR _ _ (gs_bool_sub _) HR)) (gs_bool_sub _)).
Qed.

Theorem unify_k_gsub : forall f,
  (forall D T1 T2 n s D' n', unify_k f D T1 T2 n = Some (s, D', n') -> gsub s) /\
  (forall D R1 R2 n s D' n', unify_kr f D R1 R2 n = Some (s, D', n') -> gsub s).
Proof.
  induction f as [|f IH]; [ split; intros; discriminate | ].
  destruct IH as [IHt IHr].
  split.
  - intros D T1 T2 n s D' n' H. cbn [unify_k] in H.
    destruct T1 as [| | | | | A B | R | a | i | B1 | w1 A1];
      destruct T2 as [| | | | | A' B' | R' | b | i' | B1' | w1' A1'];
      try discriminate H;
      try (injection H as <- <- <-; exact gs_id);
      try (exact (bind_k_gsub _ _ _ _ _ _ _ H));
      try (exact (IHt _ _ _ _ _ _ _ H)).
    + (* Arrow, Arrow *)
      destruct (unify_k f D A A' n) as [[[s1 D1] n1]|] eqn:E1; [|discriminate].
      destruct (unify_k f D1 (apT s1 B) (apT s1 B') n1) as [[[s2 D2] n2]|] eqn:E2; [|discriminate].
      injection H as <- <- <-.
      exact (gs_comp _ _ (IHt _ _ _ _ _ _ _ E2) (IHt _ _ _ _ _ _ _ E1)).
    + (* Record, Record *)
      exact (IHr _ _ _ _ _ _ _ H).
    + (* Var, Var *)
      destruct (Atom.eq_dec a b) as [->|]; [ injection H as <- <- <-; exact gs_id | ].
      destruct (finer_b (D b) (D a)); [ injection H as <- <- <-; apply gs_sbT; exact I | ].
      destruct (finer_b (D a) (D b)); injection H as <- <- <-; [ apply gs_sbT; exact I | apply gsub_meet ].
    + (* Bvar, Bvar *)
      destruct (Nat.eqb i i'); [ injection H as <- <- <-; exact gs_id | discriminate ].
    + (* Mu, Mu *)
      destruct (match unify_k f D B1 B1' n with
                | Some (s0, D1, n1) => if typ_eqb (apT s0 B1) (apT s0 B1') then Some (s0, D1, n1) else None
                | None => None
                end) as [[[s0 D0] n0]|] eqn:Ein.
      * injection H as <- <- <-.
        destruct (unify_k f D B1 B1' n) as [[[s1 D1] n1]|] eqn:Eu; [ | discriminate Ein ].
        destruct (typ_eqb (apT s1 B1) (apT s1 B1')); [ | discriminate Ein ].
        injection Ein as <- <- <-. exact (IHt _ _ _ _ _ _ _ Eu).
      * exact (IHt _ _ _ _ _ _ _ H).
    + (* Grp, Grp *)
      destruct (gdecl_eq_dec w1 w1'); [ | discriminate ].
      exact (IHt _ _ _ _ _ _ _ H).
  - intros D R1 R2 n s D' n' H. cbn [unify_kr] in H.
    assert (Hgen : forall R1 R2,
      (match row_head R1 with
       | None => None
       | Some (l, P, T, R1') =>
           match rewrite_row l (side_av R1) D R2 n with
           | None => None
           | Some (P', T', R2', s0, D0, n1) =>
               match unify_k f D0 (apT s0 P) P' n1 with
               | None => None
               | Some (sp, D1, n2) =>
                   match unify_k f D1 (apT sp (apT s0 T)) (apT sp T') n2 with
                   | None => None
                   | Some (s1, D2, n3) =>
                       match unify_kr f D2 (apR s1 (apR sp (apR s0 R1'))) (apR s1 (apR sp R2')) n3 with
                       | None => None
                       | Some (s2, D3, n4) => Some (scomp s2 (scomp s1 (scomp sp s0)), D3, n4)
                       end
                   end
               end
           end
       end) = Some (s, D', n') -> gsub s).
    { intros R1' R2' Hg.
      destruct (row_head R1') as [[[[l P] T] R1'']|]; [|discriminate].
      destruct (rewrite_row l (side_av R1') D R2' n) as [[[[[[P' T'] R2''] s0] D0] n1]|] eqn:Erw; [|discriminate].
      destruct (unify_k f D0 (apT s0 P) P' n1) as [[[sp D1] n2]|] eqn:Eu0; [|discriminate].
      destruct (unify_k f D1 (apT sp (apT s0 T)) (apT sp T') n2) as [[[s1 D2] n3]|] eqn:Eu1; [|discriminate].
      destruct (unify_kr f D2 (apR s1 (apR sp (apR s0 R1''))) (apR s1 (apR sp R2'')) n3)
        as [[[s2 D3] n4]|] eqn:Eu2; [|discriminate].
      injection Hg as <- <- <-.
      exact (gs_comp _ _ (IHr _ _ _ _ _ _ _ Eu2)
               (gs_comp _ _ (IHt _ _ _ _ _ _ _ Eu1)
                  (gs_comp _ _ (IHt _ _ _ _ _ _ _ Eu0) (rewrite_row_gsub _ _ _ _ _ _ _ _ _ _ _ Erw)))). }
    destruct R1 as [| r | l T R1' | lm Pm Tm Rm]; destruct R2 as [| q | l2 T2 R2' | lm2 Pm2 Tm2 Rm2];
      try (match type of H with context [row_head ?a] =>
             match type of H with context [rewrite_row _ _ _ ?b _] => exact (Hgen a b H) end end).
    + injection H as <- <- <-. exact gs_id.
    + destruct (mgbr row_Empty) eqn:Em; [|discriminate].
      exact (bind_row_gsub _ _ _ _ _ _ _ H (mgbr_mgr _ Em)).
    + eapply IHr. exact H.
    + destruct (mgbr row_Empty) eqn:Em; [|discriminate].
      exact (bind_row_gsub _ _ _ _ _ _ _ H (mgbr_mgr _ Em)).
    + destruct (Atom.eq_dec r q) as [->|]; [ injection H as <- <- <-; exact gs_id | ].
      exact (bind_row_gsub _ _ _ _ _ _ _ H I).
    + destruct (mgbr (row_Ext l2 T2 R2')) eqn:Em; [|discriminate].
      exact (bind_row_gsub _ _ _ _ _ _ _ H (mgbr_mgr _ Em)).
    + destruct (mgbr (row_Maybe lm2 Pm2 Tm2 Rm2)) eqn:Em; [|discriminate].
      exact (bind_row_gsub _ _ _ _ _ _ _ H (mgbr_mgr _ Em)).
    + destruct (mgbr (row_Ext l T R1')) eqn:Em; [|discriminate].
      exact (bind_row_gsub _ _ _ _ _ _ _ H (mgbr_mgr _ Em)).
    + destruct (mgbr (row_Maybe lm Pm Tm Rm)) eqn:Em; [|discriminate].
      exact (bind_row_gsub _ _ _ _ _ _ _ H (mgbr_mgr _ Em)).
Qed.

(* ---- the plain unifier, on guarded types ---- *)

Lemma row_head_mg : forall R l P T R',
  row_head R = Some (l, P, T, R') -> mgr R -> mg P /\ mg T /\ mgr R'.
Proof.
  intros R l P T R' H HR. destruct R as [|r|l0 T0 R0|l0 P0 T0 R0]; simpl in H; try discriminate;
    injection H as <- <- <- <-.
  - exact (conj I HR).
  - exact HR.
Qed.

Lemma rewrite_row_mg : forall l av D R n P T R' s D' n',
  rewrite_row l av D R n = Some (P, T, R', s, D', n') -> mgr R -> mg P /\ mg T /\ mgr R'.
Proof.
  intros l av D R. induction R as [|r|l' T' R'' IH|l' P' T' R'' IH]; intros n P T R' s D' n' H HR; simpl in H.
  - injection H as <- <- <- <- <- <-. exact (conj I (conj I I)).
  - destruct (AtomSetImpl.mem r av); [discriminate|].
    destruct (rk_lacks (drk D r) l); injection H as <- <- <- <- <- <-; exact (conj I (conj I I)).
  - destruct HR as [HT' HR''].
    destruct (Nat.eqb l l').
    + injection H as <- <- <- <- <- <-. exact (conj I (conj HT' HR'')).
    + destruct (rewrite_row l av D R'' n) as [[[[[[P0 T0] R3] s0] D1] n1]|] eqn:E; [|discriminate].
      injection H as <- <- <- <- <- <-.
      destruct (IH _ _ _ _ _ _ _ E HR'') as [H0 [H1 H2]].
      pose proof (rewrite_row_gsub _ _ _ _ _ _ _ _ _ _ _ E) as Hs0.
      exact (conj H0 (conj H1 (conj (mg_apT _ _ Hs0 HT') H2))).
  - destruct HR as [HP' [HT' HR'']].
    destruct (Nat.eqb l l').
    + injection H as <- <- <- <- <- <-. exact (conj HP' (conj HT' HR'')).
    + destruct (rewrite_row l av D R'' n) as [[[[[[P0 T0] R3] s0] D1] n1]|] eqn:E; [|discriminate].
      injection H as <- <- <- <- <- <-.
      destruct (IH _ _ _ _ _ _ _ E HR'') as [H0 [H1 H2]].
      pose proof (rewrite_row_gsub _ _ _ _ _ _ _ _ _ _ _ E) as Hs0.
      exact (conj H0 (conj H1 (conj (mg_apT _ _ Hs0 HP') (conj (mg_apT _ _ Hs0 HT') H2)))).
Qed.

Lemma mgr_drop_abs : forall R, mgr R -> mgr (drop_abs R).
Proof.
  induction R as [| r | l T R IH | l P T R IH]; simpl; intros H; try exact H.
  - destruct H as [H1 H2]. split; [ exact H1 | apply IH; exact H2 ].
  - destruct H as [H1 [H2 H3]].
    destruct (is_abs P && rlacks l (drop_abs R)); [ apply IH; exact H3 | ].
    simpl. split; [ exact H1 | split; [ exact H2 | apply IH; exact H3 ] ].
Qed.

Theorem unify_t_gsub : forall f,
  (forall D T1 T2 n s D' n', unify_t f D T1 T2 n = Some (s, D', n') ->
     mg T1 -> mg T2 -> gsub s) /\
  (forall D R1 R2 n s D' n', unify_r f D R1 R2 n = Some (s, D', n') ->
     mgr R1 -> mgr R2 -> gsub s).
Proof.
  induction f as [|f IH]; [ refine (conj _ _); intros; discriminate | ].
  destruct IH as [IHt IHr].
  refine (conj _ _).
  - intros D T1 T2 n s D' n' H H1 H2. simpl in H.
    destruct T1, T2; try discriminate;
      try (injection H as <- <- <-; exact gs_id);
      try (exact (bind_prop_gsub _ _ _ _ _ _ _ H H2));
      try (exact (bind_prop_gsub _ _ _ _ _ _ _ H H1));
      try (destruct (Atom.eq_dec _ _); [injection H as <- <- <-; exact gs_id|];
           destruct (finer_b _ _); [ injection H as <- <- <-; apply gs_sbT; exact I | ];
           destruct (finer_b _ _); injection H as <- <- <-; [ apply gs_sbT; exact I | apply gsub_meet ]).
    + destruct (unify_t f D T1_1 T2_1 n) as [[[s1 D1] n1]|] eqn:E1; [|discriminate].
      destruct (unify_t f D1 (apT s1 T1_2) (apT s1 T2_2) n1) as [[[s2 D2] n2]|] eqn:E2; [|discriminate].
      injection H as <- <- <-.
      pose proof (IHt _ _ _ _ _ _ _ E1 (proj1 H1) (proj1 H2)) as Hs1.
      refine (gs_comp _ _ _ Hs1).
      eapply IHt; [ exact E2 | apply mg_apT; [ exact Hs1 | exact (proj2 H1) ]
                             | apply mg_apT; [ exact Hs1 | exact (proj2 H2) ] ].
    + eapply IHr; [exact H | apply mgr_drop_abs; exact H1 | apply mgr_drop_abs; exact H2].
    + destruct (gdecl_eq_dec _ _); [|discriminate].
      eapply IHt; [exact H | exact H1 | exact H2].
  - intros D R1 R2 n s D' n' H H1 H2. simpl in H.
    assert (Hgen : forall R1 R2, mgr R1 -> mgr R2 -> forall s D' n',
      (match row_head R1 with
       | None => None
       | Some (l, P, T, R1') =>
           match rewrite_row l (side_av R1) D R2 n with
           | None => None
           | Some (P', T', R2', s0, D0, n1) =>
               match unify_t f D0 (apT s0 P) P' n1 with
               | None => None
               | Some (sp, D1, n2) =>
                   match unify_t f D1 (apT sp (apT s0 T)) (apT sp T') n2 with
                   | None => None
                   | Some (s1, D2, n3) =>
                       match unify_r f D2 (drop_abs (apR s1 (apR sp (apR s0 R1')))) (drop_abs (apR s1 (apR sp R2'))) n3 with
                       | None => None
                       | Some (s2, D3, n4) => Some (scomp s2 (scomp s1 (scomp sp s0)), D3, n4)
                       end
                   end
               end
           end
       end) = Some (s, D', n') -> gsub s).
    { intros R1' R2' Hg1 Hg2 s' D'' n'' Hg.
      destruct (row_head R1') as [[[[l P] T] R1'']|] eqn:Eh; [|discriminate].
      destruct (rewrite_row l (side_av R1') D R2' n) as [[[[[[P' T'] R2''] s0] D0] n1]|] eqn:Erw; [|discriminate].
      destruct (unify_t f D0 (apT s0 P) P' n1) as [[[sp D1] n2]|] eqn:Eu0; [|discriminate].
      destruct (unify_t f D1 (apT sp (apT s0 T)) (apT sp T') n2) as [[[s1 D2] n3]|] eqn:Eu1; [|discriminate].
      destruct (unify_r f D2 (drop_abs (apR s1 (apR sp (apR s0 R1'')))) (drop_abs (apR s1 (apR sp R2''))) n3)
        as [[[s2 D3] n4]|] eqn:Eu2; [|discriminate].
      injection Hg as <- <- <-.
      destruct (row_head_mg _ _ _ _ _ Eh Hg1) as [HP [HT HR1]].
      destruct (rewrite_row_mg _ _ _ _ _ _ _ _ _ _ _ Erw Hg2) as [M0 [M1 M2]].
      pose proof (rewrite_row_gsub _ _ _ _ _ _ _ _ _ _ _ Erw) as S0.
      pose proof (IHt _ _ _ _ _ _ _ Eu0 (mg_apT _ _ S0 HP) M0) as Sp.
      pose proof (IHt _ _ _ _ _ _ _ Eu1 (mg_apT _ _ Sp (mg_apT _ _ S0 HT)) (mg_apT _ _ Sp M1)) as S1.
      pose proof (IHr _ _ _ _ _ _ _ Eu2
                    (mgr_drop_abs _ (mg_apR _ _ S1 (mg_apR _ _ Sp (mg_apR _ _ S0 HR1))))
                    (mgr_drop_abs _ (mg_apR _ _ S1 (mg_apR _ _ Sp M2)))) as S2.
      exact (gs_comp _ _ S2 (gs_comp _ _ S1 (gs_comp _ _ Sp S0))). }
    destruct R1 as [|r|l T R1'|lm Pm Tm Rm]; destruct R2 as [|r2|l2 T2 R2'|lm2 Pm2 Tm2 Rm2];
      try (exact (Hgen _ _ H1 H2 _ _ _ H)).
    + injection H as <- <- <-. exact gs_id.
    + exact (bind_row_gsub _ _ _ _ _ _ _ H H1).
    + eapply IHr; [exact H | exact H2 | exact H1].
    + exact (bind_row_gsub _ _ _ _ _ _ _ H H2).
    + destruct (Atom.eq_dec r r2); [injection H as <- <- <-; exact gs_id|].
      exact (bind_row_gsub _ _ _ _ _ _ _ H H2).
    + exact (bind_row_gsub _ _ _ _ _ _ _ H H2).
    + exact (bind_row_gsub _ _ _ _ _ _ _ H H2).
    + exact (bind_row_gsub _ _ _ _ _ _ _ H H1).
    + exact (bind_row_gsub _ _ _ _ _ _ _ H H1).
Qed.

Lemma mg_nf_mut : forall D,
  (forall T, mg T -> mg (nfT D T)) /\ (forall R, mgr R -> mgr (nfR D R)).
Proof.
  intros D. apply typ_row_mutind.
  - intros _. exact I.
  - intros _. exact I.
  - intros _. exact I.
  - intros _. exact I.
  - intros _. exact I.
  - intros A HA B HB [H1 H2]. cbn [nfT mg]. split; [ apply HA; exact H1 | apply HB; exact H2 ].
  - intros R HR H. cbn [nfT mg] in *. apply HR. exact H.
  - intros a _. exact I.
  - intros i _. exact I.
  - intros B HB H. exact H.
  - intros w A HA H. exact H.
  - intros _. exact I.
  - intros r _. exact I.
  - intros l T HT R HR [H1 H2]. rewrite nfR_ext. cbn [mgr]. split; [ apply HT; exact H1 | apply HR; exact H2 ].
  - intros l P HP T HT R HR [H1 [H2 H3]]. rewrite nfR_maybe.
    destruct (is_abs P && rlacksD D l (nfR D R)); cbv iota.
    + apply HR. exact H3.
    + cbn [mgr]. split; [ apply HP; exact H1 | split; [ apply HT; exact H2 | apply HR; exact H3 ] ].
Qed.

Lemma mgr_nfR : forall D R, mgr R -> mgr (nfR D R).
Proof. intros D R H. exact (proj2 (mg_nf_mut D) R H). Qed.

Theorem unify_tD_gsub : forall f,
  (forall D T1 T2 n s D' n', unify_tD f D T1 T2 n = Some (s, D', n') ->
     mg T1 -> mg T2 -> gsub s) /\
  (forall D R1 R2 n s D' n', unify_rD f D R1 R2 n = Some (s, D', n') ->
     mgr R1 -> mgr R2 -> gsub s).
Proof.
  induction f as [|f IH]; [ refine (conj _ _); intros; discriminate | ].
  destruct IH as [IHt IHr].
  refine (conj _ _).
  - intros D T1 T2 n s D' n' H H1 H2. simpl in H.
    destruct T1, T2; try discriminate;
      try (injection H as <- <- <-; exact gs_id);
      try (exact (bind_prop_gsub _ _ _ _ _ _ _ H H2));
      try (exact (bind_prop_gsub _ _ _ _ _ _ _ H H1));
      try (destruct (Atom.eq_dec _ _); [injection H as <- <- <-; exact gs_id|];
           destruct (finer_b _ _); [ injection H as <- <- <-; apply gs_sbT; exact I | ];
           destruct (finer_b _ _); injection H as <- <- <-; [ apply gs_sbT; exact I | apply gsub_meet ]).
    + destruct (unify_tD f D T1_1 T2_1 n) as [[[s1 D1] n1]|] eqn:E1; [|discriminate].
      destruct (unify_tD f D1 (apT s1 T1_2) (apT s1 T2_2) n1) as [[[s2 D2] n2]|] eqn:E2; [|discriminate].
      injection H as <- <- <-.
      pose proof (IHt _ _ _ _ _ _ _ E1 (proj1 H1) (proj1 H2)) as Hs1.
      refine (gs_comp _ _ _ Hs1).
      eapply IHt; [ exact E2 | apply mg_apT; [ exact Hs1 | exact (proj2 H1) ]
                             | apply mg_apT; [ exact Hs1 | exact (proj2 H2) ] ].
    + eapply IHr; [exact H | apply mgr_nfR; exact H1 | apply mgr_nfR; exact H2].
    + destruct (gdecl_eq_dec _ _); [|discriminate].
      exact (proj1 (unify_t_gsub f) _ _ _ _ _ _ _ H H1 H2).
  - intros D R1 R2 n s D' n' H H1 H2. simpl in H.
    assert (Hgen : forall R1 R2, mgr R1 -> mgr R2 -> forall s D' n',
      (match row_head R1 with
       | None => None
       | Some (l, P, T, R1') =>
           match rewrite_row l (side_av R1) D R2 n with
           | None => None
           | Some (P', T', R2', s0, D0, n1) =>
               match unify_tD f D0 (apT s0 P) P' n1 with
               | None => None
               | Some (sp, D1, n2) =>
                   match unify_tD f D1 (apT sp (apT s0 T)) (apT sp T') n2 with
                   | None =>
                       match absent_clash D1 l (apT sp (apT s0 P)) (apT sp (apT s0 T)) (apT sp T')
                               (apR sp (apR s0 R1')) (apR sp R2') with
                       | None => None
                       | Some p =>
                           match unify_rD f D1 (nfR D1 (apR (bool_sub (p :: nil)) (apR sp (apR s0 R1'))))
                                   (nfR D1 (apR (bool_sub (p :: nil)) (apR sp R2'))) n2 with
                           | None => None
                           | Some (s2, D3, n4) =>
                               Some (scomp s2 (scomp (bool_sub (p :: nil)) (scomp sp s0)), D3, n4)
                           end
                       end
                   | Some (s1, D2, n3) =>
                       match unify_rD f D2 (nfR D2 (apR s1 (apR sp (apR s0 R1')))) (nfR D2 (apR s1 (apR sp R2'))) n3 with
                       | None => None
                       | Some (s2, D3, n4) => Some (scomp s2 (scomp s1 (scomp sp s0)), D3, n4)
                       end
                   end
               end
           end
       end) = Some (s, D', n') -> gsub s).
    { intros R1' R2' Hg1 Hg2 s' D'' n'' Hg.
      destruct (row_head R1') as [[[[l P] T] R1'']|] eqn:Eh; [|discriminate].
      destruct (rewrite_row l (side_av R1') D R2' n) as [[[[[[P' T'] R2''] s0] D0] n1]|] eqn:Erw; [|discriminate].
      destruct (unify_tD f D0 (apT s0 P) P' n1) as [[[sp D1] n2]|] eqn:Eu0; [|discriminate].
      destruct (unify_tD f D1 (apT sp (apT s0 T)) (apT sp T') n2) as [[[s1 D2] n3]|] eqn:Eu1.
      2: { destruct (absent_clash D1 l (apT sp (apT s0 P)) (apT sp (apT s0 T)) (apT sp T')
                       (apR sp (apR s0 R1'')) (apR sp R2'')) as [p|] eqn:Eac; [ | discriminate Hg ].
           destruct (unify_rD f D1 (nfR D1 (apR (bool_sub (p :: nil)) (apR sp (apR s0 R1''))))
                       (nfR D1 (apR (bool_sub (p :: nil)) (apR sp R2''))) n2)
             as [[[s2 D3] n4]|] eqn:Eu2; [ | discriminate Hg ].
           injection Hg as <- <- <-.
           destruct (row_head_mg _ _ _ _ _ Eh Hg1) as [HP [HT HR1]].
           destruct (rewrite_row_mg _ _ _ _ _ _ _ _ _ _ _ Erw Hg2) as [M0 [M1 M2]].
           pose proof (rewrite_row_gsub _ _ _ _ _ _ _ _ _ _ _ Erw) as S0.
           pose proof (IHt _ _ _ _ _ _ _ Eu0 (mg_apT _ _ S0 HP) M0) as Sp.
           pose proof (gs_bool_sub (p :: nil)) as Sb.
           pose proof (IHr _ _ _ _ _ _ _ Eu2
                         (mgr_nfR _ _ (mg_apR _ _ Sb (mg_apR _ _ Sp (mg_apR _ _ S0 HR1))))
                         (mgr_nfR _ _ (mg_apR _ _ Sb (mg_apR _ _ Sp M2)))) as S2.
           exact (gs_comp _ _ S2 (gs_comp _ _ Sb (gs_comp _ _ Sp S0))). }
      destruct (unify_rD f D2 (nfR D2 (apR s1 (apR sp (apR s0 R1'')))) (nfR D2 (apR s1 (apR sp R2''))) n3)
        as [[[s2 D3] n4]|] eqn:Eu2; [|discriminate].
      injection Hg as <- <- <-.
      destruct (row_head_mg _ _ _ _ _ Eh Hg1) as [HP [HT HR1]].
      destruct (rewrite_row_mg _ _ _ _ _ _ _ _ _ _ _ Erw Hg2) as [M0 [M1 M2]].
      pose proof (rewrite_row_gsub _ _ _ _ _ _ _ _ _ _ _ Erw) as S0.
      pose proof (IHt _ _ _ _ _ _ _ Eu0 (mg_apT _ _ S0 HP) M0) as Sp.
      pose proof (IHt _ _ _ _ _ _ _ Eu1 (mg_apT _ _ Sp (mg_apT _ _ S0 HT)) (mg_apT _ _ Sp M1)) as S1.
      pose proof (IHr _ _ _ _ _ _ _ Eu2
                    (mgr_nfR _ _ (mg_apR _ _ S1 (mg_apR _ _ Sp (mg_apR _ _ S0 HR1))))
                    (mgr_nfR _ _ (mg_apR _ _ S1 (mg_apR _ _ Sp M2)))) as S2.
      exact (gs_comp _ _ S2 (gs_comp _ _ S1 (gs_comp _ _ Sp S0))). }
    destruct R1 as [|r|l T R1'|lm Pm Tm Rm]; destruct R2 as [|r2|l2 T2 R2'|lm2 Pm2 Tm2 Rm2];
      try (exact (Hgen _ _ H1 H2 _ _ _ H)).
    + injection H as <- <- <-. exact gs_id.
    + exact (bind_row_gsub _ _ _ _ _ _ _ H H1).
    + eapply IHr; [exact H | exact H2 | exact H1].
    + exact (bind_row_gsub _ _ _ _ _ _ _ H H2).
    + destruct (Atom.eq_dec r r2); [injection H as <- <- <-; exact gs_id|].
      exact (bind_row_gsub _ _ _ _ _ _ _ H H2).
    + exact (bind_row_gsub _ _ _ _ _ _ _ H H2).
    + exact (bind_row_gsub _ _ _ _ _ _ _ H H2).
    + exact (bind_row_gsub _ _ _ _ _ _ _ H H1).
    + exact (bind_row_gsub _ _ _ _ _ _ _ H H1).
Qed.

Lemma group_row_mg : forall fs n, mgr (group_row fs n).
Proof.
  induction fs as [|l e rest IH|l e rest IH]; intros n; simpl.
  - exact I.
  - split; [exact I | apply IH].
  - split; [exact I | apply IH].
Qed.

Lemma mg_spine : forall Ts, Forall mg Ts -> mg (spine Ts).
Proof. intros Ts H. induction H; simpl; [exact I | split; assumption]. Qed.

Lemma mg_nth : forall Ts j, Forall mg Ts -> mg (nth j Ts typ_Unit).
Proof.
  intros Ts j H. revert j. induction H as [|T Ts HT HTs IH]; intros [|j]; simpl;
    [ exact I | exact I | exact HT | apply IH ].
Qed.

Lemma mg_slot_ty : forall w Ts c, Forall mg Ts -> mg (slot_ty w Ts c).
Proof.
  intros w Ts c H. unfold slot_ty. destruct c as [|[|[|[|[|[|c]]]]]]; simpl;
    first [ exact I | exact (mg_spine _ H) | exact (mg_nth _ _ H) ].
Qed.

Lemma mg_slots_row : forall w Ts cs i, Forall mg Ts -> mgr (slots_row w Ts i cs).
Proof.
  intros w Ts cs. induction cs as [|c cs IH]; intros i H; simpl;
    [ exact I | split; [ apply mg_slot_ty; exact H | apply IH; exact H ] ].
Qed.

Lemma mg_tag_payload : forall w Ts tg, Forall mg Ts -> mg (tag_payload w Ts tg).
Proof.
  intros w Ts tg H. unfold tag_payload. destruct (nth_error (gtags w) tg) as [cs|]; [|exact I].
  unfold payload_ty. destruct cs; [ exact I | cbn [mg]; apply mg_slots_row; exact H ].
Qed.

Lemma mg_fresh_tys : forall k n, Forall mg (fresh_tys n k).
Proof. induction k as [|k IH]; intros n; simpl; [constructor | constructor; [exact I | apply IH]]. Qed.

Lemma mg_map : forall s Ts, gsub s -> Forall mg Ts -> Forall mg (map (apT s) Ts).
Proof.
  intros s Ts Hs H. induction H; simpl; constructor; [ apply mg_apT; assumption | assumption ].
Qed.


Lemma mg_ctx_nil : mg_ctx nil.
Proof. intros x s Hin. destruct Hin. Qed.

Lemma unify_co_gsub : forall f D T1 T2 n s D' cs n',
  unify_co f D T1 T2 n = Some (s, D', cs, n') -> mg T1 -> mg T2 -> gsub s.
Proof.
  intros f D T1 T2 n s D' cs n' H H1 H2. unfold unify_co in H.
  destruct (unify_t f D T1 T2 n) as [[[s0 D0] n0]|] eqn:E1.
  - injection H as <- <- <- <-. exact (proj1 (unify_t_gsub f) _ _ _ _ _ _ _ E1 H1 H2).
  - destruct (unify_k f D T1 T2 n) as [[[s0 D0] n0]|] eqn:E2; [|discriminate].
    destruct (coerce_dec f D0 (apT s0 T1) (apT s0 T2)); [|discriminate].
    injection H as <- <- <- <-. exact (proj1 (unify_k_gsub f) _ _ _ _ _ _ _ E2).
Qed.

Lemma unify_coD_gsub : forall f D T1 T2 n s D' cs n',
  unify_coD f D T1 T2 n = Some (s, D', cs, n') -> mg T1 -> mg T2 -> gsub s.
Proof.
  intros f D T1 T2 n s D' cs n' H H1 H2. unfold unify_coD in H.
  destruct (unify_tD f D T1 T2 n) as [[[s0 D0] n0]|] eqn:E1.
  - injection H as <- <- <- <-. exact (proj1 (unify_tD_gsub f) _ _ _ _ _ _ _ E1 H1 H2).
  - destruct (unify_k f D T1 T2 n) as [[[s0 D0] n0]|] eqn:E2; [|discriminate].
    destruct (coerce_dec f D0 (apT s0 T1) (apT s0 T2)); [|discriminate].
    injection H as <- <- <- <-. exact (proj1 (unify_k_gsub f) _ _ _ _ _ _ _ E2).
Qed.


Lemma inst_sub_gsub : forall sc n, gsub (inst_sub sc n).
Proof.
  intros sc n. unfold inst_sub. split; [ split | split ]; intros x; simpl;
    destruct (in_dec Atom.eq_dec x _); exact I.
Qed.

Lemma instantiate_mg : forall D sc n T D' n',
  instantiate D sc n = (T, D', n') -> mg (s_body sc) -> mg T.
Proof.
  intros D sc n T D' n' H Hb. unfold instantiate in H.
  injection H as <- <- <-. apply mg_apT; [apply inst_sub_gsub | exact Hb].
Qed.

Lemma lookup_mg : forall x G sc, lookup x G = Some sc -> mg_ctx G -> mg (s_body sc).
Proof.
  intros x G. induction G as [|[y s0] G IH]; intros sc H HG; simpl in H; [discriminate|].
  destruct (Atom.eq_dec x y).
  - injection H as <-. exact (HG y s0 (or_introl eq_refl)).
  - apply IH; [exact H|]. intros z s1 Hin. exact (HG z s1 (or_intror Hin)).
Qed.

Lemma gen_ren_mg : forall D G T, mg T -> mg (s_body (gen_ren D G T)).
Proof.
  intros D G T H. unfold gen_ren. simpl.
  refine (proj1 (mg_ap_mut _ _ _ _ _) T H).
  - split; [ intros a; unfold rename_t | intros r; unfold rename_r ];
      destruct (in_dec _ _ _); exact I.
  - intros a. unfold rename_t. destruct (in_dec Atom.eq_dec a _); exact I.
  - intros r. unfold rename_r. destruct (in_dec Atom.eq_dec r _); exact I.
Qed.

Lemma mg_bin_res : forall o T, mg T -> mg (bin_res o T).
Proof. intros o T H. unfold bin_res. destruct (kind o); first [ exact H | exact I ]. Qed.

Ltac dI H E :=
  match type of H with context [infer ?f ?D ?G ?e ?n] =>
    destruct (infer f D G e n) as [[[[[? ?] ?] ?] ?]|] eqn:E; [|discriminate H] end.

Ltac dF H E :=
  match type of H with context [infer_fields ?f ?D ?G ?e ?n] =>
    destruct (infer_fields f D G e n) as [[[[[? ?] ?] ?] ?]|] eqn:E; [|discriminate H] end.

Ltac dA H E :=
  match type of H with context [infer_arms ?f ?D ?G ?w ?Ts ?x ?r ?a ?n] =>
    destruct (infer_arms f D G w Ts x r a n) as [[[[[? ?] ?] ?] ?]|] eqn:E; [|discriminate H] end.

Ltac dC H E :=
  match type of H with context [unify_coD ?f ?D ?A ?B ?n] =>
    destruct (unify_coD f D A B n) as [[[[? ?] ?] ?]|] eqn:E; [|discriminate H] end.

Ltac dP H E :=
  match type of H with context [unify_grp ?f ?D ?fs ?A ?B ?n] =>
    destruct (unify_grp f D fs A B n) as [[[[? ?] ?] ?]|] eqn:E; [|discriminate H] end.

Lemma obj_row_mg : forall fs n a, mgr (obj_row fs n (row_Var a)).
Proof.
  induction fs as [|l e rest IH|l e rest IH]; intros n a; simpl.
  - exact I.
  - split; [ exact I | apply IH ].
  - split; [ exact I | apply IH ].
Qed.

Ltac dO H E :=
  match type of H with context [infer_obj ?f ?D ?G ?p ?Tp ?e ?n] =>
    destruct (infer_obj f D G p Tp e n) as [[[[[? ?] ?] ?] ?]|] eqn:E; [|discriminate H] end.

Ltac dT H E :=
  match type of H with context [tie_obj ?f ?D ?fs ?R ?Rsl ?n] =>
    destruct (tie_obj f D fs R Rsl n) as [[[[? ?] ?] ?]|] eqn:E; [|discriminate H] end.

Lemma tie_obj_gsub : forall f fs D R Rsl n s D' n' fs2,
  tie_obj f D fs R Rsl n = Some (s, D', n', fs2) -> mgr R -> mgr Rsl -> gsub s.
Proof.
  intros f fs. induction fs as [|l e rest IH|l e rest IH];
    intros D R Rsl n s D' n' fs2 H HR HRsl;
    destruct R as [|r|l1 T R'|l1 P0 T0 R'], Rsl as [|r2|l2 A Rsl'|l2 P2 T2 R2'];
    simpl in H; try discriminate H.
  - injection H as <- <- <- <-. exact gs_id.
  - destruct (Nat.eqb l l1 && Nat.eqb l l2); [ | discriminate H ].
    destruct (unify_co f D T A n) as [[[[s1 D1] cs] n1]|] eqn:E1; [ | discriminate H ].
    destruct (tie_obj f D1 rest (apR s1 R') (apR s1 Rsl') n1) as [[[[s2 D2] n2] rest']|] eqn:E2; [ | discriminate H ].
    injection H as <- <- <- <-. destruct HR as [HT HR']. destruct HRsl as [HA HRsl'].
    pose proof (unify_co_gsub _ _ _ _ _ _ _ _ _ E1 HT HA) as S1.
    exact (gs_comp _ _ (IH _ _ _ _ _ _ _ _ E2 (mg_apR _ _ S1 HR') (mg_apR _ _ S1 HRsl')) S1).
  - destruct (Nat.eqb l l1 && Nat.eqb l l2); [ | discriminate H ].
    destruct (unify_co f D T A n) as [[[[s1 D1] cs] n1]|] eqn:E1; [ | discriminate H ].
    destruct (tie_obj f D1 rest (apR s1 R') (apR s1 Rsl') n1) as [[[[s2 D2] n2] rest']|] eqn:E2; [ | discriminate H ].
    injection H as <- <- <- <-. destruct HR as [HT HR']. destruct HRsl as [HA HRsl'].
    pose proof (unify_co_gsub _ _ _ _ _ _ _ _ _ E1 HT HA) as S1.
    exact (gs_comp _ _ (IH _ _ _ _ _ _ _ _ E2 (mg_apR _ _ S1 HR') (mg_apR _ _ S1 HRsl')) S1).
Qed.

Lemma unify_mem_gsub : forall f D e T A n s D' n' e',
  unify_mem f D e T A n = Some (s, D', n', e') -> mg T -> mg A -> gsub s.
Proof.
  intros f D e T A n s D' n' e' H HT HA. unfold unify_mem in H.
  destruct (unify_t f D T A n) as [[[s0 D0] n0]|] eqn:E.
  - injection H as <- <- <- <-. exact (proj1 (unify_t_gsub f) _ _ _ _ _ _ _ E HT HA).
  - destruct e as [ | | | | | | b | | | | | | | | | | | | | | | | ]; try discriminate H.
    destruct T as [ | | | | | X Y | | | | | ]; try discriminate H.
    destruct A as [ | | | | | X' Y' | | | | | ]; try discriminate H.
    destruct (unify_t f D X X' n) as [[[s1 D1] n1]|] eqn:E1; [ | discriminate H ].
    destruct (unify_co f D1 (apT s1 Y) (apT s1 Y') n1) as [[[[s2 D2] cs] n2]|] eqn:E2; [ | discriminate H ].
    injection H as <- <- <- <-. destruct HT as [HX HY]. destruct HA as [HX' HY'].
    pose proof ((proj1 (unify_t_gsub f)) _ _ _ _ _ _ _ E1 HX HX') as S1.
    pose proof (unify_co_gsub _ _ _ _ _ _ _ _ _ E2 (mg_apT _ _ S1 HY) (mg_apT _ _ S1 HY')) as S2.
    exact (gs_comp _ _ S2 S1).
Qed.

Lemma unify_grp_gsub : forall f D fs R1 R2 n s D' n' fs2,
  unify_grp f D fs R1 R2 n = Some (s, D', n', fs2) -> mgr R1 -> mgr R2 -> gsub s.
Proof.
  induction f as [|f IH]; intros D fs R1 R2 n s D' n' fs2 H H1 H2; [ discriminate | ].
  cbn [unify_grp] in H.
  destruct fs as [|l e rest|l e rest]; destruct R1 as [|r|l1 T R1'|lm Pm Tm Rm];
    destruct R2 as [|r2|l2 A R2'|lm2 Pm2 Tm2 Rm2]; try discriminate H.
  - injection H as <- <- <- <-. exact gs_id.
  - destruct (Nat.eqb l l1 && Nat.eqb l l2); [ | discriminate H ].
    destruct (unify_mem f D e T A n) as [[[[s1 D1] n1] e']|] eqn:E1; [ | discriminate H ].
    destruct (unify_grp f D1 rest (apR s1 R1') (apR s1 R2') n1) as [[[[s2 D2] n2] rest']|] eqn:E2; [ | discriminate H ].
    injection H as <- <- <- <-. destruct H1 as [HT HR1]. destruct H2 as [HA HR2].
    pose proof (unify_mem_gsub _ _ _ _ _ _ _ _ _ _ E1 HT HA) as S1.
    exact (gs_comp _ _ (IH _ _ _ _ _ _ _ _ _ E2 (mg_apR _ _ S1 HR1) (mg_apR _ _ S1 HR2)) S1).
Qed.

Lemma spread_present_guard : forall f D2 s1 s2 T1 T2 l e1' e2' n2 s D' T n' e',
  spread_present f D2 s1 s2 T1 T2 l e1' e2' n2 = Some (s, D', T, n', e') ->
  gsub s2 -> gsub s1 -> mg (apT s2 T1) -> mg T2 -> gsub s /\ mg T.
Proof.
  intros f D2 s1 s2 T1 T2 l e1' e2' n2 s D' T n' e' H S2 S1 M1 M2. unfold spread_present in H.
  destruct (unify_coD f (rupd D2 (ea (S n2)) (RK k_Any (Nat.eqb l))) (apT s2 T1)
              (typ_Record (row_Maybe l (typ_Var (ea n2)) T2 (row_Var (ea (S n2))))) (n2 + 2))
    as [[[[s3 D3] cs] n3]|] eqn:E; [|discriminate].
  injection H as <- <- <- <- <-.
  pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E M1 (conj I (conj M2 I))) as S3.
  exact (conj (gs_comp _ _ S3 (gs_comp _ _ S2 S1))
              (mg_apT _ (typ_Record (row_Ext _ _ (row_Var _))) S3 (conj M2 I))).
Qed.

Theorem infer_guard : forall f,
  (forall D G e n s D' T n' e', infer f D G e n = Some (s, D', T, n', e') ->
     mg_ctx G -> gsub s /\ mg T) /\
  (forall D G fs n s D' R n' fs', infer_fields f D G fs n = Some (s, D', R, n', fs') ->
     mg_ctx G -> gsub s /\ mgr R) /\
  (forall D G w Ts x res ars n s D' T n' ars',
     infer_arms f D G w Ts x res ars n = Some (s, D', T, n', ars') ->
     mg_ctx G -> Forall mg Ts -> mg res -> gsub s /\ mg T) /\
  (forall D G p Tp fs n s D' R n' fs', infer_obj f D G p Tp fs n = Some (s, D', R, n', fs') ->
     mg_ctx G -> mg Tp -> gsub s /\ mgr R).
Proof.
  induction f as [|f IH]; [refine (conj _ (conj _ (conj _ _))); intros; discriminate|].
  destruct IH as [IHi [IHf [IHa IHo]]].
  refine (conj _ (conj _ (conj _ _))).
  - intros D G e n s D' T n' e' H HG.
    destruct e as [i|x|k|d| | |b|e1 e2|e1 e2|fs e2|fs|e1 l| |q|c e1 e2|e1 o e2|e1|w tg e1|w e1 ars|e1 l e2|e1 l|e1|e1];
      simpl in H; try discriminate H;
      try (injection H as <- <- <- <- <-; exact (conj gs_id I)).
    + destruct (lookup x G) as [sc|] eqn:EL; [|discriminate].
      injection H as <- <- <- <- <-.
      exact (conj gs_id (mg_apT _ _ (inst_sub_gsub sc n) (lookup_mg _ _ _ EL HG))).
    + dI H E1.
      injection H as <- <- <- <- <-.
      destruct (IHi _ _ _ _ _ _ _ _ _ E1 (mg_cons _ (sch_mono (typ_Var (ea n))) _ I HG)) as [S1 M1].
      exact (conj S1 (conj (mg_apT _ (typ_Var _) S1 I) M1)).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dI H E2. destruct (IHi _ _ _ _ _ _ _ _ _ E2 (mg_apC _ _ S1 HG)) as [S2 M2].
      dC H E3.
      injection H as <- <- <- <- <-.
      pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E3 (mg_apT _ _ S2 M1) (conj M2 I)) as S3.
      exact (conj (gs_comp _ _ S3 (gs_comp _ _ S2 S1)) (mg_apT _ (typ_Var _) S3 I)).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      match type of H with context [if is_gen_value ?e then _ else _] => destruct (is_gen_value e) end.
      * dI H E2.
        injection H as <- <- <- <- <-.
        destruct (IHi _ _ _ _ _ _ _ _ _ E2
                    (mg_cons _ _ _ (gen_ren_mg _ _ _ M1) (mg_apC _ _ S1 HG))) as [S2 M2].
        exact (conj (gs_comp _ _ S2 S1) M2).
      * dI H E2.
        injection H as <- <- <- <- <-.
        destruct (IHi _ _ _ _ _ _ _ _ _ E2 (mg_cons _ (sch_mono _) _ M1 (mg_apC _ _ S1 HG))) as [S2 M2].
        exact (conj (gs_comp _ _ S2 S1) M2).
    + destruct (is_fn_group fs); [|discriminate].
      dF H E1.
      destruct (IHf _ _ _ _ _ _ _ _ _ E1
                  (mg_cons _ (sch_mono (typ_Record (group_row fs n))) _ (group_row_mg _ _) HG)) as [S1 M1].
      dP H E2.
      pose proof (unify_grp_gsub _ _ _ _ _ _ _ _ _ _ E2 M1
                    (mg_apR _ _ S1 (group_row_mg fs n))) as S2.
      pose proof (gs_comp _ _ S2 S1) as Sc.
      dI H E3.
      injection H as <- <- <- <- <-.
      destruct (IHi _ _ _ _ _ _ _ _ _ E3
                  (mg_cons _ _ _ (gen_ren_mg _ _ (typ_Record _) (mg_apR _ _ Sc (group_row_mg fs n)))
                     (mg_apC _ _ Sc HG))) as [S3 M3].
      exact (conj (gs_comp _ _ S3 Sc) M3).
    + destruct (no_meth fs) eqn:Hnm; try (rewrite Hnm in H).
      * dF H E1. injection H as <- <- <- <- <-.
        destruct (IHf _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1]. exact (conj S1 M1).
      * dO H E1. dT H E2. injection H as <- <- <- <- <-.
        destruct (IHo _ _ _ _ _ _ _ _ _ _ _ E1 HG (obj_row_mg fs n _)) as [S1 M1].
        pose proof (tie_obj_gsub _ _ _ _ _ _ _ _ _ _ E2 M1 (mg_apR _ _ S1 (group_row_mg fs n))) as S2.
        exact (conj (gs_comp _ _ S2 S1)
                    (mg_apT _ (typ_Record (group_row fs n)) (gs_comp _ _ S2 S1) (group_row_mg fs n))).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dC H E2. injection H as <- <- <- <- <-.
      pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E2 M1 (conj I I)) as S2.
      exact (conj (gs_comp _ _ S2 S1) (mg_apT _ (typ_Var _) S2 I)).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dC H E2.
      pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E2 M1 I) as S2.
      dI H E3. destruct (IHi _ _ _ _ _ _ _ _ _ E3 (mg_apC _ _ S2 (mg_apC _ _ S1 HG))) as [S3 M2].
      dI H E4. destruct (IHi _ _ _ _ _ _ _ _ _ E4
                           (mg_apC _ _ S3 (mg_apC _ _ S2 (mg_apC _ _ S1 HG)))) as [S4 M3].
      dC H E5. injection H as <- <- <- <- <-.
      pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E5 (mg_apT _ _ S4 M2) M3) as S5.
      exact (conj (gs_comp _ _ S5 (gs_comp _ _ S4 (gs_comp _ _ S3 (gs_comp _ _ S2 S1))))
                  (mg_apT _ _ S5 M3)).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dI H E2. destruct (IHi _ _ _ _ _ _ _ _ _ E2 (mg_apC _ _ S1 HG)) as [S2 M2].
      destruct (is_cmp_op o).
      { dC H E3.
        pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E3 (mg_apT _ _ S2 M1) M2) as S3.
        dC H E4. injection H as <- <- <- <- <-.
        pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E4 (mg_apT _ _ S3 M2) I) as S4.
        exact (conj (gs_comp _ _ S4 (gs_comp _ _ S3 (gs_comp _ _ S2 S1))) I). }
      dC H E3.
      pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E3 (mg_apT _ _ S2 M1) I) as S3.
      dC H E4. injection H as <- <- <- <- <-.
      pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E4 (mg_apT _ _ S3 M2) (mg_apT _ (typ_Var _) S3 I)) as S4.
      exact (conj (gs_comp _ _ S4 (gs_comp _ _ S3 (gs_comp _ _ S2 S1)))
                  (mg_bin_res _ _ (mg_apT _ _ S4 (mg_apT _ (typ_Var _) S3 I)))).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dC H E2. injection H as <- <- <- <- <-.
      pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E2 M1 I) as S2.
      exact (conj (gs_comp _ _ S2 S1) I).
    + destruct (Nat.ltb tg (length (gtags w))); [|discriminate].
      dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      match type of H with context [fresh_tys ?m (nparams w)] => pose proof (mg_fresh_tys (nparams w) m) as HTs end.
      dC H E2. injection H as <- <- <- <- <-.
      pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E2 M1 (mg_tag_payload _ _ _ HTs)) as S2.
      exact (conj (gs_comp _ _ S2 S1) (mg_apT _ (typ_Grp _ (spine _)) S2 (mg_spine _ HTs))).
    + destruct (arms_wf_b w ars); [|discriminate].
      dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dC H E2.
      match type of H with context [fresh_tys ?m (nparams w)] => pose proof (mg_fresh_tys (nparams w) m) as HTs end.
      pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E2 M1 (mg_spine _ HTs)) as S2.
      dA H E3. injection H as <- <- <- <- <-.
      destruct (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ E3 (mg_apC _ _ S2 (mg_apC _ _ S1 HG))
                  (mg_map _ _ S2 HTs) I) as [S3 M3].
      exact (conj (gs_comp _ _ S3 (gs_comp _ _ S2 S1)) M3).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dI H E2. destruct (IHi _ _ _ _ _ _ _ _ _ E2 (mg_apC _ _ S1 HG)) as [S2 M2].
      match type of H with context [unify_coD ?f ?D ?A ?B ?n] =>
        destruct (unify_coD f D A B n) as [[[[? ?] ?] ?]|] eqn:E3 end.
      * match type of H with context [if rlacksD ?a ?b ?c then _ else _] =>
          destruct (rlacksD a b c) end.
        -- injection H as <- <- <- <- <-.
           pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E3 (mg_apT _ _ S2 M1) I) as S3.
           exact (conj (gs_comp _ _ S3 (gs_comp _ _ S2 S1))
                       (mg_apT _ (typ_Record (row_Ext _ _ (row_Var _))) S3 (conj M2 I))).
        -- exact (spread_present_guard _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H S2 S1 (mg_apT _ _ S2 M1) M2).
      * exact (spread_present_guard _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H S2 S1 (mg_apT _ _ S2 M1) M2).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dC H E2. injection H as <- <- <- <- <-.
      pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E2 M1 (conj I I)) as S2.
      exact (conj (gs_comp _ _ S2 S1) (mg_apT _ (typ_Record (row_Var _)) S2 I)).
  - intros D G fs n s D' R n' fs' H HG.
    destruct fs as [|l e rest|l e rest]; simpl in H; [injection H as <- <- <- <- <-; exact (conj gs_id I)| | discriminate H].
    dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
    dF H E2. destruct (IHf _ _ _ _ _ _ _ _ _ E2 (mg_apC _ _ S1 HG)) as [S2 M2].
    injection H as <- <- <- <- <-.
    exact (conj (gs_comp _ _ S2 S1) (conj (mg_apT _ _ S2 M1) M2)).
  - intros D G w Ts x res ars n s D' T n' ars' H HG HTs Hres.
    destruct ars as [|e|tg e rest]; simpl in H.
    + injection H as <- <- <- <- <-. exact (conj gs_id Hres).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dC H E2. injection H as <- <- <- <- <-.
      pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E2 M1 (mg_apT _ _ S1 Hres)) as S2.
      exact (conj (gs_comp _ _ S2 S1) (mg_apT _ _ S2 (mg_apT _ _ S1 Hres))).
    + dI H E1.
      destruct (IHi _ _ _ _ _ _ _ _ _ E1
                  (mg_cons _ (sch_mono (tag_payload w Ts tg)) _ (mg_tag_payload _ _ _ HTs) HG)) as [S1 M1].
      dC H E2.
      pose proof (unify_coD_gsub _ _ _ _ _ _ _ _ _ E2 M1 (mg_apT _ _ S1 Hres)) as S2.
      pose proof (gs_comp _ _ S2 S1) as S12.
      dA H E3. injection H as <- <- <- <- <-.
      destruct (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ E3 (mg_apC _ _ S12 HG) (mg_map _ _ S12 HTs)
                  (mg_apT _ _ S2 (mg_apT _ _ S1 Hres))) as [S3 M3].
      exact (conj (gs_comp _ _ S3 S12) M3).
  - intros D G p Tp fs n s D' R n' fs' H HG HTp.
    destruct fs as [|l e rest|l e rest]; simpl in H; try discriminate H.
    + injection H as <- <- <- <- <-. exact (conj gs_id I).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dO H E2. destruct (IHo _ _ _ _ _ _ _ _ _ _ _ E2 (mg_apC _ _ S1 HG) (mg_apT _ _ S1 HTp)) as [S2 M2].
      injection H as <- <- <- <- <-.
      exact (conj (gs_comp _ _ S2 S1) (conj (mg_apT _ _ S2 M1) M2)).
    + destruct e; try discriminate H.
      dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 (mg_cons _ (sch_mono Tp) _ HTp HG)) as [S1 M1].
      dO H E2. destruct (IHo _ _ _ _ _ _ _ _ _ _ _ E2 (mg_apC _ _ S1 HG) (mg_apT _ _ S1 HTp)) as [S2 M2].
      injection H as <- <- <- <- <-.
      exact (conj (gs_comp _ _ S2 S1)
                  (conj (conj (mg_apT _ _ S2 (mg_apT _ _ S1 HTp)) (mg_apT _ _ S2 M1)) M2)).
Qed.

(* Every recursive type inside a type the algorithm infers for a closed
   program has a guarded body. *)
Theorem infer_guarded : forall fuel e D T e',
  infer_closed_elab fuel e = Some (D, T, e') -> mg T.
Proof.
  intros fuel e D T e' H. unfold infer_closed_elab in H.
  destruct (infer fuel d_any nil e 0) as [[[[[s D1] T1] n] e1]|] eqn:E; [|discriminate].
  injection H as <- <- <-.
  exact (proj2 (proj1 (infer_guard fuel) _ _ _ _ _ _ _ _ _ E mg_ctx_nil)).
Qed.

Corollary infer_closed_env_guarded : forall fuel e D T,
  infer_closed_env fuel e = Some (D, T) -> mg T.
Proof.
  intros fuel e D T H. unfold infer_closed_env in H.
  destruct (infer_closed_elab fuel e) as [[[D0 T0] e0]|] eqn:E; [|discriminate].
  injection H as <- <-. exact (infer_guarded _ _ _ _ _ E).
Qed.
