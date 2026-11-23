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

Lemma bind_k_gsub : forall D a T n s n',
  bind_k D a T n = Some (s, n') -> gsub s.
Proof.
  intros D a T n s n' H. unfold bind_k in H.
  destruct (lcb 0 T) eqn:Elc; cbn [negb] in H; [ | discriminate ].
  destruct (mgb T) eqn:Emg; cbn [negb] in H; [ | discriminate ].
  assert (Hlc : lct 0 T) by (apply lcb_lct; exact Elc).
  assert (Hmg : mg T) by (apply mgb_mg; exact Emg).
  destruct (AtomSetImpl.mem a (ftv_typ T)) eqn:Emem.
  - destruct (gdb false false a T && sat_b D (D a) (knot a T)) eqn:Eg; [ | discriminate ].
    inversion H; subst; clear H.
    apply Bool.andb_true_iff in Eg as [Hg _].
    apply gs_sbT; [ apply knot_lc; exact Hlc | apply mg_knot; assumption ].
  - destruct (sat_b D (D a) T); [ | discriminate ]. inversion H; subst; clear H.
    apply gs_sbT; assumption.
Qed.

Lemma rewrite_row_gsub : forall l av R n P T R' s n',
  rewrite_row l av R n = Some (P, T, R', s, n') -> gsub s.
Proof.
  intros l av R. induction R as [|r|l' T' R'' IH|l' P' T' R'' IH]; intros n P T R' s n' H; simpl in H.
  - injection H as <- <- <- <- <-. exact gs_id.
  - destruct (AtomSetImpl.mem r av); [discriminate|].
    injection H as <- <- <- <- <-.
    apply gs_sbR; repeat (split || exact I).
  - destruct (Nat.eqb l l'); [ injection H as <- <- <- <- <-; exact gs_id | ].
    destruct (rewrite_row l av R'' n) as [[[[[P0 T0] R3] s0] n1]|] eqn:E; [|discriminate].
    injection H as <- <- <- <- <-. exact (IH _ _ _ _ _ _ E).
  - destruct (Nat.eqb l l'); [ injection H as <- <- <- <- <-; exact gs_id | ].
    destruct (rewrite_row l av R'' n) as [[[[[P0 T0] R3] s0] n1]|] eqn:E; [|discriminate].
    injection H as <- <- <- <- <-. exact (IH _ _ _ _ _ _ E).
Qed.

Theorem unify_k_gsub : forall f,
  (forall D T1 T2 n s n', unify_k f D T1 T2 n = Some (s, n') -> gsub s) /\
  (forall D R1 R2 n s n', unify_kr f D R1 R2 n = Some (s, n') -> gsub s).
Proof.
  induction f as [|f IH]; [ split; intros; discriminate | ].
  destruct IH as [IHt IHr].
  split.
  - intros D T1 T2 n s n' H. cbn [unify_k] in H.
    destruct T1 as [| | | | | A B | R | a | i | B1 | w1 A1];
      destruct T2 as [| | | | | A' B' | R' | b | i' | B1' | w1' A1'];
      try discriminate H;
      try (injection H as <- <-; exact gs_id);
      try (exact (bind_k_gsub _ _ _ _ _ _ H));
      try (exact (IHt _ _ _ _ _ _ H)).
    + (* Arrow, Arrow *)
      destruct (unify_k f D A A' n) as [[s1 n1]|] eqn:E1; [|discriminate].
      destruct (unify_k f D (apT s1 B) (apT s1 B') n1) as [[s2 n2]|] eqn:E2; [|discriminate].
      injection H as <- <-.
      exact (gs_comp _ _ (IHt _ _ _ _ _ _ E2) (IHt _ _ _ _ _ _ E1)).
    + (* Record, Record *)
      exact (IHr _ _ _ _ _ _ H).
    + (* Var, Var *)
      destruct (Atom.eq_dec a b) as [->|]; [ injection H as <- <-; exact gs_id | ].
      destruct (finer_b (D b) (D a)); injection H as <- <-; apply gs_sbT; exact I.
    + (* Bvar, Bvar *)
      destruct (Nat.eqb i i'); [ injection H as <- <-; exact gs_id | discriminate ].
    + (* Mu, Mu *)
      destruct (match unify_k f D B1 B1' n with
                | Some (s0, n1) => if typ_eqb (apT s0 B1) (apT s0 B1') then Some (s0, n1) else None
                | None => None
                end) as [[s0 n0]|] eqn:Ein.
      * injection H as <- <-.
        destruct (unify_k f D B1 B1' n) as [[s1 n1]|] eqn:Eu; [ | discriminate Ein ].
        destruct (typ_eqb (apT s1 B1) (apT s1 B1')); [ | discriminate Ein ].
        injection Ein as <- <-. exact (IHt _ _ _ _ _ _ Eu).
      * exact (IHt _ _ _ _ _ _ H).
    + (* Grp, Grp *)
      destruct (gdecl_eq_dec w1 w1'); [ | discriminate ].
      exact (IHt _ _ _ _ _ _ H).
  - intros D R1 R2 n s n' H. cbn [unify_kr] in H.
    assert (Hgen : forall R1 R2,
      (match row_head R1 with
       | None => None
       | Some (l, P, T, R1') =>
           match rewrite_row l (frv_row R1) R2 n with
           | None => None
           | Some (P', T', R2', s0, n1) =>
               match unify_k f D (apT s0 P) P' n1 with
               | None => None
               | Some (sp, n2) =>
                   match unify_k f D (apT sp (apT s0 T)) (apT sp T') n2 with
                   | None => None
                   | Some (s1, n3) =>
                       match unify_kr f D (apR s1 (apR sp (apR s0 R1'))) (apR s1 (apR sp R2')) n3 with
                       | None => None
                       | Some (s2, n4) => Some (scomp s2 (scomp s1 (scomp sp s0)), n4)
                       end
                   end
               end
           end
       end) = Some (s, n') -> gsub s).
    { intros R1' R2' Hg.
      destruct (row_head R1') as [[[[l P] T] R1'']|]; [|discriminate].
      destruct (rewrite_row l (frv_row R1') R2' n) as [[[[[P' T'] R2''] s0] n1]|] eqn:Erw; [|discriminate].
      destruct (unify_k f D (apT s0 P) P' n1) as [[sp n2]|] eqn:Eu0; [|discriminate].
      destruct (unify_k f D (apT sp (apT s0 T)) (apT sp T') n2) as [[s1 n3]|] eqn:Eu1; [|discriminate].
      destruct (unify_kr f D (apR s1 (apR sp (apR s0 R1''))) (apR s1 (apR sp R2'')) n3)
        as [[s2 n4]|] eqn:Eu2; [|discriminate].
      injection Hg as <- <-.
      exact (gs_comp _ _ (IHr _ _ _ _ _ _ Eu2)
               (gs_comp _ _ (IHt _ _ _ _ _ _ Eu1)
                  (gs_comp _ _ (IHt _ _ _ _ _ _ Eu0) (rewrite_row_gsub _ _ _ _ _ _ _ _ _ Erw)))). }
    destruct R1 as [| r | l T R1' | lm Pm Tm Rm]; destruct R2 as [| q | l2 T2 R2' | lm2 Pm2 Tm2 Rm2];
      try (match type of H with context [row_head ?a] =>
             match type of H with context [rewrite_row _ _ ?b _] => exact (Hgen a b H) end end).
    + injection H as <- <-. exact gs_id.
    + destruct (occR q row_Empty) eqn:Eo; [discriminate|].
      destruct (mgbr row_Empty) eqn:Em; [|discriminate]. injection H as <- <-.
      apply gs_sbR; exact I.
    + eapply IHr. exact H.
    + destruct (occR r row_Empty) eqn:Eo; [discriminate|].
      destruct (mgbr row_Empty) eqn:Em; [|discriminate]. injection H as <- <-.
      apply gs_sbR; exact I.
    + destruct (Atom.eq_dec r q) as [->|]; [ injection H as <- <-; exact gs_id | ].
      injection H as <- <-. apply gs_sbR; exact I.
    + destruct (occR r (row_Ext l2 T2 R2')) eqn:Eo; [discriminate|].
      destruct (mgbr (row_Ext l2 T2 R2')) eqn:Em; [|discriminate]. injection H as <- <-.
      apply gs_sbR; [ exact (proj2 (occR_false _ _ Eo)) | apply mgbr_mgr; exact Em ].
    + destruct (occR r (row_Maybe lm2 Pm2 Tm2 Rm2)) eqn:Eo; [discriminate|].
      destruct (mgbr (row_Maybe lm2 Pm2 Tm2 Rm2)) eqn:Em; [|discriminate]. injection H as <- <-.
      apply gs_sbR; [ exact (proj2 (occR_false _ _ Eo)) | apply mgbr_mgr; exact Em ].
    + destruct (occR q (row_Ext l T R1')) eqn:Eo; [discriminate|].
      destruct (mgbr (row_Ext l T R1')) eqn:Em; [|discriminate]. injection H as <- <-.
      apply gs_sbR; [ exact (proj2 (occR_false _ _ Eo)) | apply mgbr_mgr; exact Em ].
    + destruct (occR q (row_Maybe lm Pm Tm Rm)) eqn:Eo; [discriminate|].
      destruct (mgbr (row_Maybe lm Pm Tm Rm)) eqn:Em; [|discriminate]. injection H as <- <-.
      apply gs_sbR; [ exact (proj2 (occR_false _ _ Eo)) | apply mgbr_mgr; exact Em ].
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

Lemma rewrite_row_mg : forall l av R n P T R' s n',
  rewrite_row l av R n = Some (P, T, R', s, n') -> mgr R -> mg P /\ mg T /\ mgr R'.
Proof.
  intros l av R. induction R as [|r|l' T' R'' IH|l' P' T' R'' IH]; intros n P T R' s n' H HR; simpl in H.
  - injection H as <- <- <- <- <-. exact (conj I (conj I I)).
  - destruct (AtomSetImpl.mem r av); [discriminate|].
    injection H as <- <- <- <- <-. exact (conj I (conj I I)).
  - destruct HR as [HT' HR''].
    destruct (Nat.eqb l l').
    + injection H as <- <- <- <- <-. exact (conj I (conj HT' HR'')).
    + destruct (rewrite_row l av R'' n) as [[[[[P0 T0] R3] s0] n1]|] eqn:E; [|discriminate].
      injection H as <- <- <- <- <-.
      destruct (IH _ _ _ _ _ _ E HR'') as [H0 [H1 H2]].
      pose proof (rewrite_row_gsub _ _ _ _ _ _ _ _ _ E) as Hs0.
      exact (conj H0 (conj H1 (conj (mg_apT _ _ Hs0 HT') H2))).
  - destruct HR as [HP' [HT' HR'']].
    destruct (Nat.eqb l l').
    + injection H as <- <- <- <- <-. exact (conj HP' (conj HT' HR'')).
    + destruct (rewrite_row l av R'' n) as [[[[[P0 T0] R3] s0] n1]|] eqn:E; [|discriminate].
      injection H as <- <- <- <- <-.
      destruct (IH _ _ _ _ _ _ E HR'') as [H0 [H1 H2]].
      pose proof (rewrite_row_gsub _ _ _ _ _ _ _ _ _ E) as Hs0.
      exact (conj H0 (conj H1 (conj (mg_apT _ _ Hs0 HP') (conj (mg_apT _ _ Hs0 HT') H2)))).
Qed.

Theorem unify_t_gsub : forall f,
  (forall D T1 T2 n s n', unify_t f D T1 T2 n = Some (s, n') ->
     mg T1 -> mg T2 -> gsub s) /\
  (forall D R1 R2 n s n', unify_r f D R1 R2 n = Some (s, n') ->
     mgr R1 -> mgr R2 -> gsub s) /\
  (forall D R1 R2 n s n', unify_pw f D R1 R2 n = Some (s, n') ->
     mgr R1 -> mgr R2 -> gsub s).
Proof.
  induction f as [|f IH]; [ refine (conj _ (conj _ _)); intros; discriminate | ].
  destruct IH as [IHt [IHr IHp]].
  refine (conj _ (conj _ _)).
  - intros D T1 T2 n s n' H H1 H2. simpl in H.
    destruct T1, T2; try discriminate;
      try (injection H as <- <-; exact gs_id);
      try (destruct (occT _ _) eqn:Eo; [discriminate|]; destruct (sat_b _ _ _); [|discriminate];
           injection H as <- <-; apply gs_sbT; [ exact (proj2 (occT_false _ _ Eo)) | assumption ]; fail);
      try (destruct (Atom.eq_dec _ _); [injection H as <- <-; exact gs_id|];
           destruct (finer_b _ _); injection H as <- <-; apply gs_sbT; exact I).
    + destruct (unify_t f D T1_1 T2_1 n) as [[s1 n1]|] eqn:E1; [|discriminate].
      destruct (unify_t f D (apT s1 T1_2) (apT s1 T2_2) n1) as [[s2 n2]|] eqn:E2; [|discriminate].
      injection H as <- <-.
      pose proof (IHt _ _ _ _ _ _ E1 (proj1 H1) (proj1 H2)) as Hs1.
      refine (gs_comp _ _ _ Hs1).
      eapply IHt; [ exact E2 | apply mg_apT; [ exact Hs1 | exact (proj2 H1) ]
                             | apply mg_apT; [ exact Hs1 | exact (proj2 H2) ] ].
    + eapply IHr; [exact H | exact H1 | exact H2].
    + destruct (gdecl_eq_dec _ _); [|discriminate].
      eapply IHt; [exact H | exact H1 | exact H2].
  - intros D R1 R2 n s n' H H1 H2. simpl in H.
    assert (Hgen : forall R1 R2, mgr R1 -> mgr R2 -> forall s n',
      (match row_head R1 with
       | None => None
       | Some (l, P, T, R1') =>
           match rewrite_row l (frv_row R1) R2 n with
           | None => None
           | Some (P', T', R2', s0, n1) =>
               match unify_t f D (apT s0 P) P' n1 with
               | None => None
               | Some (sp, n2) =>
                   match unify_t f D (apT sp (apT s0 T)) (apT sp T') n2 with
                   | None => None
                   | Some (s1, n3) =>
                       match unify_r f D (apR s1 (apR sp (apR s0 R1'))) (apR s1 (apR sp R2')) n3 with
                       | None => None
                       | Some (s2, n4) => Some (scomp s2 (scomp s1 (scomp sp s0)), n4)
                       end
                   end
               end
           end
       end) = Some (s, n') -> gsub s).
    { intros R1' R2' Hg1 Hg2 s' n'' Hg.
      destruct (row_head R1') as [[[[l P] T] R1'']|] eqn:Eh; [|discriminate].
      destruct (rewrite_row l (frv_row R1') R2' n) as [[[[[P' T'] R2''] s0] n1]|] eqn:Erw; [|discriminate].
      destruct (unify_t f D (apT s0 P) P' n1) as [[sp n2]|] eqn:Eu0; [|discriminate].
      destruct (unify_t f D (apT sp (apT s0 T)) (apT sp T') n2) as [[s1 n3]|] eqn:Eu1; [|discriminate].
      destruct (unify_r f D (apR s1 (apR sp (apR s0 R1''))) (apR s1 (apR sp R2'')) n3)
        as [[s2 n4]|] eqn:Eu2; [|discriminate].
      injection Hg as <- <-.
      destruct (row_head_mg _ _ _ _ _ Eh Hg1) as [HP [HT HR1]].
      destruct (rewrite_row_mg _ _ _ _ _ _ _ _ _ Erw Hg2) as [M0 [M1 M2]].
      pose proof (rewrite_row_gsub _ _ _ _ _ _ _ _ _ Erw) as S0.
      pose proof (IHt _ _ _ _ _ _ Eu0 (mg_apT _ _ S0 HP) M0) as Sp.
      pose proof (IHt _ _ _ _ _ _ Eu1 (mg_apT _ _ Sp (mg_apT _ _ S0 HT)) (mg_apT _ _ Sp M1)) as S1.
      pose proof (IHr _ _ _ _ _ _ Eu2
                    (mg_apR _ _ S1 (mg_apR _ _ Sp (mg_apR _ _ S0 HR1)))
                    (mg_apR _ _ S1 (mg_apR _ _ Sp M2))) as S2.
      exact (gs_comp _ _ S2 (gs_comp _ _ S1 (gs_comp _ _ Sp S0))). }
    destruct R1 as [|r|l T R1'|lm Pm Tm Rm]; destruct R2 as [|r2|l2 T2 R2'|lm2 Pm2 Tm2 Rm2];
      try (exact (Hgen _ _ H1 H2 _ _ H)).
    + injection H as <- <-. exact gs_id.
    + destruct (occR r2 row_Empty); [discriminate|]. injection H as <- <-.
      apply gs_sbR; exact I.
    + eapply IHr; [exact H | exact H2 | exact H1].
    + destruct (occR r row_Empty); [discriminate|]. injection H as <- <-.
      apply gs_sbR; exact I.
    + destruct (Atom.eq_dec r r2); [injection H as <- <-; exact gs_id|].
      injection H as <- <-. apply gs_sbR; exact I.
    + destruct (occR r _) eqn:Eo; [discriminate|]. injection H as <- <-.
      apply gs_sbR; [ exact (proj2 (occR_false _ _ Eo)) | exact H2 ].
    + destruct (occR r _) eqn:Eo; [discriminate|]. injection H as <- <-.
      apply gs_sbR; [ exact (proj2 (occR_false _ _ Eo)) | exact H2 ].
    + destruct (occR r2 _) eqn:Eo; [discriminate|]. injection H as <- <-.
      apply gs_sbR; [ exact (proj2 (occR_false _ _ Eo)) | exact H1 ].
    + destruct (occR r2 _) eqn:Eo; [discriminate|]. injection H as <- <-.
      apply gs_sbR; [ exact (proj2 (occR_false _ _ Eo)) | exact H1 ].
  - intros D R1 R2 n s n' H H1 H2. simpl in H.
    destruct R1 as [|r|l T R1'|lm Pm Tm Rm], R2 as [|r2|l2 T2 R2'|lm2 Pm2 Tm2 Rm2]; try discriminate.
    + injection H as <- <-. exact gs_id.
    + destruct (Nat.eqb l l2); [|discriminate].
      destruct (unify_t f D T T2 n) as [[s1 n1]|] eqn:E1; [|discriminate].
      destruct (unify_pw f D (apR s1 R1') (apR s1 R2') n1) as [[s2 n2]|] eqn:E2; [|discriminate].
      injection H as <- <-.
      destruct H1 as [H1a H1b]. destruct H2 as [H2a H2b].
      pose proof (IHt _ _ _ _ _ _ E1 H1a H2a) as Hs1.
      refine (gs_comp _ _ _ Hs1).
      eapply IHp; [ exact E2 | apply mg_apR; [ exact Hs1 | exact H1b ]
                             | apply mg_apR; [ exact Hs1 | exact H2b ] ].
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
  intros w Ts tg H. unfold tag_payload. destruct (nth_error w tg) as [cs|]; [|exact I].
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

Lemma unify_co_gsub : forall f D T1 T2 n s cs n',
  unify_co f D T1 T2 n = Some (s, cs, n') -> mg T1 -> mg T2 -> gsub s.
Proof.
  intros f D T1 T2 n s cs n' H H1 H2. unfold unify_co in H.
  destruct (unify_t f D T1 T2 n) as [[s0 n0]|] eqn:E1.
  - injection H as <- <- <-. exact (proj1 (unify_t_gsub f) _ _ _ _ _ _ E1 H1 H2).
  - destruct (unify_k f D T1 T2 n) as [[s0 n0]|] eqn:E2; [|discriminate].
    destruct (coerce_dec f D (apT s0 T1) (apT s0 T2)); [|discriminate].
    injection H as <- <- <-. exact (proj1 (unify_k_gsub f) _ _ _ _ _ _ E2).
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

Lemma bin_arg_mg : forall ora D o A B T0,
  (forall a, mg (ora a)) -> bin_arg false ora D o A B = Some T0 -> mg T0.
Proof.
  intros ora D o A B T0 Hora EB. unfold bin_arg in EB. destruct (kind o); try discriminate.
  - injection EB as <-. exact I.
  - destruct (cmp_ty B) eqn:C2.
    + injection EB as <-. destruct B; simpl in C2; try discriminate; exact I.
    + destruct (cmp_ty A) eqn:C1.
      * injection EB as <-. destruct A; simpl in C1; try discriminate; exact I.
      * destruct (open_var A) as [a|]; [|destruct (open_var B) as [b|]; [|discriminate]];
          injection EB as <-; apply Hora.
Qed.

Lemma bin_ty_mg : forall o T R, bin_ty o T = Some R -> mg R.
Proof.
  intros o T R ER. unfold bin_ty in ER. destruct (kind o), T; try discriminate;
    injection ER as <-; exact I.
Qed.

Ltac dI H E :=
  match type of H with context [infer ?f ?l ?o ?D ?G ?e ?n] =>
    destruct (infer f l o D G e n) as [[[[[? ?] ?] ?] ?]|] eqn:E; [|discriminate H] end.

Ltac dF H E :=
  match type of H with context [infer_fields ?f ?l ?o ?D ?G ?e ?n] =>
    destruct (infer_fields f l o D G e n) as [[[[[? ?] ?] ?] ?]|] eqn:E; [|discriminate H] end.

Ltac dA H E :=
  match type of H with context [infer_arms ?f ?l ?o ?D ?G ?w ?Ts ?x ?r ?a ?n] =>
    destruct (infer_arms f l o D G w Ts x r a n) as [[[[[? ?] ?] ?] ?]|] eqn:E; [|discriminate H] end.

Ltac dC H E :=
  match type of H with context [unify_co ?f ?D ?A ?B ?n] =>
    destruct (unify_co f D A B n) as [[[? ?] ?]|] eqn:E; [|discriminate H] end.

Ltac dP H E :=
  match type of H with context [unify_grp ?f ?D ?fs ?A ?B ?n] =>
    destruct (unify_grp f D fs A B n) as [[[? ?] ?]|] eqn:E; [|discriminate H] end.

Lemma obj_row_mg : forall fs n a, mgr (obj_row fs n (row_Var a)).
Proof.
  induction fs as [|l e rest IH|l e rest IH]; intros n a; simpl.
  - exact I.
  - split; [ exact I | apply IH ].
  - split; [ exact I | apply IH ].
Qed.

Ltac dO H E :=
  match type of H with context [infer_obj ?f ?l ?o ?D ?G ?p ?Tp ?e ?n] =>
    destruct (infer_obj f l o D G p Tp e n) as [[[[[? ?] ?] ?] ?]|] eqn:E; [|discriminate H] end.

Ltac dT H E :=
  match type of H with context [tie_obj ?f ?D ?fs ?R ?Rsl ?n] =>
    destruct (tie_obj f D fs R Rsl n) as [[[? ?] ?]|] eqn:E; [|discriminate H] end.

Lemma tie_obj_gsub : forall f D fs R Rsl n s n' fs2,
  tie_obj f D fs R Rsl n = Some (s, n', fs2) -> mgr R -> mgr Rsl -> gsub s.
Proof.
  intros f D fs. induction fs as [|l e rest IH|l e rest IH];
    intros R Rsl n s n' fs2 H HR HRsl;
    destruct R as [|r|l1 T R'|l1 P0 T0 R'], Rsl as [|r2|l2 A Rsl'|l2 P2 T2 R2'];
    simpl in H; try discriminate H.
  - injection H as <- <- <-. exact gs_id.
  - destruct (Nat.eqb l l1 && Nat.eqb l l2); [ | discriminate H ].
    destruct (unify_co f D T A n) as [[[s1 cs] n1]|] eqn:E1; [ | discriminate H ].
    destruct (tie_obj f D rest (apR s1 R') (apR s1 Rsl') n1) as [[[s2 n2] rest']|] eqn:E2; [ | discriminate H ].
    injection H as <- <- <-. destruct HR as [HT HR']. destruct HRsl as [HA HRsl'].
    pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E1 HT HA) as S1.
    exact (gs_comp _ _ (IH _ _ _ _ _ _ E2 (mg_apR _ _ S1 HR') (mg_apR _ _ S1 HRsl')) S1).
  - destruct (Nat.eqb l l1 && Nat.eqb l l2); [ | discriminate H ].
    destruct (unify_co f D T A n) as [[[s1 cs] n1]|] eqn:E1; [ | discriminate H ].
    destruct (tie_obj f D rest (apR s1 R') (apR s1 Rsl') n1) as [[[s2 n2] rest']|] eqn:E2; [ | discriminate H ].
    injection H as <- <- <-. destruct HR as [HT HR']. destruct HRsl as [HA HRsl'].
    pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E1 HT HA) as S1.
    exact (gs_comp _ _ (IH _ _ _ _ _ _ E2 (mg_apR _ _ S1 HR') (mg_apR _ _ S1 HRsl')) S1).
Qed.

Lemma unify_mem_gsub : forall f D e T A n s n' e',
  unify_mem f D e T A n = Some (s, n', e') -> mg T -> mg A -> gsub s.
Proof.
  intros f D e T A n s n' e' H HT HA. unfold unify_mem in H.
  destruct (unify_t f D T A n) as [[s0 n0]|] eqn:E.
  - injection H as <- <- <-. exact (proj1 (unify_t_gsub f) _ _ _ _ _ _ E HT HA).
  - destruct e as [ | | | | | | b | | | | | | | | | | | | | | | | ]; try discriminate H.
    destruct T as [ | | | | | X Y | | | | | ]; try discriminate H.
    destruct A as [ | | | | | X' Y' | | | | | ]; try discriminate H.
    destruct (unify_t f D X X' n) as [[s1 n1]|] eqn:E1; [ | discriminate H ].
    destruct (unify_co f D (apT s1 Y) (apT s1 Y') n1) as [[[s2 cs] n2]|] eqn:E2; [ | discriminate H ].
    injection H as <- <- <-. destruct HT as [HX HY]. destruct HA as [HX' HY'].
    pose proof ((proj1 (unify_t_gsub f)) _ _ _ _ _ _ E1 HX HX') as S1.
    pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E2 (mg_apT _ _ S1 HY) (mg_apT _ _ S1 HY')) as S2.
    exact (gs_comp _ _ S2 S1).
Qed.

Lemma unify_grp_gsub : forall f D fs R1 R2 n s n' fs2,
  unify_grp f D fs R1 R2 n = Some (s, n', fs2) -> mgr R1 -> mgr R2 -> gsub s.
Proof.
  induction f as [|f IH]; intros D fs R1 R2 n s n' fs2 H H1 H2; [ discriminate | ].
  cbn [unify_grp] in H.
  destruct fs as [|l e rest|l e rest]; destruct R1 as [|r|l1 T R1'|lm Pm Tm Rm];
    destruct R2 as [|r2|l2 A R2'|lm2 Pm2 Tm2 Rm2]; try discriminate H.
  - injection H as <- <- <-. exact gs_id.
  - destruct (Nat.eqb l l1 && Nat.eqb l l2); [ | discriminate H ].
    destruct (unify_mem f D e T A n) as [[[s1 n1] e']|] eqn:E1; [ | discriminate H ].
    destruct (unify_grp f D rest (apR s1 R1') (apR s1 R2') n1) as [[[s2 n2] rest']|] eqn:E2; [ | discriminate H ].
    injection H as <- <- <-. destruct H1 as [HT HR1]. destruct H2 as [HA HR2].
    pose proof (unify_mem_gsub _ _ _ _ _ _ _ _ _ E1 HT HA) as S1.
    exact (gs_comp _ _ (IH _ _ _ _ _ _ _ _ E2 (mg_apR _ _ S1 HR1) (mg_apR _ _ S1 HR2)) S1).
Qed.

Theorem infer_guard : forall f ora, (forall a, mg (ora a)) ->
  (forall D G e n s D' T n' e', infer f false ora D G e n = Some (s, D', T, n', e') ->
     mg_ctx G -> gsub s /\ mg T) /\
  (forall D G fs n s D' R n' fs', infer_fields f false ora D G fs n = Some (s, D', R, n', fs') ->
     mg_ctx G -> gsub s /\ mgr R) /\
  (forall D G w Ts x res ars n s D' T n' ars',
     infer_arms f false ora D G w Ts x res ars n = Some (s, D', T, n', ars') ->
     mg_ctx G -> Forall mg Ts -> mg res -> gsub s /\ mg T) /\
  (forall D G p Tp fs n s D' R n' fs', infer_obj f false ora D G p Tp fs n = Some (s, D', R, n', fs') ->
     mg_ctx G -> mg Tp -> gsub s /\ mgr R).
Proof.
  induction f as [|f IH]; intros ora Hora; [refine (conj _ (conj _ (conj _ _))); intros; discriminate|].
  destruct (IH ora Hora) as [IHi [IHf [IHa IHo]]].
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
      pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E3 (mg_apT _ _ S2 M1) (conj M2 I)) as S3.
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
      pose proof (unify_grp_gsub _ _ _ _ _ _ _ _ _ E2 M1
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
        pose proof (tie_obj_gsub _ _ _ _ _ _ _ _ _ E2 M1 (mg_apR _ _ S1 (group_row_mg fs n))) as S2.
        exact (conj (gs_comp _ _ S2 S1)
                    (mg_apT _ (typ_Record (group_row fs n)) (gs_comp _ _ S2 S1) (group_row_mg fs n))).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dC H E2. injection H as <- <- <- <- <-.
      pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E2 M1 (conj I I)) as S2.
      exact (conj (gs_comp _ _ S2 S1) (mg_apT _ (typ_Var _) S2 I)).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dC H E2.
      pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E2 M1 I) as S2.
      dI H E3. destruct (IHi _ _ _ _ _ _ _ _ _ E3 (mg_apC _ _ S2 (mg_apC _ _ S1 HG))) as [S3 M2].
      dI H E4. destruct (IHi _ _ _ _ _ _ _ _ _ E4
                           (mg_apC _ _ S3 (mg_apC _ _ S2 (mg_apC _ _ S1 HG)))) as [S4 M3].
      dC H E5. injection H as <- <- <- <- <-.
      pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E5 (mg_apT _ _ S4 M2) M3) as S5.
      exact (conj (gs_comp _ _ S5 (gs_comp _ _ S4 (gs_comp _ _ S3 (gs_comp _ _ S2 S1))))
                  (mg_apT _ _ S5 M3)).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dI H E2. destruct (IHi _ _ _ _ _ _ _ _ _ E2 (mg_apC _ _ S1 HG)) as [S2 M2].
      destruct (is_generic_op o).
      * dC H E3.
        pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E3 (mg_apT _ _ S2 M1) I) as S3.
        dC H E4. injection H as <- <- <- <- <-.
        pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E4 (mg_apT _ _ S3 M2) (mg_apT _ (typ_Var _) S3 I)) as S4.
        exact (conj (gs_comp _ _ S4 (gs_comp _ _ S3 (gs_comp _ _ S2 S1)))
                    (mg_apT _ _ S4 (mg_apT _ (typ_Var _) S3 I))).
      * match type of H with context [bin_arg ?l ?o0 ?D0 ?op ?A ?B] =>
          destruct (bin_arg l o0 D0 op A B) as [T0|] eqn:EB; [|discriminate H] end.
        pose proof (bin_arg_mg _ _ _ _ _ _ Hora EB) as MT.
        dC H E3.
        pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E3 (mg_apT _ _ S2 M1) MT) as S3.
        dC H E4.
        match type of H with context [bin_ty ?o0 ?A] =>
          destruct (bin_ty o0 A) as [R|] eqn:ER; [|discriminate H] end.
        injection H as <- <- <- <- <-.
        pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E4 (mg_apT _ _ S3 M2) MT) as S4.
        exact (conj (gs_comp _ _ S4 (gs_comp _ _ S3 (gs_comp _ _ S2 S1))) (bin_ty_mg _ _ _ ER)).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dC H E2. injection H as <- <- <- <- <-.
      pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E2 M1 I) as S2.
      exact (conj (gs_comp _ _ S2 S1) I).
    + destruct (Nat.ltb tg (length w)); [|discriminate].
      dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      match type of H with context [fresh_tys ?m (nparams w)] => pose proof (mg_fresh_tys (nparams w) m) as HTs end.
      dC H E2. injection H as <- <- <- <- <-.
      pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E2 M1 (mg_tag_payload _ _ _ HTs)) as S2.
      exact (conj (gs_comp _ _ S2 S1) (mg_apT _ (typ_Grp _ (spine _)) S2 (mg_spine _ HTs))).
    + destruct (arms_wf_b w ars); [|discriminate].
      dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dC H E2.
      match type of H with context [fresh_tys ?m (nparams w)] => pose proof (mg_fresh_tys (nparams w) m) as HTs end.
      pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E2 M1 (mg_spine _ HTs)) as S2.
      dA H E3. injection H as <- <- <- <- <-.
      destruct (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ E3 (mg_apC _ _ S2 (mg_apC _ _ S1 HG))
                  (mg_map _ _ S2 HTs) I) as [S3 M3].
      exact (conj (gs_comp _ _ S3 (gs_comp _ _ S2 S1)) M3).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dI H E2. destruct (IHi _ _ _ _ _ _ _ _ _ E2 (mg_apC _ _ S1 HG)) as [S2 M2].
      dC H E3. injection H as <- <- <- <- <-.
      pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E3 (mg_apT _ _ S2 M1) (conj I (conj M2 I))) as S3.
      exact (conj (gs_comp _ _ S3 (gs_comp _ _ S2 S1)) (mg_apT _ (typ_Record (row_Ext _ _ (row_Var _))) S3 (conj M2 I))).
    + dI H E1. destruct (IHi _ _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      dC H E2. injection H as <- <- <- <- <-.
      pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E2 M1 (conj I I)) as S2.
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
      pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E2 M1 (mg_apT _ _ S1 Hres)) as S2.
      exact (conj (gs_comp _ _ S2 S1) (mg_apT _ _ S2 (mg_apT _ _ S1 Hres))).
    + dI H E1.
      destruct (IHi _ _ _ _ _ _ _ _ _ E1
                  (mg_cons _ (sch_mono (tag_payload w Ts tg)) _ (mg_tag_payload _ _ _ HTs) HG)) as [S1 M1].
      dC H E2.
      pose proof (unify_co_gsub _ _ _ _ _ _ _ _ E2 M1 (mg_apT _ _ S1 Hres)) as S2.
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

Lemma resolved_mg : forall s a, mg (resolved s a).
Proof.
  intros s a. unfold resolved. destruct (apT s (typ_Var a)); simpl; exact I.
Qed.

(* Every recursive type inside a type the algorithm infers for a closed
   program has a guarded body. *)
Theorem infer_guarded : forall fuel e D T e',
  infer_closed_elab fuel e = Some (D, T, e') -> mg T.
Proof.
  intros fuel e D T e' H. unfold infer_closed_elab in H.
  destruct (infer fuel true (fun _ => typ_Int) d_any nil e 0) as [[[[[s0 D00] T00] n0] e00]|]; [|discriminate].
  destruct (infer fuel false (resolved s0) d_any nil e 0) as [[[[[s D1] T1] n] e1]|] eqn:E; [|discriminate].
  injection H as <- <- <-.
  exact (proj2 (proj1 (infer_guard fuel (resolved s0) (resolved_mg s0)) _ _ _ _ _ _ _ _ _ E mg_ctx_nil)).
Qed.

Corollary infer_closed_env_guarded : forall fuel e D T,
  infer_closed_env fuel e = Some (D, T) -> mg T.
Proof.
  intros fuel e D T H. unfold infer_closed_env in H.
  destruct (infer_closed_elab fuel e) as [[[D0 T0] e0]|] eqn:E; [|discriminate].
  injection H as <- <-. exact (infer_guarded _ _ _ _ _ E).
Qed.
