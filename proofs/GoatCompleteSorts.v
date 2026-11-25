(* Completeness of algorithm W, stage 7.6e: the factoring substitution for the
   variables a sort invents (docs/design/phase7-proof-plan.md).

   Binding a sorted variable to a type renames each variable of the type whose
   sort is coarser than the sort to a fresh variable of that sort ([push_sort]),
   and each such row variable to a fresh row variable of that sort that lacks
   what it lacked ([push_sort_r]).  A substitution [Sg] that unifies the two
   types knows nothing of the fresh variables, so completeness has to invent
   its extension [S2]: the fresh variable takes the image of the variable it
   renames.  [S2] respects the new environment because the image satisfies the
   sort, which is what [sat_teq] (stage 7.6b) lets the caller read off the
   image of the bound variable.

   [S2] agrees with [Sg] on its other component, and composing it with the
   renaming gives [Sg] back on the atoms below the supply [n], where the types
   being unified live.  Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatSatTeq.
Require Import Goat.GoatCompleteEr.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

Definition supd (Sg : sub) (a : atom) (T : typ) : sub :=
  Sub (fun x => if Atom.eq_dec x a then T else sT Sg x) (sR Sg).

Definition srupd (Sg : sub) (r : atom) (R : row) : sub :=
  Sub (sT Sg) (fun x => if Atom.eq_dec x r then R else sR Sg x).

Lemma dec_same : forall (A : Type) (a : atom) (X Y : A), (if Atom.eq_dec a a then X else Y) = X.
Proof. intros. destruct (Atom.eq_dec a a); [ reflexivity | exfalso; congruence ]. Qed.

Lemma dec_diff : forall (A : Type) (a b : atom) (X Y : A),
  a <> b -> (if Atom.eq_dec a b then X else Y) = Y.
Proof. intros. destruct (Atom.eq_dec a b); [ exfalso; congruence | reflexivity ]. Qed.

(* The extension [S2] sends each atom to a type [Sg] sends some atom to: it
   invents no type, so a bound on the atoms of [Sg]'s images bounds [S2]'s. *)
Definition Img (Sg S2 : sub) : Prop := forall y, exists z, sT S2 y = sT Sg z.

Lemma Img_refl : forall Sg, Img Sg Sg.
Proof. intros Sg y. exists y. reflexivity. Qed.

Lemma Img_trans : forall S1 S2 S3, Img S1 S2 -> Img S2 S3 -> Img S1 S3.
Proof.
  intros S1 S2 S3 H12 H23 y. destruct (H23 y) as [z Hz]. destruct (H12 z) as [w Hw].
  exists w. rewrite Hz. exact Hw.
Qed.

Lemma Img_supd : forall Sg a b, Img Sg (supd Sg a (sT Sg b)).
Proof.
  intros Sg a b y. cbn [supd sT]. destruct (Atom.eq_dec y a) as [_|_]; [ exists b | exists y ]; reflexivity.
Qed.

Lemma Img_bound : forall (P : typ -> Prop) Sg S2,
  Img Sg S2 -> (forall z, P (sT Sg z)) -> forall y, P (sT S2 y).
Proof. intros P Sg S2 H HP y. destruct (H y) as [z ->]. exact (HP z). Qed.

Lemma Img_sT : forall Sg S2, sT S2 = sT Sg -> Img Sg S2.
Proof. intros Sg S2 H y. exists y. rewrite H. reflexivity. Qed.

(* The same for rows: each row [S2] sends a row variable to is a row [Sg] sends
   some row variable to. *)
Definition RImg (Sg S2 : sub) : Prop := forall r, exists q, sR S2 r = sR Sg q.

Lemma RImg_refl : forall Sg, RImg Sg Sg.
Proof. intros Sg r. exists r. reflexivity. Qed.

Lemma RImg_trans : forall S1 S2 S3, RImg S1 S2 -> RImg S2 S3 -> RImg S1 S3.
Proof.
  intros S1 S2 S3 H12 H23 r. destruct (H23 r) as [q Hq]. destruct (H12 q) as [w Hw].
  exists w. rewrite Hq. exact Hw.
Qed.

Lemma RImg_sR : forall Sg S2, sR S2 = sR Sg -> RImg Sg S2.
Proof. intros Sg S2 H r. exists r. rewrite H. reflexivity. Qed.

(* What an extension may mention.  If the images [Sg] gives to types and rows
   mention type variables only from [E] and row variables only from [F], [Cov]
   says the extension's images do too.  [Img] and [RImg] say the extension's
   images are images of [Sg]; [Cov] is weaker, and it is what a step through
   [rewrite_row] can promise, because the field a row variable is bound to is
   known only up to [teq] and need not be an image of any atom. *)
Definition Bnd (E F : atom -> Prop) (S : sub) : Prop :=
  (forall z a, a `in` ftv_typ (sT S z) -> E a) /\ (forall z q, q `in` frv_typ (sT S z) -> F q) /\
  (forall r a, a `in` ftv_row (sR S r) -> E a) /\ (forall r q, q `in` frv_row (sR S r) -> F q).

Definition Cov (Sg S2 : sub) : Prop := forall E F, Bnd E F Sg -> Bnd E F S2.

Lemma Cov_refl : forall Sg, Cov Sg Sg.
Proof. intros Sg E F H. exact H. Qed.

Lemma Cov_trans : forall S1 S2 S3, Cov S1 S2 -> Cov S2 S3 -> Cov S1 S3.
Proof. intros S1 S2 S3 H12 H23 E F H. exact (H23 E F (H12 E F H)). Qed.

Lemma Cov_of_imgs : forall Sg S2, Img Sg S2 -> RImg Sg S2 -> Cov Sg S2.
Proof.
  intros Sg S2 HI HR E F (B1 & B2 & B3 & B4). refine (conj _ (conj _ (conj _ _))).
  - intros z a Ha. destruct (HI z) as [w Hw]. rewrite Hw in Ha. exact (B1 w a Ha).
  - intros z q Hq. destruct (HI z) as [w Hw]. rewrite Hw in Hq. exact (B2 w q Hq).
  - intros r a Ha. destruct (HR r) as [w Hw]. rewrite Hw in Ha. exact (B3 w a Ha).
  - intros r q Hq. destruct (HR r) as [w Hw]. rewrite Hw in Hq. exact (B4 w q Hq).
Qed.

Lemma Bnd_supd : forall E F S a U, Bnd E F S ->
  (forall x, x `in` ftv_typ U -> E x) -> (forall q, q `in` frv_typ U -> F q) -> Bnd E F (supd S a U).
Proof.
  intros E F S a U (B1 & B2 & B3 & B4) HE HF. refine (conj _ (conj _ (conj _ _))).
  - intros z x Hx. cbn [supd sT] in Hx. destruct (Atom.eq_dec z a) as [_|_]; [ exact (HE x Hx) | exact (B1 z x Hx) ].
  - intros z q Hq. cbn [supd sT] in Hq. destruct (Atom.eq_dec z a) as [_|_]; [ exact (HF q Hq) | exact (B2 z q Hq) ].
  - exact B3.
  - exact B4.
Qed.

Lemma Bnd_srupd : forall E F S r R, Bnd E F S ->
  (forall x, x `in` ftv_row R -> E x) -> (forall q, q `in` frv_row R -> F q) -> Bnd E F (srupd S r R).
Proof.
  intros E F S r R (B1 & B2 & B3 & B4) HE HF. refine (conj _ (conj _ (conj _ _))).
  - exact B1.
  - exact B2.
  - intros z x Hx. cbn [srupd sR] in Hx. destruct (Atom.eq_dec z r) as [_|_]; [ exact (HE x Hx) | exact (B3 z x Hx) ].
  - intros z q Hq. cbn [srupd sR] in Hq. destruct (Atom.eq_dec z r) as [_|_]; [ exact (HF q Hq) | exact (B4 z q Hq) ].
Qed.

(* The atoms of a presence, a field and a row lie in [E] and [F]. *)
Definition AIn (E F : atom -> Prop) (P T : typ) (R : row) : Prop :=
  (forall x, x `in` ftv_typ P -> E x) /\ (forall x, x `in` ftv_typ T -> E x) /\ (forall x, x `in` ftv_row R -> E x) /\
  (forall q, q `in` frv_typ P -> F q) /\ (forall q, q `in` frv_typ T -> F q) /\ (forall q, q `in` frv_row R -> F q).

Lemma push_sort_complete : forall l D n k Sg D1,
  DOk D n -> KR D D1 Sg ->
  (forall b, In b l -> sat D1 k (sT Sg b)) ->
  (forall b, In b l -> forall m, n <= m -> b <> ea m) ->
  forall sp D' n', push_sort D k l n = (sp, D', n') ->
  exists S2, KR D' D1 S2 /\ sR S2 = sR Sg /\
    (forall x, (forall m, n <= m -> x <> ea m) -> sT Sg x = apT S2 (sT sp x)) /\ Img Sg S2.
Proof.
  induction l as [|b l IH]; intros D n k Sg D1 Hd HK Hs Hnew sp D' n' E.
  - cbn [push_sort] in E. inversion E; subst. exists Sg.
    split; [ exact HK | split; [ reflexivity | split; [ intros x _; reflexivity | apply Img_refl ] ] ].
  - cbn [push_sort] in E. destruct (finer_b (D b) k) eqn:Ef.
    + exact (IH D n k Sg D1 Hd HK (fun b' H => Hs b' (or_intror H))
               (fun b' H => Hnew b' (or_intror H)) sp D' n' E).
    + destruct (finer_b k (D b)) eqn:Ef2;
        [ | destruct (push_sort D k l n) as [[s D''] n''] eqn:E1;
            inversion E; subst sp D' n';
            destruct (IH D n k Sg D1 Hd HK (fun b' H => Hs b' (or_intror H))
                        (fun b' H => Hnew b' (or_intror H)) s D'' n'' E1) as (S2 & H1 & H2 & H3 & H5);
            exists S2; refine (conj H1 (conj H2 (conj _ H5)));
            intros x Hx;
            change (sT Sg x = apT S2 (apT s (sT (sbT b typ_Float) x))); cbn [sT sbT];
            destruct (Atom.eq_dec x b) as [->|Hne];
            [ change (sT Sg b = apT S2 typ_Float);
              pose proof (proj1 HK b) as Hsb; pose proof (Hs b (or_introl eq_refl)) as Hsk;
              destruct (finer_b_cmp _ _ Ef2 Ef) as [[Hk1 Hk2]|[Hk1 Hk2]];
              [ rewrite Hk2 in Hsb; rewrite Hk1 in Hsk; exact (quot_literal_float D1 _ Hsb Hsk)
              | rewrite Hk2 in Hsb; rewrite Hk1 in Hsk; exact (quot_literal_float D1 _ Hsk Hsb) ]
            | exact (H3 x Hx) ] ].
      destruct (push_sort (upd D (ea n) k) k l (Datatypes.S n)) as [[s D''] n''] eqn:E1.
      inversion E; subst sp D' n'.
      set (S' := supd Sg (ea n) (sT Sg b)).
      assert (HK' : KR (upd D (ea n) k) D1 S').
      { split.
        - intros a. cbn [sT S' supd]. destruct (Atom.eq_dec a (ea n)) as [->|Hne].
          + rewrite upd_same. exact (Hs b (or_introl eq_refl)).
          + rewrite upd_other by exact Hne. exact (proj1 HK a).
        - intros r. cbn [sR S' supd drk upd]. exact (proj2 HK r). }
      assert (Hs' : forall b', In b' l -> sat D1 k (sT S' b')).
      { intros b' H. cbn [sT S' supd]. destruct (Atom.eq_dec b' (ea n)) as [E2|Hne].
        - exfalso. exact (Hnew b' (or_intror H) n (le_n n) E2).
        - exact (Hs b' (or_intror H)). }
      assert (Hnew' : forall b', In b' l -> forall m, Datatypes.S n <= m -> b' <> ea m).
      { intros b' H m Hm. apply (Hnew b' (or_intror H)). lia. }
      destruct (IH (upd D (ea n) k) (Datatypes.S n) k S' D1 (DOk_upd D n k Hd) HK' Hs' Hnew'
                  s D'' n'' E1) as (S2 & H1 & H2 & H3 & H5).
      exists S2. split; [ exact H1 | split; [ rewrite H2; reflexivity | split; [ | exact (Img_trans _ _ _ (Img_supd Sg (ea n) b) H5) ] ] ].
      intros x Hx.
      assert (Hn : forall m, Datatypes.S n <= m -> ea n <> ea m)
        by (intros m Hm Heq; apply ea_inj in Heq; lia).
      change (sT (scomp s (sbT b (typ_Var (ea n)))) x)
        with (apT s (sT (sbT b (typ_Var (ea n))) x)).
      cbn [sT sbT]. destruct (Atom.eq_dec x b) as [->|Hne]; cbn iota.
      * pose proof (H3 (ea n) Hn) as H4. cbn [sT S' supd] in H4.
        rewrite dec_same in H4. exact H4.
      * assert (Hxn : x <> ea n) by (intros Heq; exact (Hx n (le_n n) Heq)).
        pose proof (H3 x (fun m Hm => Hx m ltac:(lia))) as H4. cbn [sT S' supd] in H4.
        rewrite (dec_diff _ _ _ _ _ Hxn) in H4. exact H4.
Qed.

Lemma push_sort_r_complete : forall l D n k Sg D1,
  DOk D n -> KR D D1 Sg ->
  (forall q, In q l -> rsat D1 k (sR Sg q)) ->
  (forall q, In q l -> forall m, n <= m -> q <> ea m) ->
  forall sr D' n', push_sort_r D k l n = (sr, D', n') ->
  exists S2, KR D' D1 S2 /\ sT S2 = sT Sg /\
    (forall r, (forall m, n <= m -> r <> ea m) -> sR Sg r = apR S2 (sR sr r)) /\ RImg Sg S2.
Proof.
  induction l as [|q l IH]; intros D n k Sg D1 Hd HK Hs Hnew sr D' n' E.
  - cbn [push_sort_r] in E. inversion E; subst. exists Sg.
    split; [ exact HK | split; [ reflexivity | split; [ intros x _; reflexivity | apply RImg_refl ] ] ].
  - cbn [push_sort_r] in E. destruct (finer_b (rk_sort (drk D q)) k) eqn:Ef.
    + exact (IH D n k Sg D1 Hd HK (fun b' H => Hs b' (or_intror H))
               (fun b' H => Hnew b' (or_intror H)) sr D' n' E).
    + destruct (finer_b k (rk_sort (drk D q))) eqn:Ef2;
        [ | exact (IH D n k Sg D1 Hd HK (fun b' H => Hs b' (or_intror H))
                     (fun b' H => Hnew b' (or_intror H)) sr D' n' E) ].
      destruct (push_sort_r (rupd D (ea n) (RK k (rk_lacks (drk D q)))) k l (Datatypes.S n))
        as [[s D''] n''] eqn:E1.
      inversion E; subst sr D' n'.
      set (S' := srupd Sg (ea n) (sR Sg q)).
      assert (HK' : KR (rupd D (ea n) (RK k (rk_lacks (drk D q)))) D1 S').
      { split.
        - intros a. cbn [sT S' srupd dsort rupd]. exact (proj1 HK a).
        - intros r. cbn [sR S' srupd drk rupd]. destruct (Atom.eq_dec r (ea n)) as [->|Hne].
          + split; [ exact (Hs q (or_introl eq_refl)) | ].
            intros l0 Hl0. exact (proj2 (proj2 HK q) l0 Hl0).
          + exact (proj2 HK r). }
      assert (Hs' : forall q', In q' l -> rsat D1 k (sR S' q')).
      { intros q' H. cbn [sR S' srupd]. destruct (Atom.eq_dec q' (ea n)) as [E2|Hne].
        - exfalso. exact (Hnew q' (or_intror H) n (le_n n) E2).
        - exact (Hs q' (or_intror H)). }
      assert (Hnew' : forall q', In q' l -> forall m, Datatypes.S n <= m -> q' <> ea m).
      { intros q' H m Hm. apply (Hnew q' (or_intror H)). lia. }
      destruct (IH (rupd D (ea n) (RK k (rk_lacks (drk D q)))) (Datatypes.S n) k S' D1
                  (DOk_rupd D n _ Hd) HK' Hs' Hnew' s D'' n'' E1) as (S2 & H1 & H2 & H3 & H5).
      exists S2. split; [ exact H1 | split; [ rewrite H2; reflexivity | ] ].
      assert (HRI : RImg Sg S').
      { intros r. cbn [sR S' srupd]. destruct (Atom.eq_dec r (ea n)) as [_|_]; [ exists q | exists r ]; reflexivity. }
      split; [ | exact (RImg_trans _ _ _ HRI H5) ].
      intros r Hr.
      assert (Hn : forall m, Datatypes.S n <= m -> ea n <> ea m)
        by (intros m Hm Heq; apply ea_inj in Heq; lia).
      change (sR (scomp s (sbR q (row_Var (ea n)))) r)
        with (apR s (sR (sbR q (row_Var (ea n))) r)).
      cbn [sR sbR]. destruct (Atom.eq_dec r q) as [->|Hne]; cbn iota.
      * pose proof (H3 (ea n) Hn) as H4. cbn [sR S' srupd] in H4.
        rewrite dec_same in H4. exact H4.
      * assert (Hxn : r <> ea n) by (intros Heq; exact (Hr n (le_n n) Heq)).
        pose proof (H3 r (fun m Hm => Hr m ltac:(lia))) as H4. cbn [sR S' srupd] in H4.
        rewrite (dec_diff _ _ _ _ _ Hxn) in H4. exact H4.
Qed.

(* ---- the fresh variables of [rewrite_row] ---- *)

Lemma is_abs_Bool : forall P, is_abs P = true -> P = typ_Bool.
Proof. intros P H. destruct P; cbn in H; try discriminate. reflexivity. Qed.

(* A row of the kind [K] that is an entry followed by [R] has [R] of the kind. *)
Lemma rkok_maybe_tail : forall D K l P T R, rkok D K (row_Maybe l P T R) -> rkok D K R.
Proof.
  intros D K l P T R [Hs Hl]. split; [ exact (proj2 Hs) | ].
  intros l' Hl'. specialize (Hl l' Hl'). cbn [rlacksD] in Hl.
  destruct (Nat.eqb l' l); [ exact (proj2 (andb_prop _ _ Hl)) | exact Hl ].
Qed.

(* A label the kind lacks has an absent entry. *)
Lemma rkok_maybe_abs : forall D K l P T R,
  rkok D K (row_Maybe l P T R) -> rk_lacks K l = true -> P = typ_Bool.
Proof.
  intros D K l P T R [_ Hl] Hk. specialize (Hl l Hk). cbn [rlacksD] in Hl.
  rewrite Nat.eqb_refl in Hl. exact (is_abs_Bool _ (proj1 (andb_prop _ _ Hl))).
Qed.

Lemma rkok_req : forall D K R R', req R R' -> rkok D K R -> rkok D K R'.
Proof.
  intros D K R R' H [Hs Hl]. split; [ exact (rsat_req D _ _ _ H Hs) | ].
  intros l Hk. rewrite <- (req_rlacksD _ _ H). exact (Hl l Hk).
Qed.

(* [rewrite_row] at a row variable binds it to an entry of the label, a fresh
   field type and a fresh tail (and, unless the variable lacks the label, a
   fresh presence).  A substitution [Sg] that sends the variable to a row that
   presents the label as [l ^ P0 : T0 ; R0] extends to those variables by the
   three parts, and the extension respects the environment [rewrite_row]
   returns.  The one fact the sort of the variable does not give is the sort of
   [T0] when the entry is absent: the fresh field variable carries the sort of
   the row variable, an absent field is unconstrained by [rsat], so the
   hypothesis [Hfield] is needed there, and it is a real condition on [Sg]. *)
Lemma rewrite_row_var_complete : forall l av D n r D1 Sg P0 T0 R0,
  DOk D n -> KR D D1 Sg -> AtomSetImpl.mem r av = false ->
  req (sR Sg r) (row_Maybe l P0 T0 R0) ->
  (rk_lacks (drk D r) l = false -> P0 = typ_Bool -> sat D1 (rk_sort (drk D r)) T0) ->
  exists P' T' R' s0 D0 n1 S2,
    rewrite_row l av D (row_Var r) n = Some (P', T', R', s0, D0, n1) /\
    KR D0 D1 S2 /\ n <= n1 /\
    apT S2 P' = P0 /\ apT S2 T' = T0 /\ apR S2 R' = R0 /\
    (forall x, (forall m, n <= m -> x <> ea m) -> sT Sg x = apT S2 (sT s0 x)) /\
    (forall q, (forall m, n <= m -> q <> ea m) -> req (sR Sg q) (apR S2 (sR s0 q))) /\
    (forall E F, Bnd E F Sg -> AIn E F P0 T0 R0 -> Bnd E F S2).
Proof.
  intros l av D n r D1 Sg P0 T0 R0 Hd HK Hav Hreq Hfield.
  assert (Hrk : rkok D1 (drk D r) (row_Maybe l P0 T0 R0)).
  { exact (rkok_req D1 _ _ _ Hreq (proj2 HK r)). }
  assert (HR0 : rkok D1 (drk D r) R0) by exact (rkok_maybe_tail _ _ _ _ _ _ Hrk).
  assert (Hfresh : forall j, n <= j -> forall x, (forall m, n <= m -> x <> ea m) -> x <> ea j)
    by (intros j Hj x Hx E; exact (Hx j Hj E)).
  assert (Hne1 : ea n <> ea (Datatypes.S n)) by (intros E; apply ea_inj in E; lia).
  assert (Hne2 : ea n <> ea (n + 2)) by (intros E; apply ea_inj in E; lia).
  assert (Hne3 : ea (Datatypes.S n) <> ea (n + 2)) by (intros E; apply ea_inj in E; lia).
  cbn [rewrite_row]. rewrite Hav. cbn zeta.
  destruct (rk_lacks (drk D r) l) eqn:Hl.
  - pose proof (rkok_maybe_abs _ _ _ _ _ _ Hrk Hl) as HP0. subst P0.
    set (S2 := srupd (supd Sg (ea n) T0) (ea (Datatypes.S n)) R0).
    exists typ_Bool, (typ_Var (ea n)), (row_Var (ea (Datatypes.S n))),
      (sbR r (row_Maybe l typ_Bool (typ_Var (ea n)) (row_Var (ea (Datatypes.S n))))),
      (rupd D (ea (Datatypes.S n)) (drk D r)), (n + 2), S2.
    refine (conj eq_refl (conj _ (conj _ (conj eq_refl (conj _ (conj _ (conj _ (conj _ _)))))))).
    + split.
      * intros a. cbn [sT S2 srupd supd dsort rupd]. destruct (Atom.eq_dec a (ea n)) as [->|Hne].
        -- rewrite (DOk_ea D n n Hd (le_n n)). apply sat_any.
        -- exact (proj1 HK a).
      * intros q. cbn [sR S2 srupd supd drk rupd]. destruct (Atom.eq_dec q (ea (Datatypes.S n))) as [->|Hne].
        -- exact HR0.
        -- exact (proj2 HK q).
    + lia.
    + cbn [apT S2 sT supd ap_typ srupd]. rewrite dec_same. reflexivity.
    + cbn [apR S2 sR srupd ap_row]. rewrite dec_same. reflexivity.
    + intros x Hx. cbn [sT sbR]. unfold idt. cbn [apT S2 sT supd ap_typ srupd].
      rewrite (dec_diff _ _ _ _ _ (Hfresh n (le_n n) x Hx)). reflexivity.
    + intros q Hq. cbn [sR sbR]. destruct (Atom.eq_dec q r) as [->|Hne].
      * cbn [apR S2 sR srupd supd ap_row ap_typ sT]. rewrite dec_same.
        rewrite dec_same. exact Hreq.
      * cbn [apR S2 sR srupd ap_row]. rewrite (dec_diff _ _ _ _ _ (Hfresh (Datatypes.S n) ltac:(lia) q Hq)).
        apply req_refl.
    + intros E F HB (_ & AT & AR & _ & FT & FR).
      exact (Bnd_srupd E F _ _ _ (Bnd_supd E F _ _ _ HB AT FT) AR FR).
  - set (S2 := srupd (supd (supd Sg (ea n) P0) (ea (Datatypes.S n)) T0) (ea (n + 2)) R0).
    assert (HT0 : sat D1 (rk_sort (drk D r)) T0).
    { destruct Hrk as [[[H|H] _] _]; [ subst; exact (Hfield eq_refl eq_refl) | exact H ]. }
    exists (typ_Var (ea n)), (typ_Var (ea (Datatypes.S n))), (row_Var (ea (n + 2))),
      (sbR r (row_Maybe l (typ_Var (ea n)) (typ_Var (ea (Datatypes.S n))) (row_Var (ea (n + 2))))),
      (rupd (upd D (ea (Datatypes.S n)) (rk_sort (drk D r))) (ea (n + 2)) (drk D r)), (n + 3), S2.
    refine (conj eq_refl (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
    + split.
      * intros a. cbn [sT S2 srupd supd dsort rupd upd].
        destruct (Atom.eq_dec a (ea (Datatypes.S n))) as [->|Hne2'].
        -- exact HT0.
        -- destruct (Atom.eq_dec a (ea n)) as [->|Hne].
           ++ rewrite (DOk_ea D n n Hd (le_n n)). apply sat_any.
           ++ exact (proj1 HK a).
      * intros q. cbn [sR S2 srupd supd drk rupd upd].
        destruct (Atom.eq_dec q (ea (n + 2))) as [->|Hne].
        -- exact HR0.
        -- exact (proj2 HK q).
    + lia.
    + cbn [apT S2 sT supd srupd ap_typ].
      rewrite (dec_diff _ _ _ _ _ Hne1), dec_same. reflexivity.
    + cbn [apT S2 sT supd srupd ap_typ]. rewrite dec_same. reflexivity.
    + cbn [apR S2 sR srupd ap_row]. rewrite dec_same. reflexivity.
    + intros x Hx. cbn [sT sbR]. unfold idt. cbn [apT S2 sT supd ap_typ srupd].
      rewrite (dec_diff _ _ _ _ _ (Hfresh (Datatypes.S n) ltac:(lia) x Hx)),
              (dec_diff _ _ _ _ _ (Hfresh n (le_n n) x Hx)). reflexivity.
    + intros q Hq. cbn [sR sbR]. destruct (Atom.eq_dec q r) as [->|Hne].
      * cbn [apR S2 sR srupd supd ap_row ap_typ sT].
        repeat (first [ rewrite dec_same | rewrite (dec_diff _ _ _ _ _ Hne1)
                      | rewrite (dec_diff _ _ _ _ _ Hne2) | rewrite (dec_diff _ _ _ _ _ Hne3) ]).
        exact Hreq.
      * cbn [apR S2 sR srupd ap_row]. rewrite (dec_diff _ _ _ _ _ (Hfresh (n + 2) ltac:(lia) q Hq)).
        apply req_refl.
    + intros E F HB (AP & AT & AR & FP & FT & FR).
      exact (Bnd_srupd E F _ _ _ (Bnd_supd E F _ _ _ (Bnd_supd E F _ _ _ HB AP FP) AT FT) AR FR).
Qed.

(* The fresh variables take canonical representatives, so the extension
   mentions only atoms [Sg] does: the field the row's image presents is known
   only up to [teq], and an arbitrary representative of its class can carry
   atoms the image does not.  The presence is present, which rules out the
   variable lacking the label. *)
Lemma rewrite_row_var_canon : forall l av D n r D1 Sg P0 T0 R0,
  DOk D n -> KR D D1 Sg -> AtomSetImpl.mem r av = false ->
  req (sR Sg r) (row_Maybe l P0 T0 R0) -> is_abs P0 = false ->
  exists P' T' R' s0 D0 n1 S2,
    rewrite_row l av D (row_Var r) n = Some (P', T', R', s0, D0, n1) /\
    KR D0 D1 S2 /\ n <= n1 /\
    req (row_Maybe l (apT S2 P') (apT S2 T') (apR S2 R')) (row_Maybe l P0 T0 R0) /\
    (forall x, (forall m, n <= m -> x <> ea m) -> sT Sg x = apT S2 (sT s0 x)) /\
    (forall q, (forall m, n <= m -> q <> ea m) -> req (sR Sg q) (apR S2 (sR s0 q))) /\
    Cov Sg S2.
Proof.
  intros l av D n r D1 Sg P0 T0 R0 Hd HK Hav Hreq Hna.
  pose proof (proj1 er_teq P0) as HP. pose proof (proj1 er_teq T0) as HT. pose proof (proj2 er_teq R0) as HR.
  assert (Hq : req (row_Maybe l (erT P0) (erT T0) (erR R0)) (row_Maybe l P0 T0 R0))
    by (apply req_maybe; assumption).
  assert (Hna' : is_abs (erT P0) = false) by exact (er_not_abs P0 Hna).
  destruct (rewrite_row_var_complete l av D n r D1 Sg (erT P0) (erT T0) (erR R0) Hd HK Hav
              (req_trans _ _ _ Hreq (req_sym _ _ Hq))
              (fun _ H => ltac:(exfalso; rewrite H in Hna'; discriminate Hna')))
    as (P' & T' & R' & s0 & D0 & n1 & S2 & E & K & Hn & HP' & HT' & HR' & F1 & F2 & Hb).
  exists P', T', R', s0, D0, n1, S2.
  refine (conj E (conj K (conj Hn (conj _ (conj F1 (conj F2 _)))))).
  - rewrite HP', HT', HR'. exact Hq.
  - intros E0 F0 HB. refine (Hb E0 F0 HB _). destruct HB as (B1 & B2 & B3 & B4).
    pose proof (proj2 er_inv _ _ Hreq) as [Hf Hr]. cbn [erR] in Hf, Hr.
    rewrite Hna in Hf, Hr. cbn [ftv_row frv_row] in Hf, Hr.
    pose proof (proj2 er_sub (sR Sg r)) as [Hs1 Hs2].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + intros x Hx. apply (B3 r x). apply Hs1. apply (proj2 (Hf x)). fsetdec.
    + intros x Hx. apply (B3 r x). apply Hs1. apply (proj2 (Hf x)). fsetdec.
    + intros x Hx. apply (B3 r x). apply Hs1. apply (proj2 (Hf x)). fsetdec.
    + intros x Hx. apply (B4 r x). apply Hs2. apply (proj2 (Hr x)). fsetdec.
    + intros x Hx. apply (B4 r x). apply Hs2. apply (proj2 (Hr x)). fsetdec.
    + intros x Hx. apply (B4 r x). apply Hs2. apply (proj2 (Hr x)). fsetdec.
Qed.

(* ---- the fresh variable of [bind_row] ---- *)

Lemma rk_join_ok : forall D K1 K2 R, rkok D K1 R -> rkok D K2 R -> rkok D (rk_join K1 K2) R.
Proof.
  intros D K1 K2 R [Hs1 Hl1] [Hs2 Hl2]. unfold rk_join. split.
  - cbn [rk_sort]. destruct (finer_b (rk_sort K1) (rk_sort K2)); assumption.
  - intros l Hl. cbn [rk_lacks] in Hl. apply Bool.orb_true_iff in Hl.
    destruct Hl as [H|H]; [ exact (Hl1 l H) | exact (Hl2 l H) ].
Qed.

(* [bind_row] renames the variable [q] at the tail of the row to a fresh row
   variable of the kind both [r] and [q] have (the lacks sets are functions, so
   the two cannot be compared).  A substitution that respects [q]'s kind and
   also gives [S q] [r]'s kind extends to it by the image of [q]; the second
   hypothesis is what the row that [r] equals has to supply of its tail. *)
Lemma bind_row_tail_complete : forall D n r q D1 Sg,
  DOk D n -> KR D D1 Sg -> rkok D1 (drk D r) (sR Sg q) ->
  exists S2, KR (rupd D (ea n) (rk_join (drk D r) (drk D q))) D1 S2 /\
    (forall x, sT Sg x = apT S2 (sT (sbR q (row_Var (ea n))) x)) /\
    (forall q', (forall m, n <= m -> q' <> ea m) ->
       sR Sg q' = apR S2 (sR (sbR q (row_Var (ea n))) q')).
Proof.
  intros D n r q D1 Sg Hd HK Hr. exists (srupd Sg (ea n) (sR Sg q)). split; [ | split ].
  - split.
    + intros a. cbn [sT srupd dsort rupd]. exact (proj1 HK a).
    + intros r'. cbn [sR srupd drk rupd]. destruct (Atom.eq_dec r' (ea n)) as [->|Hne].
      * exact (rk_join_ok _ _ _ _ Hr (proj2 HK q)).
      * exact (proj2 HK r').
  - intros x. reflexivity.
  - intros q' Hq. cbn [sR sbR]. destruct (Atom.eq_dec q' q) as [->|Hne]; cbn iota.
    + cbn [apR sR srupd ap_row]. rewrite dec_same. reflexivity.
    + cbn [apR sR srupd ap_row]. rewrite (dec_diff _ _ _ _ _ (fun E => Hq n (le_n n) E)). reflexivity.
Qed.
