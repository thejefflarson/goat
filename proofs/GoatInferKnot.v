(* The knot-tying unifier (phase 5, stage 4, part 3;
   docs/design/w-recursive-types-plan.md, Option B).

   [unify_k] is [unify_t] with three changes, and [unify_kr] is [unify_r]
   calling it.
   - A variable that occurs in the type it meets is bound to a recursive
     type, not refused: [x := knot x T] when every mention of [x] is guarded
     ([bind_k]).
   - A recursive type that meets a different head is unrolled once, spending
     fuel; two recursive types are compared by their bodies and, failing
     that, by unrolling.  Fuel is the checker's cap on knots.
   - A bound index meets only itself.  A variable never binds to a type with a
     free index, so a substitution's images stay closed ([OkS]).

   Its specification is [unroll_eq], not [teq]: a successful unifier [s]
   gives [s T1 ~~[m] s T2] for some budget [m] ([unify_k_sound]).  The
   elaboration pass of the later parts reads the coercions off that
   difference.  [unify_t] is untouched, so the soundness of W as it stands
   ([infer_closed_sound]) does not move. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatElab.
Require Import Goat.GoatUnrollEqb.
Require Import Goat.GoatKnot.
Require Import Goat.GoatGuard.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

(* ------------------------------------------------------------------ *)
(* The algorithm                                                        *)
(* ------------------------------------------------------------------ *)

(* Bind [a] to [T].  A type with a free index, or with a recursive type inside
   whose body is not guarded, is refused (the second never happens to a type
   the algorithm built; the check makes every image of a substitution this
   unifier returns guarded without a hypothesis on its inputs, [unify_k_guard]).
   If [a] occurs in [T] the binding is a knot, which needs every mention of [a]
   guarded and the knot to have the sort of [a]. *)
Definition bind_k (D : denv) (a : atom) (T : typ) (n : nat) : option (sub * denv * nat) :=
  if negb (lcb 0 T) then None
  else if negb (mgb T) then None
  else if AtomSetImpl.mem a (ftv_typ T) then
    if gdb false false a T && sat_b D (D a) (knot a T)
    then Some (sbT a (knot a T), D, n) else None
  else bind_prop D a T n.

Fixpoint unify_k (f : nat) (D : denv) (T1 T2 : typ) (n : nat) {struct f}
  : option (sub * denv * nat) :=
  match f with
  | O => None
  | S f' =>
      match T1, T2 with
      | typ_Int, typ_Int => Some (sid, D, n)
      | typ_Float, typ_Float => Some (sid, D, n)
      | typ_Bool, typ_Bool => Some (sid, D, n)
      | typ_Unit, typ_Unit => Some (sid, D, n)
      | typ_String, typ_String => Some (sid, D, n)
      | typ_Bvar i, typ_Bvar j => if Nat.eqb i j then Some (sid, D, n) else None
      | typ_Var a, typ_Var b =>
          if Atom.eq_dec a b then Some (sid, D, n)
          else if finer_b (D b) (D a) then Some (sbT a T2, D, n)
          else if finer_b (D a) (D b) then Some (sbT b T1, D, n)
          else Some (meet_float a b, D, n)
      | typ_Var a, _ => bind_k D a T2 n
      | _, typ_Var b => bind_k D b T1 n
      | typ_Mu B1, typ_Mu B2 =>
          match
            match unify_k f' D B1 B2 n with
            | Some (s, D1, n1) => if typ_eqb (apT s B1) (apT s B2) then Some (s, D1, n1) else None
            | None => None
            end
          with
          | Some r => Some r
          | None => unify_k f' D (open_typ 0 T1 B1) T2 n
          end
      | typ_Mu B1, _ => unify_k f' D (open_typ 0 T1 B1) T2 n
      | _, typ_Mu B2 => unify_k f' D T1 (open_typ 0 T2 B2) n
      | typ_Arrow A B, typ_Arrow A' B' =>
          match unify_k f' D A A' n with
          | None => None
          | Some (s1, D1, n1) =>
              match unify_k f' D1 (apT s1 B) (apT s1 B') n1 with
              | None => None
              | Some (s2, D2, n2) => Some (scomp s2 s1, D2, n2)
              end
          end
      | typ_Record R, typ_Record R' => unify_kr f' D R R' n
      | typ_Grp w A, typ_Grp w' A' =>
          if gdecl_eq_dec w w' then unify_k f' D A A' n else None
      | _, _ => None
      end
  end
with unify_kr (f : nat) (D : denv) (R1 R2 : row) (n : nat) {struct f}
  : option (sub * denv * nat) :=
  match f with
  | O => None
  | S f' =>
      match R1, R2 with
      | row_Var r, row_Var s =>
          if Atom.eq_dec r s then Some (sid, D, n) else bind_row D r R2 n
      | row_Var r, _ => if mgbr R2 then bind_row D r R2 n else None
      | _, row_Var s => if mgbr R1 then bind_row D s R1 n else None
      | row_Empty, row_Empty => Some (sid, D, n)
      | row_Empty, row_Maybe _ _ _ _ => unify_kr f' D R2 R1 n
      | _, _ =>
          match row_head R1 with
          | None => None
          | Some (l, P, T, R1') =>
              match rewrite_row l (side_av R1) D R2 n with
              | None => None
              | Some (P', T', R2', s0, D0, n1) =>
                  match unify_k f' D0 (apT s0 P) P' n1 with
                  | None => None
                  | Some (sp, D1, n2) =>
                      match unify_k f' D1 (apT sp (apT s0 T)) (apT sp T') n2 with
                      | None => None
                      | Some (s1, D2, n3) =>
                          match unify_kr f' D2 (apR s1 (apR sp (apR s0 R1'))) (apR s1 (apR sp R2')) n3 with
                          | None => None
                          | Some (s2, D3, n4) => Some (scomp s2 (scomp s1 (scomp sp s0)), D3, n4)
                          end
                      end
                  end
              end
          end
      end
  end.

(* ------------------------------------------------------------------ *)
(* Facts about substitution, unrolling and the invariants               *)
(* ------------------------------------------------------------------ *)

Lemma OkS_lc : forall s, OkS s -> lc_sub (sT s) (sR s).
Proof. intros s [[A [_ [_ H]]] _]. exact H. Qed.

Lemma unroll_apT : forall s n T T', OkS s -> unroll_eq n T T' ->
  unroll_eq n (apT s T) (apT s T').
Proof. intros s n T T' Hok H. exact (unroll_ap (sT s) (sR s) n T T' (OkS_lc s Hok) H). Qed.

Lemma unroll_apR : forall s n R R', OkS s -> unroll_row n R R' ->
  unroll_row n (apR s R) (apR s R').
Proof.
  intros s n R R' Hok H. exact (proj2 (unroll_ap_mut (sT s) (sR s) (OkS_lc s Hok)) n R R' H).
Qed.

Lemma unroll_row_mono : forall m n R R', m <= n -> unroll_row m R R' -> unroll_row n R R'.
Proof.
  intros m n R R' Hle H. induction Hle; [ exact H | apply (proj2 unroll_mono_mut); exact IHHle ].
Qed.

Lemma unroll_row_sym : forall n R R', unroll_row n R R' -> unroll_row n R' R.
Proof. intros n R R' H. exact (proj2 unroll_sym_mut n R R' H). Qed.

Lemma unroll_row_trans_l : forall n R1 R2 R3,
  unroll_row 0 R1 R2 -> unroll_row n R2 R3 -> unroll_row n R1 R3.
Proof. intros n R1 R2 R3 H1 H2. exact (UR_trans 0 n _ _ _ H1 H2). Qed.

Lemma unroll_row_trans_r : forall n R1 R2 R3,
  unroll_row n R1 R2 -> unroll_row 0 R2 R3 -> unroll_row n R1 R3.
Proof.
  intros n R1 R2 R3 H1 H2. rewrite <- (Nat.add_0_r n). exact (UR_trans n 0 _ _ _ H1 H2).
Qed.

Lemma ftv_open_mut :
  (forall T k U, ftv_typ (open_typ k U T) [<=] ftv_typ T `union` ftv_typ U) /\
  (forall R k U, ftv_row (open_row k U R) [<=] ftv_row R `union` ftv_typ U).
Proof.
  apply typ_row_mutind; simpl; intros; try fsetdec;
    try (pose proof (H k U); try pose proof (H0 k U); try pose proof (H1 k U); fsetdec).
  - destruct (lt_eq_lt_dec i k) as [[?|?]|?]; simpl; fsetdec.
  - pose proof (H (S k) U). fsetdec.
Qed.

Lemma frv_open_mut :
  (forall T k U, frv_typ (open_typ k U T) [<=] frv_typ T `union` frv_typ U) /\
  (forall R k U, frv_row (open_row k U R) [<=] frv_row R `union` frv_typ U).
Proof.
  apply typ_row_mutind; simpl; intros; try fsetdec;
    try (pose proof (H k U); try pose proof (H0 k U); try pose proof (H1 k U); fsetdec).
  - destruct (lt_eq_lt_dec i k) as [[?|?]|?]; simpl; fsetdec.
  - pose proof (H (S k) U). fsetdec.
Qed.

Lemma EvT_open : forall T k U, EvT T -> EvT U -> EvT (open_typ k U T).
Proof.
  intros T k U [H1 H2] [H3 H4]. split; intros a Ha.
  - apply (proj1 ftv_open_mut T k U) in Ha. apply AtomSetFacts.union_iff in Ha as [Ha|Ha]; auto.
  - apply (proj1 frv_open_mut T k U) in Ha. apply AtomSetFacts.union_iff in Ha as [Ha|Ha]; auto.
Qed.

Lemma EvT_knot : forall a T, EvT T -> EvT (knot a T).
Proof.
  intros a T [H1 H2]. split.
  - intros b Hb. exact (H1 b (knot_ftv a T b Hb)).
  - rewrite knot_frv. exact H2.
Qed.

Lemma lift_teq : forall (s : sub) D n D' n' T T',
  OkS s /\ teq T T' /\ GoodU D n s D' n' ->
  OkS s /\ (exists m, unroll_eq m T T') /\ GoodU D n s D' n'.
Proof.
  intros s D n D' n' T T' (Hs & Ht & Hg).
  refine (conj Hs (conj _ Hg)). exists 0. apply UE_teq. exact Ht.
Qed.

Lemma lift_req : forall (s : sub) D n D' n' R R',
  OkS s /\ req R R' /\ GoodU D n s D' n' ->
  OkS s /\ (exists m, unroll_row m R R') /\ GoodU D n s D' n'.
Proof.
  intros s D n D' n' R R' (Hs & Ht & Hg).
  refine (conj Hs (conj _ Hg)). exists 0. apply UR_req. exact Ht.
Qed.

Lemma var_left_Rk : forall D a R n s D' n',
  (if mgbr R then bind_row D a R n else None) = Some (s, D', n') ->
  EvR (row_Var a) -> EvR R ->
  OkS s /\ req (apR s (row_Var a)) (apR s R) /\ GoodU D n s D' n'.
Proof.
  intros D a R n s D' n' H Ha HR.
  destruct (mgbr R) eqn:Em; [|discriminate].
  exact (bind_row_sound _ _ _ _ _ _ _ H Ha HR).
Qed.

Lemma var_right_Rk : forall D b R n s D' n',
  (if mgbr R then bind_row D b R n else None) = Some (s, D', n') ->
  EvR R -> EvR (row_Var b) ->
  OkS s /\ req (apR s R) (apR s (row_Var b)) /\ GoodU D n s D' n'.
Proof.
  intros D b R n s D' n' H HR Hb.
  destruct (mgbr R) eqn:Em; [|discriminate].
  destruct (bind_row_sound _ _ _ _ _ _ _ H Hb HR) as (Hs & Hr & Hg).
  exact (conj Hs (conj (req_sym _ _ Hr) Hg)).
Qed.

(* ------------------------------------------------------------------ *)
(* The specification                                                    *)
(* ------------------------------------------------------------------ *)

Definition Spec (D : denv) (n : nat) (T1 T2 : typ) (r : option (sub * denv * nat)) : Prop :=
  forall s D' n', r = Some (s, D', n') -> EvT T1 -> EvT T2 ->
    OkS s /\ (exists m, unroll_eq m (apT s T1) (apT s T2)) /\ GoodU D n s D' n'.

Definition SpecR (D : denv) (n : nat) (R1 R2 : row) (r : option (sub * denv * nat)) : Prop :=
  forall s D' n', r = Some (s, D', n') -> EvR R1 -> EvR R2 ->
    OkS s /\ (exists m, unroll_row m (apR s R1) (apR s R2)) /\ GoodU D n s D' n'.

Lemma spec_none : forall D n T1 T2, Spec D n T1 T2 None.
Proof. intros D n T1 T2 s D' n' H. discriminate. Qed.

Lemma spec_base : forall D n T, Spec D n T T (Some (sid, D, n)).
Proof.
  intros D n T s D' n' H _ _. inversion H; subst; clear H.
  apply lift_teq. split; [ apply OkS_id | split; [ apply teq_refl | exact (GoodU_id _ _) ] ].
Qed.

Lemma bind_k_sound : forall D a T n,
  Spec D n (typ_Var a) T (bind_k D a T n).
Proof.
  intros D a T n s D' n' H Ha HT. unfold bind_k in H.
  destruct (lcb 0 T) eqn:Elc; cbn [negb] in H; [ | discriminate ].
  destruct (mgb T) eqn:Emg; cbn [negb] in H; [ | discriminate ].
  destruct (AtomSetImpl.mem a (ftv_typ T)) eqn:Emem.
  - destruct (gdb false false a T && sat_b D (D a) (knot a T)) eqn:Eg; [ | discriminate ].
    inversion H; subst; clear H.
    apply Bool.andb_true_iff in Eg as [Hg Hs].
    assert (Hlc : lct 0 T) by (apply lcb_lct; exact Elc).
    split; [ exact (OkS_sbT a (knot a T) (ev_var_T a Ha) (EvT_knot a T HT) (knot_lc a T Hlc)) | ].
    split.
    + exists 1.
      assert (E1 : apT (sbT a (knot a T)) (typ_Var a) = knot a T).
      { unfold apT, sbT; simpl. destruct (Atom.eq_dec a a); [ reflexivity | contradiction ]. }
      assert (E2 : apT (sbT a (knot a T)) T = ap_typ (sub1 a (knot a T)) idr T) by reflexivity.
      rewrite E1, E2. exact (knot_unroll_eq a T Hlc).
    + apply GoodU_same; [ exact (OkS_sbT a (knot a T) (ev_var_T a Ha) (EvT_knot a T HT) (knot_lc a T Hlc)) | | lia ].
      apply KR_sbT; apply sat_b_sound; exact Hs.
  - destruct (bind_prop_sound _ _ _ _ _ _ _ H Ha HT) as (Hs & Ht & Hg).
    refine (conj Hs (conj _ Hg)). exists 0. apply UE_teq. exact Ht.
Qed.

Lemma bind_k_sound_right : forall D b T n,
  Spec D n T (typ_Var b) (bind_k D b T n).
Proof.
  intros D b T n s D' n' H HT Hb.
  destruct (bind_k_sound D b T n s D' n' H Hb HT) as (Hs & [m Hm] & Hg).
  refine (conj Hs (conj _ Hg)). exists m. apply unroll_sym. exact Hm.
Qed.

Lemma spec_var_var : forall D n a b,
  Spec D n (typ_Var a) (typ_Var b)
    (if Atom.eq_dec a b then Some (sid, D, n)
     else if finer_b (D b) (D a) then Some (sbT a (typ_Var b), D, n)
     else if finer_b (D a) (D b) then Some (sbT b (typ_Var a), D, n)
     else Some (meet_float a b, D, n)).
Proof.
  intros D n a b s D' n' H H1 H2.
  destruct (Atom.eq_dec a b) as [->|Hne].
  - inversion H; subst. apply lift_teq.
    split; [apply OkS_id | split; [apply teq_refl | exact (GoodU_id _ _) ]].
  - assert (Eoa : occT a (typ_Var b) = false).
    { unfold occT. simpl. apply Bool.orb_false_iff. split; [ | reflexivity ].
      apply AtomSetFacts.not_mem_iff. intro Hin.
      apply AtomSetFacts.singleton_iff in Hin. congruence. }
    assert (Eob : occT b (typ_Var a) = false).
    { unfold occT. simpl. apply Bool.orb_false_iff. split; [ | reflexivity ].
      apply AtomSetFacts.not_mem_iff. intro Hin.
      apply AtomSetFacts.singleton_iff in Hin. congruence. }
    apply lift_teq.
    destruct (finer_b (D b) (D a)) eqn:Ef.
    + inversion H; subst; clear H.
      destruct (sound_bindT a (typ_Var b) (ev_var_T a H1) H2 Eoa) as [Hs Ht].
      split; [exact Hs|]. split; [exact Ht|].
      apply GoodU_same; [ exact Hs | apply KR_sbT; simpl; apply finer_b_sound; exact Ef | lia ].
    + destruct (finer_b (D a) (D b)) eqn:Ef2.
      * inversion H; subst; clear H.
        destruct (sound_bindT b (typ_Var a) (ev_var_T b H2) H1 Eob) as [Hs Ht].
        split; [exact Hs|]. split; [apply teq_sym; exact Ht|].
        apply GoodU_same; [ exact Hs | apply KR_sbT; simpl; apply finer_b_sound; exact Ef2 | lia ].
      * inversion H; subst; clear H.
        destruct (sound_meet D' a b H1 H2 Hne) as [Hs [Ht Hk]].
        split; [exact Hs|]. split; [exact Ht|].
        apply GoodU_same; [ exact Hs | exact Hk | lia ].
Qed.

(* A mu that meets another head is unrolled: the result for the unrolling is
   a result for the mu, one unrolling more. *)
Lemma spec_unfold_left : forall D n B T2 r,
  Spec D n (open_typ 0 (typ_Mu B) B) T2 r -> Spec D n (typ_Mu B) T2 r.
Proof.
  intros D n B T2 r Hs s D' n' E H1 H2.
  assert (H1' : EvT (open_typ 0 (typ_Mu B) B)) by (apply EvT_open; exact H1).
  destruct (Hs s D' n' E H1' H2) as (Hok & [m Hm] & Hg).
  refine (conj Hok (conj _ Hg)). exists (1 + m).
  assert (Eap : apT s (open_typ 0 (typ_Mu B) B) = open_typ 0 (typ_Mu (apT s B)) (apT s B)).
  { unfold apT. rewrite (ap_open (sT s) (sR s) B 0 (typ_Mu B) (OkS_lc s Hok)). reflexivity. }
  rewrite Eap in Hm.
  apply (UE_trans 1 m _ (open_typ 0 (typ_Mu (apT s B)) (apT s B))); [ | exact Hm ].
  change (apT s (typ_Mu B)) with (typ_Mu (apT s B)). apply (UE_unfold 0).
Qed.

Lemma spec_unfold_right : forall D n B T1 r,
  Spec D n T1 (open_typ 0 (typ_Mu B) B) r -> Spec D n T1 (typ_Mu B) r.
Proof.
  intros D n B T1 r Hs s D' n' E H1 H2.
  assert (H2' : EvT (open_typ 0 (typ_Mu B) B)) by (apply EvT_open; exact H2).
  destruct (Hs s D' n' E H1 H2') as (Hok & [m Hm] & Hg).
  refine (conj Hok (conj _ Hg)). exists (m + 1).
  assert (Eap : apT s (open_typ 0 (typ_Mu B) B) = open_typ 0 (typ_Mu (apT s B)) (apT s B)).
  { unfold apT. rewrite (ap_open (sT s) (sR s) B 0 (typ_Mu B) (OkS_lc s Hok)). reflexivity. }
  rewrite Eap in Hm.
  apply (UE_trans m 1 _ (open_typ 0 (typ_Mu (apT s B)) (apT s B))); [ exact Hm | ].
  change (apT s (typ_Mu B)) with (typ_Mu (apT s B)). apply (UE_fold 0).
Qed.

(* One field of a row at a time: the substitutions the steps build, and the
   budgets of the three pieces, give a budget for the whole row. *)
Lemma row_step_unroll : forall s0 sp s1 s2 R1 R2 l P T R1' P' T' R2' mp mt mr,
  OkS s2 -> OkS s1 ->
  req R1 (row_Maybe l P T R1') ->
  req (apR s0 R2) (row_Maybe l P' T' R2') ->
  unroll_eq mp (apT sp (apT s0 P)) (apT sp P') ->
  unroll_eq mt (apT s1 (apT sp (apT s0 T))) (apT s1 (apT sp T')) ->
  unroll_row mr (apR s2 (apR s1 (apR sp (apR s0 R1')))) (apR s2 (apR s1 (apR sp R2'))) ->
  exists m, unroll_row m (apR (scomp s2 (scomp s1 (scomp sp s0))) R1)
                         (apR (scomp s2 (scomp s1 (scomp sp s0))) R2).
Proof.
  intros s0 sp s1 s2 R1 R2 l P T R1' P' T' R2' mp mt mr Hs2 Hs1 H1 H2 Hp Ht Hr.
  exists (mp + mt + mr).
  rewrite <- !apR_comp.
  eapply unroll_row_trans_l.
  { apply UR_req.
    exact (req_apR s2 _ _ (req_apR s1 _ _ (req_apR sp _ _ (req_apR s0 _ _ H1)))). }
  eapply unroll_row_trans_r;
    [ | apply UR_req; apply req_sym;
        exact (req_apR s2 _ _ (req_apR s1 _ _ (req_apR sp _ _ H2))) ].
  rewrite !apR_Maybe.
  apply UR_maybe.
  - apply (unroll_mono mp); [ lia | ].
    exact (unroll_apT s2 _ _ _ Hs2 (unroll_apT s1 _ _ _ Hs1 Hp)).
  - apply (unroll_mono mt); [ lia | ].
    exact (unroll_apT s2 _ _ _ Hs2 Ht).
  - apply (unroll_row_mono mr); [ lia | exact Hr ].
Qed.

(* ------------------------------------------------------------------ *)
(* Soundness of the unifier                                             *)
(* ------------------------------------------------------------------ *)

Theorem unify_k_sound : forall f,
  (forall D T1 T2 n, Spec D n T1 T2 (unify_k f D T1 T2 n)) /\
  (forall D R1 R2 n, SpecR D n R1 R2 (unify_kr f D R1 R2 n)).
Proof.
  induction f as [|f IH]; [ split; intros; intros s D' n' H; discriminate | ].
  destruct IH as [IHt IHr].
  split.
  - intros D T1 T2 n. cbn [unify_k].
    destruct T1 as [| | | | | A B | R | a | i | B1 | w1 A1];
      destruct T2 as [| | | | | A' B' | R' | b | i' | B1' | w1' A1'];
      try apply spec_none;
      try apply spec_base;
      try apply bind_k_sound;
      try apply bind_k_sound_right;
      try apply spec_var_var;
      try (apply spec_unfold_left; apply IHt);
      try (apply spec_unfold_right; apply IHt).
    + (* Arrow, Arrow *)
      intros s D' n' H H1 H2.
      destruct (unify_k f D A A' n) as [[[s1 D1] n1]|] eqn:E1; [|discriminate].
      destruct (unify_k f D1 (apT s1 B) (apT s1 B') n1) as [[[s2 D2] n2]|] eqn:E2; [|discriminate].
      inversion H; subst; clear H.
      destruct (EvT_arrow_inv _ _ H1) as [EA EB].
      destruct (EvT_arrow_inv _ _ H2) as [EA' EB'].
      destruct (IHt D A A' n _ _ _ E1 EA EA') as (Hs1 & [m1 Ht1] & Hg1).
      destruct (IHt D1 _ _ n1 _ _ _ E2 (EvT_ap s1 B Hs1 EB) (EvT_ap s1 B' Hs1 EB'))
        as (Hs2 & [m2 Ht2] & Hg2).
      split; [ apply OkS_comp; auto | ].
      split.
      { exists (m1 + m2).
        change (apT (scomp s2 s1) (typ_Arrow A B))
          with (typ_Arrow (apT (scomp s2 s1) A) (apT (scomp s2 s1) B)).
        change (apT (scomp s2 s1) (typ_Arrow A' B'))
          with (typ_Arrow (apT (scomp s2 s1) A') (apT (scomp s2 s1) B')).
        rewrite <- !apT_comp. apply UE_arrow.
        - apply (unroll_mono m1); [ lia | exact (unroll_apT s2 _ _ _ Hs2 Ht1) ].
        - apply (unroll_mono m2); [ lia | exact Ht2 ]. }
      exact (GoodU_comp _ _ _ _ _ _ _ _ Hg1 Hg2).
    + (* Record, Record *)
      intros s D' n' H H1 H2.
      destruct (IHr D R R' n s D' n' H H1 H2) as (Hs & [m Hr] & Hg).
      refine (conj Hs (conj _ Hg)). exists m. apply UE_record. exact Hr.
    + (* Bvar, Bvar *)
      destruct (Nat.eqb i i') eqn:Ei.
      * apply Nat.eqb_eq in Ei. subst. apply spec_base.
      * apply spec_none.
    + (* Mu, Mu *)
      intros s D' n' H H1 H2.
      destruct (match unify_k f D B1 B1' n with
                | Some (s0, D1, n1) => if typ_eqb (apT s0 B1) (apT s0 B1') then Some (s0, D1, n1) else None
                | None => None
                end) as [r|] eqn:Ein.
      * inversion H; subst r; clear H.
        destruct (unify_k f D B1 B1' n) as [[[s0 D1] n1]|] eqn:Eu; [ | discriminate Ein ].
        destruct (typ_eqb (apT s0 B1) (apT s0 B1')) eqn:Eeq; [ | discriminate Ein ].
        inversion Ein; subst; clear Ein.
        destruct (IHt D B1 B1' n s D' n' Eu H1 H2) as (Hok & _ & Hg).
        refine (conj Hok (conj _ Hg)). exists 0. apply UE_teq.
        change (apT s (typ_Mu B1)) with (typ_Mu (apT s B1)).
        change (apT s (typ_Mu B1')) with (typ_Mu (apT s B1')).
        rewrite (proj1 typ_eqb_eq_mut _ _ Eeq). apply teq_refl.
      * exact (spec_unfold_left D n B1 (typ_Mu B1') _ (IHt D _ _ n) s D' n' H H1 H2).
    + (* Grp, Grp *)
      destruct (gdecl_eq_dec w1 w1') as [->|]; [ | apply spec_none ].
      intros s D' n' H H1 H2.
      destruct (IHt D A1 A1' n s D' n' H H1 H2) as (Hs & [m Ht] & Hg).
      refine (conj Hs (conj _ Hg)). exists m. apply UE_grp. exact Ht.
  - intros D R1 R2 n. cbn [unify_kr].
    assert (Hgen : forall R1 R2,
      SpecR D n R1 R2
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
       end)).
    { intros R1' R2' s' D'' n'' Hg Hg1 Hg2.
      destruct (row_head R1') as [[[[l P] T] R1'']|] eqn:Eh; [|discriminate].
      destruct (rewrite_row l (side_av R1') D R2' n) as [[[[[[P' T'] R2''] s0] D0] n1]|] eqn:Erw; [|discriminate].
      destruct (unify_k f D0 (apT s0 P) P' n1) as [[[sp D1] n2]|] eqn:Eu0; [|discriminate].
      destruct (unify_k f D1 (apT sp (apT s0 T)) (apT sp T') n2) as [[[s1 D2] n3]|] eqn:Eu1; [|discriminate].
      destruct (unify_kr f D2 (apR s1 (apR sp (apR s0 R1''))) (apR s1 (apR sp R2'')) n3)
        as [[[s2 D3] n4]|] eqn:Eu2; [|discriminate].
      inversion Hg; subst; clear Hg.
      destruct (row_head_sound _ _ _ _ _ Eh Hg1) as (HP & HT & HR1' & Hhd).
      destruct (rewrite_row_sound _ _ _ _ _ _ _ _ _ _ _ Erw Hg2) as (Hs0 & HP' & HT' & HR2' & Hrw & Hg0).
      destruct (IHt D0 _ _ n1 sp D1 n2 Eu0 (EvT_ap s0 P Hs0 HP) HP') as (Hsp & [mp Htp] & Hgp).
      destruct (IHt D1 _ _ n2 s1 D2 n3 Eu1 (EvT_ap sp _ Hsp (EvT_ap s0 T Hs0 HT)) (EvT_ap sp T' Hsp HT'))
        as (Hs1 & [mt Ht1] & Hg1').
      destruct (IHr D2 _ _ n3 _ _ _ Eu2
                  (EvR_ap s1 _ Hs1 (EvR_ap sp _ Hsp (EvR_ap s0 R1'' Hs0 HR1')))
                  (EvR_ap s1 _ Hs1 (EvR_ap sp _ Hsp HR2'))) as (Hs2 & [mr Hr2] & Hg2').
      split; [ apply OkS_comp; [ exact Hs2 | apply OkS_comp; [ exact Hs1 | apply OkS_comp; auto ] ] | ].
      split; [ exact (row_step_unroll s0 sp s1 s2 R1' R2' _ _ _ _ _ _ _ mp mt mr Hs2 Hs1 Hhd Hrw Htp Ht1 Hr2) | ].
      exact (GoodU_comp _ _ _ _ _ _ _ _
               (GoodU_comp _ _ _ _ _ _ _ _
                  (GoodU_comp _ _ _ _ _ _ _ _ Hg0 Hgp) Hg1') Hg2'). }
    destruct R1 as [| r | l T R1' | lm Pm Tm Rm]; destruct R2 as [| q | l2 T2 R2' | lm2 Pm2 Tm2 Rm2];
      try (intros s D' n' H H1 H2; apply lift_req;
           match type of H with
           | (if mgbr ?R then bind_row ?D ?a ?R ?n else None) = _ =>
               exact (var_left_Rk D a R n _ _ _ H H1 H2)
           end);
      try (intros s D' n' H H1 H2; apply lift_req;
           match type of H with
           | (if mgbr ?R then bind_row ?D ?a ?R ?n else None) = _ =>
               exact (var_right_Rk D a R n _ _ _ H H1 H2)
           end);
      try apply Hgen.
    + intros s D' n' H H1 H2. inversion H; subst.
      apply lift_req. split; [apply OkS_id | split; [apply req_refl | exact (GoodU_id _ _) ]].
    + (* Empty, Maybe: the same equation read the other way *)
      intros s D' n' H H1 H2.
      destruct (IHr D _ _ n s D' n' H H2 H1) as (Hs & [m Hr] & Hg).
      refine (conj Hs (conj _ Hg)). exists m. apply unroll_row_sym. exact Hr.
    + (* Var, Var *)
      intros s D' n' H H1 H2.
      destruct (Atom.eq_dec r q) as [->|Hne].
      * inversion H; subst. apply lift_req.
        split; [apply OkS_id | split; [apply req_refl | exact (GoodU_id _ _) ]].
      * apply lift_req. exact (bind_row_sound _ _ _ _ _ _ _ H H1 H2).
Qed.

(* ------------------------------------------------------------------ *)
(* What [bind_k] does, by case                                          *)
(* ------------------------------------------------------------------ *)

Lemma bind_k_ties : forall D a T n,
  lcb 0 T = true -> mgb T = true -> AtomSetImpl.mem a (ftv_typ T) = true ->
  gdb false false a T = true -> sat_b D (D a) (knot a T) = true ->
  bind_k D a T n = Some (sbT a (knot a T), D, n).
Proof.
  intros D a T n Hlc Hmg Hm Hg Hs. unfold bind_k. rewrite Hlc, Hmg, Hm, Hg, Hs. reflexivity.
Qed.

Lemma bind_k_unguarded : forall D a T n,
  lcb 0 T = true -> mgb T = true -> AtomSetImpl.mem a (ftv_typ T) = true ->
  gdb false false a T = false -> bind_k D a T n = None.
Proof.
  intros D a T n Hlc Hmg Hm Hg. unfold bind_k. rewrite Hlc, Hmg, Hm, Hg. reflexivity.
Qed.

Lemma bind_k_sorted : forall D a T n,
  lcb 0 T = true -> mgb T = true -> AtomSetImpl.mem a (ftv_typ T) = true ->
  sat_b D (D a) (knot a T) = false -> bind_k D a T n = None.
Proof.
  intros D a T n Hlc Hmg Hm Hs. unfold bind_k. rewrite Hlc, Hmg, Hm, Hs. rewrite Bool.andb_false_r. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The unifier at work                                                  *)
(* ------------------------------------------------------------------ *)

(* A record with a method: { moved : (a) -> Int }. *)
Definition ball_of (a : typ) : typ :=
  typ_Record (row_Ext 0 (typ_Arrow a typ_Int) row_Empty).
Definition ball_ty : typ := typ_Mu (ball_of (typ_Bvar 0)).
Definition ball_unrolled : typ := ball_of ball_ty.

Definition solved_at (r : option (sub * denv * nat)) (a : atom) (T : typ) : bool :=
  match r with
  | Some (s, _, _) => typ_eqb (apT s (typ_Var a)) T
  | None => false
  end.

Definition succeeds (r : option (sub * denv * nat)) : bool :=
  match r with Some _ => true | None => false end.

Ltac same_atoms :=
  repeat match goal with
  | |- context [Atom.eq_dec ?x ?x] =>
      destruct (Atom.eq_dec x x) as [_|?N]; [ | exfalso; apply N; reflexivity ]
  end.

(* Atoms do not compute (their equality is opaque), so the examples that
   mention a variable rewrite with the lemmas above instead of evaluating. *)
Lemma mem_ball : forall a, AtomSetImpl.mem a (ftv_typ (ball_of (typ_Var a))) = true.
Proof. intros a. apply AtomSetFacts.mem_iff. simpl. fsetdec. Qed.

Lemma guard_ball : forall a, gdb false false a (ball_of (typ_Var a)) = true.
Proof. intros a. cbn. same_atoms. reflexivity. Qed.

Example knot_ties : forall a,
  solved_at (unify_k 10 d_any (typ_Var a) (ball_of (typ_Var a)) 0) a ball_ty = true.
Proof.
  intros a.
  change (unify_k 10 d_any (typ_Var a) (ball_of (typ_Var a)) 0)
    with (bind_k d_any a (ball_of (typ_Var a)) 0).
  rewrite (bind_k_ties d_any a (ball_of (typ_Var a)) 0 eq_refl eq_refl (mem_ball a) (guard_ball a) eq_refl).
  unfold solved_at, apT, sbT. simpl. unfold knot, ball_ty, ball_of.
  cbn [abs_typ abs_row]. same_atoms. reflexivity.
Qed.

Example knot_ties_right : forall a,
  solved_at (unify_k 10 d_any (ball_of (typ_Var a)) (typ_Var a) 0) a ball_ty = true.
Proof.
  intros a.
  change (unify_k 10 d_any (ball_of (typ_Var a)) (typ_Var a) 0)
    with (bind_k d_any a (ball_of (typ_Var a)) 0).
  rewrite (bind_k_ties d_any a (ball_of (typ_Var a)) 0 eq_refl eq_refl (mem_ball a) (guard_ball a) eq_refl).
  unfold solved_at, apT, sbT. simpl. unfold knot, ball_ty, ball_of.
  cbn [abs_typ abs_row]. same_atoms. reflexivity.
Qed.

Example plain_unify_refuses : forall a,
  succeeds (unify_t 10 d_any (typ_Var a) (ball_of (typ_Var a)) 0) = false.
Proof.
  intros a.
  change (unify_t 10 d_any (typ_Var a) (ball_of (typ_Var a)) 0)
    with (bind_prop d_any a (ball_of (typ_Var a)) 0).
  unfold bind_prop, bind_prop0.
  assert (H : occT a (ball_of (typ_Var a)) = true).
  { unfold occT. rewrite (mem_ball a). reflexivity. }
  rewrite H. reflexivity.
Qed.

Example unguarded_is_refused : forall a,
  succeeds (unify_k 10 d_any (typ_Var a)
              (typ_Record (row_Ext 0 (typ_Var a) row_Empty)) 0) = false.
Proof.
  intros a.
  change (unify_k 10 d_any (typ_Var a) (typ_Record (row_Ext 0 (typ_Var a) row_Empty)) 0)
    with (bind_k d_any a (typ_Record (row_Ext 0 (typ_Var a) row_Empty)) 0).
  rewrite (bind_k_unguarded d_any a (typ_Record (row_Ext 0 (typ_Var a) row_Empty)) 0 eq_refl eq_refl).
  - reflexivity.
  - apply AtomSetFacts.mem_iff. simpl. fsetdec.
  - cbn. same_atoms. reflexivity.
Qed.

Example knot_needs_the_sort : forall a,
  succeeds (unify_k 10 (upd d_any a k_Numeric) (typ_Var a) (ball_of (typ_Var a)) 0) = false.
Proof.
  intros a.
  change (unify_k 10 (upd d_any a k_Numeric) (typ_Var a) (ball_of (typ_Var a)) 0)
    with (bind_k (upd d_any a k_Numeric) a (ball_of (typ_Var a)) 0).
  rewrite (bind_k_sorted (upd d_any a k_Numeric) a (ball_of (typ_Var a)) 0 eq_refl eq_refl (mem_ball a)).
  - reflexivity.
  - unfold upd. simpl. same_atoms. reflexivity.
Qed.

Example mu_meets_its_unrolling :
  succeeds (unify_k 10 d_any ball_ty ball_unrolled 0) = true /\
  succeeds (unify_k 10 d_any ball_unrolled ball_ty 0) = true.
Proof. vm_compute. split; reflexivity. Qed.

Example plain_unify_refuses_unrolling :
  succeeds (unify_t 10 d_any ball_ty ball_unrolled 0) = false.
Proof. vm_compute. reflexivity. Qed.

Example mu_is_not_int : succeeds (unify_k 10 d_any ball_ty typ_Int 0) = false.
Proof. vm_compute. reflexivity. Qed.

Example fuel_runs_out : succeeds (unify_k 1 d_any ball_ty ball_unrolled 0) = false.
Proof. vm_compute. reflexivity. Qed.

