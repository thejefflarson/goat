(* Algorithm W never builds a recursive type (ADR 0037, decision 3).

   [infer] has no case for [e_fold] or [e_unfold], and [unify_t] has none for
   [typ_Mu] or [typ_Bvar].  Starting from a closed program, so with no
   recursive type in the context, every type and substitution it builds is
   free of [typ_Mu] and [typ_Bvar].  The incompleteness of the algorithm on
   the programs the checker types with a recursive type is therefore exactly
   this: [infer_mu_free].  See [docs/design/w-recursive-types-plan.md],
   option C. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatInfer.
Require Import Stdlib.Lists.List.
Import ListNotations.

Fixpoint mu_free (T : typ) : Prop :=
  match T with
  | typ_Mu _ | typ_Bvar _ => False
  | typ_Arrow A B => mu_free A /\ mu_free B
  | typ_Record R => mu_free_row R
  | _ => True
  end
with mu_free_row (R : row) : Prop :=
  match R with
  | row_Ext _ T R' => mu_free T /\ mu_free_row R'
  | _ => True
  end.

Definition mf_sub (s : sub) : Prop :=
  (forall a, mu_free (sT s a)) /\ (forall r, mu_free_row (sR s r)).

Definition mf_ctx (G : ctx) : Prop :=
  forall x s, In (x, s) G -> mu_free (s_body s).

Lemma ap_mf_mut :
  (forall T st sr, mu_free T -> (forall a, mu_free (st a)) -> (forall r, mu_free_row (sr r)) ->
     mu_free (ap_typ st sr T)) /\
  (forall R st sr, mu_free_row R -> (forall a, mu_free (st a)) -> (forall r, mu_free_row (sr r)) ->
     mu_free_row (ap_row st sr R)).
Proof.
  apply typ_row_mutind; intros; simpl in *; intuition auto.
Qed.

Lemma apT_mf : forall s T, mf_sub s -> mu_free T -> mu_free (apT s T).
Proof. intros s T [Ht Hr] H. exact (proj1 ap_mf_mut T (sT s) (sR s) H Ht Hr). Qed.

Lemma apR_mf : forall s R, mf_sub s -> mu_free_row R -> mu_free_row (apR s R).
Proof. intros s R [Ht Hr] H. exact (proj2 ap_mf_mut R (sT s) (sR s) H Ht Hr). Qed.

Lemma mf_sid : mf_sub sid.
Proof. split; intros; exact I. Qed.

Lemma mf_scomp : forall s2 s1, mf_sub s2 -> mf_sub s1 -> mf_sub (scomp s2 s1).
Proof.
  intros s2 s1 H2 [Ht Hr]. split; intros x; simpl.
  - apply apT_mf; auto.
  - apply apR_mf; auto.
Qed.

Lemma mf_sbT : forall a T, mu_free T -> mf_sub (sbT a T).
Proof.
  intros a T H. split; intros x; simpl.
  - destruct (Atom.eq_dec x a); [exact H | exact I].
  - exact I.
Qed.

Lemma mf_sbR : forall r R, mu_free_row R -> mf_sub (sbR r R).
Proof.
  intros r R H. split; intros x; simpl.
  - exact I.
  - destruct (Atom.eq_dec x r); [exact H | exact I].
Qed.

Lemma mf_apC : forall s G, mf_sub s -> mf_ctx G -> mf_ctx (apC s G).
Proof.
  intros s G Hs HG x sc Hin. unfold apC in Hin.
  apply in_map_iff in Hin. destruct Hin as [[y sc0] [Heq Hin]].
  injection Heq as <- <-. simpl. apply apT_mf; auto. exact (HG y sc0 Hin).
Qed.

Lemma mf_cons : forall x sc G, mu_free (s_body sc) -> mf_ctx G -> mf_ctx ((x, sc) :: G).
Proof.
  intros x sc G H HG y s Hin. destruct Hin as [Heq | Hin].
  - injection Heq as <- <-. exact H.
  - exact (HG y s Hin).
Qed.

Lemma rewrite_row_mf : forall l av R n T R' s n',
  rewrite_row l av R n = Some (T, R', s, n') ->
  mu_free_row R -> mu_free T /\ mu_free_row R' /\ mf_sub s.
Proof.
  intros l av R. induction R as [|r|l' T' R'' IH]; intros n T R' s n' H HR; simpl in H.
  - discriminate.
  - destruct (AtomSetImpl.mem r av); [discriminate|].
    injection H as <- <- <- <-.
    exact (conj I (conj I (mf_sbR r (row_Ext l (typ_Var (ea n)) (row_Var (ea (S n)))) (conj I I)))).
  - destruct HR as [HT' HR''].
    destruct (Nat.eqb l l').
    + injection H as <- <- <- <-. exact (conj HT' (conj HR'' mf_sid)).
    + destruct (rewrite_row l av R'' n) as [[[[T0 R3] s0] n1]|] eqn:E; [|discriminate].
      injection H as <- <- <- <-.
      destruct (IH _ _ _ _ _ E HR'') as [H1 [H2 H3]].
      refine (conj H1 (conj _ H3)). exact (conj (apT_mf _ _ H3 HT') H2).
Qed.

Lemma unify_mf : forall f,
  (forall Dk T1 T2 n s n', unify_t f Dk T1 T2 n = Some (s, n') ->
     mu_free T1 -> mu_free T2 -> mf_sub s) /\
  (forall Dk R1 R2 n s n', unify_r f Dk R1 R2 n = Some (s, n') ->
     mu_free_row R1 -> mu_free_row R2 -> mf_sub s) /\
  (forall Dk R1 R2 n s n', unify_pw f Dk R1 R2 n = Some (s, n') ->
     mu_free_row R1 -> mu_free_row R2 -> mf_sub s).
Proof.
  induction f as [|f IH]; [refine (conj _ (conj _ _)); intros; discriminate|].
  destruct IH as [IHt [IHr IHp]].
  refine (conj _ (conj _ _)).
  - intros Dk T1 T2 n s n' H H1 H2. simpl in H.
    destruct T1, T2; try discriminate;
      try (injection H as <- <-; exact mf_sid);
      try (destruct (occT _ _); [discriminate|]; destruct (sat_b _ _ _); [|discriminate];
           injection H as <- <-; apply mf_sbT; simpl; auto; fail);
      try (destruct (Atom.eq_dec _ _); [injection H as <- <-; exact mf_sid|];
           destruct (finer_b _ _); injection H as <- <-; apply mf_sbT; exact I).
    + destruct (unify_t f Dk T1_1 T2_1 n) as [[s1 n1]|] eqn:E1; [|discriminate].
      destruct (unify_t f Dk (apT s1 T1_2) (apT s1 T2_2) n1) as [[s2 n2]|] eqn:E2; [|discriminate].
      injection H as <- <-.
      assert (Hs1 := IHt _ _ _ _ _ _ E1 (proj1 H1) (proj1 H2)).
      apply mf_scomp; [|exact Hs1].
      eapply IHt; [exact E2 | apply apT_mf; auto; apply H1 | apply apT_mf; auto; apply H2].
    + eapply IHr; [exact H | exact H1 | exact H2].
  - intros Dk R1 R2 n s n' H H1 H2. simpl in H.
    destruct R1 as [|r|l T R1'].
    + destruct R2 as [|r2|l2 T2 R2']; try discriminate.
      * injection H as <- <-. exact mf_sid.
      * destruct (occR r2 row_Empty); [discriminate|]. injection H as <- <-. apply mf_sbR. exact I.
    + destruct R2 as [|r2|l2 T2 R2'].
      * destruct (occR r row_Empty); [discriminate|]. injection H as <- <-. apply mf_sbR. exact I.
      * destruct (Atom.eq_dec r r2); [injection H as <- <-; exact mf_sid|].
        injection H as <- <-. apply mf_sbR. exact I.
      * destruct (occR r _); [discriminate|]. injection H as <- <-. apply mf_sbR. exact H2.
    + destruct R2 as [|r2|l2 T2 R2']; try discriminate.
      * destruct (occR r2 _); [discriminate|]. injection H as <- <-. apply mf_sbR. exact H1.
      * destruct (rewrite_row l _ _ n) as [[[[T' R2x] s0] n1]|] eqn:E0; [|discriminate].
        destruct (unify_t f Dk (apT s0 T) T' n1) as [[s1 n2]|] eqn:E1; [|discriminate].
        destruct (unify_r f Dk (apR s1 (apR s0 R1')) (apR s1 R2x) n2) as [[s2 n3]|] eqn:E2; [|discriminate].
        injection H as <- <-.
        destruct (rewrite_row_mf _ _ _ _ _ _ _ _ E0 H2) as [M1 [M2 M3]].
        destruct H1 as [H1a H1b].
        assert (Hs1 := IHt _ _ _ _ _ _ E1 (apT_mf _ _ M3 H1a) M1).
        assert (Hs2 := IHr _ _ _ _ _ _ E2 (apR_mf _ _ Hs1 (apR_mf _ _ M3 H1b)) (apR_mf _ _ Hs1 M2)).
        apply mf_scomp; [exact Hs2|]. apply mf_scomp; assumption.
  - intros Dk R1 R2 n s n' H H1 H2. simpl in H.
    destruct R1 as [|r|l T R1'], R2 as [|r2|l2 T2 R2']; try discriminate.
    + injection H as <- <-. exact mf_sid.
    + destruct (Nat.eqb l l2); [|discriminate].
      destruct (unify_t f Dk T T2 n) as [[s1 n1]|] eqn:E1; [|discriminate].
      destruct (unify_pw f Dk (apR s1 R1') (apR s1 R2') n1) as [[s2 n2]|] eqn:E2; [|discriminate].
      injection H as <- <-.
      destruct H1 as [H1a H1b]. destruct H2 as [H2a H2b].
      assert (Hs1 := IHt _ _ _ _ _ _ E1 H1a H2a).
      apply mf_scomp; [|exact Hs1].
      eapply IHp; [exact E2 | apply apR_mf; auto | apply apR_mf; auto].
Qed.

Lemma inst_sub_mf : forall sc n, mf_sub (inst_sub sc n).
Proof.
  intros sc n. unfold inst_sub. split; intros x; simpl.
  - destruct (in_dec Atom.eq_dec x _); exact I.
  - destruct (in_dec Atom.eq_dec x _); exact I.
Qed.

Lemma instantiate_mf : forall D sc n T D' n',
  instantiate D sc n = (T, D', n') -> mu_free (s_body sc) -> mu_free T.
Proof.
  intros D sc n T D' n' H Hb. unfold instantiate in H.
  injection H as <- <- <-. apply apT_mf; [apply inst_sub_mf | exact Hb].
Qed.

Lemma lookup_mf : forall x G sc, lookup x G = Some sc -> mf_ctx G -> mu_free (s_body sc).
Proof.
  intros x G. induction G as [|[y s0] G IH]; intros sc H HG; simpl in H; [discriminate|].
  destruct (Atom.eq_dec x y).
  - injection H as <-. exact (HG y s0 (or_introl eq_refl)).
  - apply IH; [exact H|]. intros z s1 Hin. exact (HG z s1 (or_intror Hin)).
Qed.

Lemma gen_ren_mf : forall D G T, mu_free T -> mu_free (s_body (gen_ren D G T)).
Proof.
  intros D G T H. unfold gen_ren. simpl.
  apply (proj1 ap_mf_mut T _ _ H).
  - intros a. unfold rename_t. destruct (in_dec Atom.eq_dec a _); exact I.
  - intros r. unfold rename_r. destruct (in_dec Atom.eq_dec r _); exact I.
Qed.

Lemma group_row_mf : forall fs n, mu_free_row (group_row fs n).
Proof.
  induction fs as [|l e rest IH]; intros n; simpl; [exact I|].
  split; [exact I | apply IH].
Qed.

Lemma infer_mf : forall f,
  (forall Dk G e n s D' T n', infer f Dk G e n = Some (s, D', T, n') ->
     mf_ctx G -> mf_sub s /\ mu_free T) /\
  (forall Dk G fs n s D' R n', infer_fields f Dk G fs n = Some (s, D', R, n') ->
     mf_ctx G -> mf_sub s /\ mu_free_row R).
Proof.
  induction f as [|f IH]; [split; intros; discriminate|].
  destruct IH as [IHi IHf].
  split.
  - intros Dk G e n s D' T n' H HG.
    destruct e as [i|x|k|d| | |b|e1 e2|e1 e2|fs e2|fs|e1 l| |q|c e1 e2|e1 o e2|e1|e1|e1];
      simpl in H; try discriminate;
      try (injection H as <- <- <- <-; exact (conj mf_sid I)).
    + destruct (lookup x G) as [sc|] eqn:EL; [|discriminate].
      destruct (instantiate Dk sc n) as [[T0 D1] n1] eqn:EI.
      injection H as <- <- <- <-.
      exact (conj mf_sid (apT_mf _ _ (inst_sub_mf _ _) (lookup_mf _ _ _ EL HG))).
    + destruct (infer f Dk ((fresh_var G b, sch_mono (typ_Var (ea n))) :: G)
                  (open_exp_wrt_exp b (e_fvar_f (fresh_var G b))) (S n))
        as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      injection H as <- <- <- <-.
      destruct (IHi _ _ _ _ _ _ _ _ E1 (mf_cons _ (sch_mono (typ_Var (ea n))) _ I HG)) as [S1 M1].
      exact (conj S1 (conj (apT_mf _ (typ_Var _) S1 I) M1)).
    + destruct (infer f Dk G e1 n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      destruct (IHi _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      destruct (infer f D1 (apC s1 G) e2 n1) as [[[[s2 D2] T2] n2]|] eqn:E2; [|discriminate].
      destruct (IHi _ _ _ _ _ _ _ _ E2 (mf_apC _ _ S1 HG)) as [S2 M2].
      destruct (unify_t f D2 (apT s2 T1) (typ_Arrow T2 (typ_Var (ea n2))) (S n2))
        as [[s3 n3]|] eqn:E3; [|discriminate].
      injection H as <- <- <- <-.
      assert (S3 := proj1 (unify_mf f) _ _ _ _ _ _ E3 (apT_mf _ _ S2 M1) (conj M2 I)).
      exact (conj (mf_scomp _ _ S3 (mf_scomp _ _ S2 S1)) (apT_mf _ (typ_Var _) S3 I)).
    + destruct (is_gen_value e1).
      * destruct (infer f Dk G e1 n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
        destruct (IHi _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
        destruct (infer f D1 ((fresh_var (apC s1 G) e2, gen_ren D1 (apC s1 G) T1) :: apC s1 G)
                    (open_exp_wrt_exp e2 (e_fvar_f (fresh_var (apC s1 G) e2))) n1)
          as [[[[s2 D2] T2] n2]|] eqn:E2; [|discriminate].
        injection H as <- <- <- <-.
        destruct (IHi _ _ _ _ _ _ _ _ E2 (mf_cons _ _ _ (gen_ren_mf _ _ _ M1) (mf_apC _ _ S1 HG))) as [S2 M2].
        exact (conj (mf_scomp _ _ S2 S1) M2).
      * destruct (infer f Dk G e1 n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
        destruct (IHi _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
        destruct (infer f D1 ((fresh_var (apC s1 G) e2, sch_mono T1) :: apC s1 G)
                    (open_exp_wrt_exp e2 (e_fvar_f (fresh_var (apC s1 G) e2))) n1)
          as [[[[s2 D2] T2] n2]|] eqn:E2; [|discriminate].
        injection H as <- <- <- <-.
        destruct (IHi _ _ _ _ _ _ _ _ E2 (mf_cons _ (sch_mono T1) _ M1 (mf_apC _ _ S1 HG))) as [S2 M2].
        exact (conj (mf_scomp _ _ S2 S1) M2).
    + destruct (is_fn_group fs); [|discriminate].
      destruct (infer_fields f Dk ((fresh_var G (e_rec fs), sch_mono (typ_Record (group_row fs n))) :: G)
                  (open_fields_wrt_exp fs (e_fvar_f (fresh_var G (e_rec fs)))) (n + nfields fs))
        as [[[[s1 D1] R1] n1]|] eqn:E1; [|discriminate].
      destruct (IHf _ _ _ _ _ _ _ _ E1 (mf_cons _ (sch_mono (typ_Record (group_row fs n))) _ (group_row_mf _ _) HG)) as [S1 M1].
      destruct (unify_pw f D1 R1 (apR s1 (group_row fs n)) n1) as [[s2 n2]|] eqn:E2; [|discriminate].
      assert (S2 := proj2 (proj2 (unify_mf f)) _ _ _ _ _ _ E2 M1 (apR_mf _ _ S1 (group_row_mf _ _))).
      assert (Sc := mf_scomp _ _ S2 S1).
      destruct (infer f D1 ((fresh_var (apC (scomp s2 s1) G) e2,
                   gen_ren D1 (apC (scomp s2 s1) G) (typ_Record (apR (scomp s2 s1) (group_row fs n))))
                  :: apC (scomp s2 s1) G)
                  (open_exp_wrt_exp e2 (e_fvar_f (fresh_var (apC (scomp s2 s1) G) e2))) n2)
        as [[[[s3 D3] T3] n3]|] eqn:E3; [|discriminate].
      injection H as <- <- <- <-.
      destruct (IHi _ _ _ _ _ _ _ _ E3
        (mf_cons _ _ _ (gen_ren_mf _ _ (typ_Record _) (apR_mf _ _ Sc (group_row_mf _ _))) (mf_apC _ _ Sc HG))) as [S3 M3].
      exact (conj (mf_scomp _ _ S3 Sc) M3).
    + destruct (infer_fields f Dk G fs n) as [[[[s1 D1] R1] n1]|] eqn:E1; [|discriminate].
      injection H as <- <- <- <-.
      destruct (IHf _ _ _ _ _ _ _ _ E1 HG) as [S1 M1]. exact (conj S1 M1).
    + destruct (infer f Dk G e1 n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      destruct (IHi _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      destruct (unify_t f D1 T1 (typ_Record (row_Ext l (typ_Var (ea n1)) (row_Var (ea (S n1))))) (n1 + 2))
        as [[s2 n2]|] eqn:E2; [|discriminate].
      injection H as <- <- <- <-.
      assert (S2 := proj1 (unify_mf f) _ _ _ _ _ _ E2 M1 (conj I I)).
      exact (conj (mf_scomp _ _ S2 S1) (apT_mf _ (typ_Var _) S2 I)).
    + destruct (infer f Dk G c n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      destruct (IHi _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      destruct (unify_t f D1 T1 typ_Bool n1) as [[s2 n2]|] eqn:E2; [|discriminate].
      assert (S2 := proj1 (unify_mf f) _ _ _ _ _ _ E2 M1 I).
      destruct (infer f D1 (apC s2 (apC s1 G)) e1 n2) as [[[[s3 D3] T2] n3]|] eqn:E3; [|discriminate].
      destruct (IHi _ _ _ _ _ _ _ _ E3 (mf_apC _ _ S2 (mf_apC _ _ S1 HG))) as [S3 M2].
      destruct (infer f D3 (apC s3 (apC s2 (apC s1 G))) e2 n3) as [[[[s4 D4] T3] n4]|] eqn:E4; [|discriminate].
      destruct (IHi _ _ _ _ _ _ _ _ E4 (mf_apC _ _ S3 (mf_apC _ _ S2 (mf_apC _ _ S1 HG)))) as [S4 M3].
      destruct (unify_t f D4 (apT s4 T2) T3 n4) as [[s5 n5]|] eqn:E5; [|discriminate].
      injection H as <- <- <- <-.
      assert (S5 := proj1 (unify_mf f) _ _ _ _ _ _ E5 (apT_mf _ _ S4 M2) M3).
      exact (conj (mf_scomp _ _ S5 (mf_scomp _ _ S4 (mf_scomp _ _ S3 (mf_scomp _ _ S2 S1))))
                  (apT_mf _ _ S5 M3)).
    + destruct (infer f Dk G e1 n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      destruct (IHi _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      destruct (infer f D1 (apC s1 G) e2 n1) as [[[[s2 D2] T2] n2]|] eqn:E2; [|discriminate].
      destruct (IHi _ _ _ _ _ _ _ _ E2 (mf_apC _ _ S1 HG)) as [S2 M2].
      destruct (is_generic_op o).
      * destruct (unify_t f (upd D2 (ea n2) k_Numeric) (apT s2 T1) (typ_Var (ea n2)) (S n2))
          as [[s3 n3]|] eqn:E3; [|discriminate].
        assert (S3 := proj1 (unify_mf f) _ _ _ _ _ _ E3 (apT_mf _ _ S2 M1) I).
        destruct (unify_t f (upd D2 (ea n2) k_Numeric) (apT s3 T2) (apT s3 (typ_Var (ea n2))) n3)
          as [[s4 n4]|] eqn:E4; [|discriminate].
        injection H as <- <- <- <-.
        assert (S4 := proj1 (unify_mf f) _ _ _ _ _ _ E4 (apT_mf _ _ S3 M2) (apT_mf _ (typ_Var _) S3 I)).
        exact (conj (mf_scomp _ _ S4 (mf_scomp _ _ S3 (mf_scomp _ _ S2 S1)))
                    (apT_mf _ _ S4 (apT_mf _ (typ_Var _) S3 I))).
      * destruct (bin_arg D2 o (apT s2 T1) T2) as [T0|] eqn:EB; [|discriminate].
        destruct (unify_t f D2 (apT s2 T1) T0 n2) as [[s3 n3]|] eqn:E3; [|discriminate].
        destruct (unify_t f D2 (apT s3 T2) T0 n3) as [[s4 n4]|] eqn:E4; [|discriminate].
        destruct (bin_ty o T0) as [R|] eqn:ER; [|discriminate].
        injection H as <- <- <- <-.
        assert (MT : mu_free T0).
        { unfold bin_arg in EB. destruct (kind o); try discriminate.
          - injection EB as <-. exact I.
          - destruct (cmp_ty T2) eqn:C2.
            + injection EB as <-. destruct T2; simpl in C2; try discriminate; exact I.
            + destruct (cmp_ty (apT s2 T1)) eqn:C1.
              * injection EB as <-. destruct (apT s2 T1); simpl in C1; try discriminate; exact I.
              * destruct (is_literal D2 (apT s2 T1) || is_literal D2 T2); [|discriminate].
                injection EB as <-. exact I. }
        assert (S3 := proj1 (unify_mf f) _ _ _ _ _ _ E3 (apT_mf _ _ S2 M1) MT).
        assert (S4 := proj1 (unify_mf f) _ _ _ _ _ _ E4 (apT_mf _ _ S3 M2) MT).
        refine (conj (mf_scomp _ _ S4 (mf_scomp _ _ S3 (mf_scomp _ _ S2 S1))) _).
        unfold bin_ty in ER. destruct (kind o), T0; try discriminate; injection ER as <-; exact I.
    + destruct (infer f Dk G e1 n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
      destruct (IHi _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
      destruct (unify_t f (upd D1 (ea n1) k_Numeric) T1 (typ_Var (ea n1)) (S n1))
        as [[s2 n2]|] eqn:E2; [|discriminate].
      injection H as <- <- <- <-.
      assert (S2 := proj1 (unify_mf f) _ _ _ _ _ _ E2 M1 I).
      exact (conj (mf_scomp _ _ S2 S1) I).
  - intros Dk G fs n s D' R n' H HG.
    destruct fs as [|l e rest]; simpl in H; [injection H as <- <- <- <-; exact (conj mf_sid I)|].
    destruct (infer f Dk G e n) as [[[[s1 D1] T1] n1]|] eqn:E1; [|discriminate].
    destruct (IHi _ _ _ _ _ _ _ _ E1 HG) as [S1 M1].
    destruct (infer_fields f D1 (apC s1 G) rest n1) as [[[[s2 D2] R2] n2]|] eqn:E2; [|discriminate].
    destruct (IHf _ _ _ _ _ _ _ _ E2 (mf_apC _ _ S1 HG)) as [S2 M2].
    injection H as <- <- <- <-.
    exact (conj (mf_scomp _ _ S2 S1) (conj (apT_mf _ _ S2 M1) M2)).
Qed.

Theorem infer_mu_free : forall fuel e D T,
  infer_closed_env fuel e = Some (D, T) -> mu_free T.
Proof.
  intros fuel e D T H. unfold infer_closed_env in H.
  destruct (infer fuel d_any nil e 0) as [[[[s D1] T1] n]|] eqn:E; [|discriminate].
  injection H as <- <-.
  exact (proj2 (proj1 (infer_mf fuel) _ _ _ _ _ _ _ _ E (fun x s0 Hin => match Hin with end))).
Qed.

Lemma infer_fold_none : forall f D G e n, infer f D G (e_fold e) n = None.
Proof. intros [|f] D G e n; reflexivity. Qed.

Lemma infer_unfold_none : forall f D G e n, infer f D G (e_unfold e) n = None.
Proof. intros [|f] D G e n; reflexivity. Qed.
