(* Completeness of algorithm W, stage 7.7c, part L3: freshening a generalizing
   binder (docs/design/phase7-proof-plan.md).

   The completeness induction compares the algorithm's substitution with the
   derivation's types.  At a [let] of a value or a [letrec] the derivation
   generalizes the variables [V] of its first premise, and the comparison
   ([gen_mono_let], GoatCompleteLet.v) needs those variables to be even atoms
   that no type outside the premise mentions.  The derivation chooses [V]
   itself, so the induction asks for a derivation whose [V] is as wanted.

   This file renames [V] to even atoms outside a given finite set [B].  It is
   the [T_Let] and [T_Letrec] cases of [typing_tsubst_gen_mut] (GoatSound.v) run at
   the identity substitution with the renamer of [tsubst_gen_core_ren] set to
   [mk_rename_even]: the renaming bijection is the same, only the atoms it sends
   [V] to are even.  The atoms of the whole derivation are not touched; applying
   the lemma at every binder in turn is the normal form of the plan.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Goat.GoatSubst.
Require Import Goat.GoatBij.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Vectors.FinFun.
Import ListNotations.

(* ---- even atoms outside a finite set ---- *)

Lemma ea_inj : forall m n, ea m = ea n -> m = n.
Proof. intros m n H. unfold ea in H. apply idx_atom_inj in H. lia. Qed.

Lemma fresh_even : forall S : atoms, exists a, ev a /\ a `notin` S.
Proof.
  intros S. set (l := AtomSetImpl.elements S).
  destruct (existsb (fun m => negb (AtomSetImpl.mem (ea m) S)) (seq 0 (Datatypes.S (length l)))) eqn:E.
  - apply existsb_exists in E. destruct E as [m [_ Hm]].
    exists (ea m). split; [ apply ev_ea | ].
    apply Bool.negb_true_iff in Hm. apply AtomSetFacts.not_mem_iff. exact Hm.
  - exfalso.
    assert (Hin : incl (map ea (seq 0 (Datatypes.S (length l)))) l).
    { intros a Ha. apply in_map_iff in Ha. destruct Ha as [m [<- Hm]].
      assert (Hf : negb (AtomSetImpl.mem (ea m) S) = false).
      { destruct (negb (AtomSetImpl.mem (ea m) S)) eqn:Eb; [ | reflexivity ].
        exfalso. assert (Hx : existsb (fun m => negb (AtomSetImpl.mem (ea m) S)) (seq 0 (Datatypes.S (length l))) = true)
          by (apply existsb_exists; exists m; split; [ exact Hm | exact Eb ]).
        rewrite E in Hx. discriminate Hx. }
      apply Bool.negb_false_iff in Hf. apply AtomSetFacts.mem_iff in Hf.
      apply AtomSetFacts.elements_iff in Hf. apply SetoidList.InA_alt in Hf.
      destruct Hf as [y [Hy Hyl]]. subst y. exact Hyl. }
    assert (Hnd : NoDup (map ea (seq 0 (Datatypes.S (length l))))).
    { apply FinFun.Injective_map_NoDup; [ exact ea_inj | apply seq_NoDup ]. }
    pose proof (NoDup_incl_length Hnd Hin) as Hlen.
    rewrite length_map, length_seq in Hlen. lia.
Qed.

Lemma fresh_even_list : forall (n : nat) (S : atoms),
  exists l : list atom, length l = n /\ NoDup l /\ (forall x, In x l -> ev x /\ x `notin` S).
Proof.
  induction n as [|n IH]; intros S.
  - exists nil. split; [ reflexivity | split; [ constructor | intros x Hx; inversion Hx ] ].
  - destruct (fresh_even S) as [a [Hev Ha]].
    destruct (IH (S `union` {{a}})) as [l [Hl [Hnd Hx]]].
    exists (a :: l). split; [ simpl; lia | split ].
    + constructor; [ | exact Hnd ]. intros Hin. destruct (Hx a Hin) as [_ Hn]. fsetdec.
    + intros x [Hxa|Hin]; [ subst x; exact (conj Hev Ha) | ].
      destruct (Hx x Hin) as [H1 H2]. split; [ exact H1 | fsetdec ].
Qed.

(* [mk_rename] (GoatBij.v) with the fresh names taken even. *)
Lemma mk_rename_even : renamer ev.
Proof.
  intros V B.
  set (vl := AtomSetImpl.elements V).
  destruct (fresh_even_list (length vl) (B `union` V)) as [nt [Hlen' [Hnn Hnt]]].
  assert (Hlen : length vl = length nt) by (symmetry; exact Hlen').
  assert (Hnv : NoDup vl) by apply NoDup_elements.
  assert (Hdisj : forall x, In x vl -> ~ In x nt).
  { intros x Hx HC. destruct (Hnt x HC) as [_ Hn]. apply Hn. apply In_elements in Hx. fsetdec. }
  exists (perm (combine vl nt)), nt.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - apply perm_invol. apply nodup_supp_combine; auto.
  - intros x Hx. destruct (Hnt x Hx) as [_ H]. fsetdec.
  - intros x Hx. destruct (Hnt x Hx) as [_ H]. fsetdec.
  - intros x Hx. apply perm_combine_img; auto. apply In_elements; auto.
  - intros x HxV HxN. apply perm_fix.
    rewrite In_supp_combine by auto. intros [HC|HC].
    + apply HxV. apply In_elements; auto.
    + contradiction.
  - intros x Hx. exact (proj1 (Hnt x Hx)).
Qed.

(* ---- the identity substitution's side conditions ---- *)

Lemma tr_supp_id : forall A, tr_supp idt idr A.
Proof. intros A. split; [ intros a _; reflexivity | split; [ intros r _; reflexivity | apply lc_sub_id ] ]. Qed.

Lemma tr_compat_id : forall G, tr_compat idt idr G G.
Proof.
  intros G. unfold tr_compat. repeat split; intros a Ha; unfold idt, idr; simpl; fsetdec.
Qed.

Lemma ctx_subst_id : forall G, ctx_subst idt idr G G.
Proof. intros G. apply ctx_subst_weaken. intros x s H. exact H. Qed.

Lemma ap_typ_id : forall T, ap_typ idt idr T = T.
Proof. intros T. apply ap_typ_pointwise_id; reflexivity. Qed.

Lemma ap_row_id : forall R, ap_row idt idr R = R.
Proof.
  intros R. pose proof (ap_typ_id (typ_Record R)) as H. simpl in H. injection H as H. exact H.
Qed.

(* ---- [let] ---- *)

(* A [let]'s generalizing premise at a renamed type: the generalized atoms are
   even and outside [B], for [B] any finite set. *)
Lemma typing_let_even : forall (L : vars) D G e1 e2 T1 T2 (k : sort_fn) (rk : rkind_fn) (Tm : typ)
  (S B : atoms),
  supp_ok D S -> uniq G ->
  lit_pinned e1 (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G))) k ->
  typing (extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G))) k)
               (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G))) rk) G e1 T1 ->
  (forall x, x `notin` L ->
     typing D ((x ~ gen (pin_ctx Tm G) T1 k rk) ++ G) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
  exists (L' : vars) (T1' : typ) (k' : sort_fn) (rk' : rkind_fn),
    lit_pinned e1 (AtomSetImpl.diff (ftv_typ T1') (ftv_ctx (pin_ctx Tm G))) k' /\
    typing (extr (ext D (AtomSetImpl.diff (ftv_typ T1') (ftv_ctx (pin_ctx Tm G))) k')
                 (AtomSetImpl.diff (frv_typ T1') (frv_ctx (pin_ctx Tm G))) rk') G e1 T1' /\
    (forall x, x `notin` L' ->
       typing D ((x ~ gen (pin_ctx Tm G) T1' k' rk') ++ G) (open_exp_wrt_exp e2 (e_fvar_f x)) T2) /\
    (forall a, a `in` AtomSetImpl.diff (ftv_typ T1') (ftv_ctx (pin_ctx Tm G)) -> ev a /\ a `notin` B) /\
    (forall a, a `in` AtomSetImpl.diff (frv_typ T1') (frv_ctx (pin_ctx Tm G)) -> ev a /\ a `notin` B).
Proof.
  intros L D G e1 e2 T1 T2 k rk Tm S B HS Hu Hlp Ht1 Ht2.
  destruct (tsubst_gen_pin_ren ev mk_rename_even G Tm T1 k rk idt idr G B D D S S HS HS
              (kres_id D) (rkres_id D) (ctx_subst_id G) (tr_supp_id B) (tr_compat_id G))
    as (s' & st1 & sr1 & A1 & N & Nr & k' & rk' & Hk1 & Hkr1 & Hcs1 & Hsupp1 & Hcompat1 & HN & HNr
        & HS1 & Hsi & Hbr & Hcx & Hlk & HP & HPr).
  rewrite ap_typ_id in HN, HNr, Hbr.
  assert (Hext : denv_eq (extr (ext D N k') Nr rk')
    (extr (ext D (AtomSetImpl.diff (ftv_typ (ap_typ st1 sr1 T1)) (ftv_ctx (pin_ctx Tm G))) k')
          (AtomSetImpl.diff (frv_typ (ap_typ st1 sr1 T1)) (frv_ctx (pin_ctx Tm G))) rk')).
  { apply denv_eq_trans with (D2 := extr (ext D (AtomSetImpl.diff (ftv_typ (ap_typ st1 sr1 T1))
                                         (ftv_ctx (pin_ctx Tm G))) k') Nr rk').
    - apply extr_pw. apply ext_set_eq_d. exact HN.
    - apply extr_set_eq. exact HNr. }
  exists (L `union` dom G), (ap_typ st1 sr1 T1), k', rk'.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - intros Hc a Ha. apply (proj2 (HN a)) in Ha.
    destruct (Hlk a Ha) as [b [Hb Hkb]]. rewrite Hkb. apply Hlp; assumption.
  - eapply typing_pw.
    + apply (proj1 typing_tsubst_gen_mut _ G e1 T1 Ht1 st1 sr1 G (extr (ext D N k') Nr rk') A1
               (S `union` AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G))
                  `union` AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G)))
               (S `union` N `union` Nr)
               Hu (supp_ok_ext2 _ _ _ _ _ _ HS) HS1 Hk1 Hkr1 Hcs1 Hsupp1 Hcompat1).
    + exact Hext.
  - intros x Hx.
    apply typing_sch_equiv_ctx with (G := (x ~ s') ++ G).
    + pose proof (proj1 typing_tsubst_gen_mut _ ((x ~ gen (pin_ctx Tm G) T1 k rk) ++ G)
                    (open_exp_wrt_exp e2 (e_fvar_f x)) T2 (Ht2 x ltac:(fsetdec)) idt idr ((x ~ s') ++ G) D B S S
                    ltac:(constructor; [ exact Hu | fsetdec ]) HS HS (kres_id D) (rkres_id D)
                    ltac:(apply ctx_subst_cons; [ exact Hsi | exact (ctx_subst_id G) ])
                    (tr_supp_id B) (Hcx x)) as H.
      rewrite ap_typ_id in H. exact H.
    + apply ctx_equiv_cons; [ exact Hbr | apply ctx_equiv_refl ].
  - intros a Ha. apply (proj2 (HN a)) in Ha. exact (HP a Ha).
  - intros a Ha. apply (proj2 (HNr a)) in Ha. exact (HPr a Ha).
Qed.

(* ---- [letrec] ---- *)

Lemma typing_letrec_even : forall (L : vars) D G fs e2 R T (k : sort_fn) (rk : rkind_fn) (S B : atoms),
  supp_ok D S -> uniq G ->
  (forall p, p `notin` L ->
     field_typing (extr (ext D (AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G)) k)
                        (AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G)) rk)
       ((p ~ sch_mono (typ_Record R)) ++ G) (open_fields_wrt_exp fs (e_fvar_f p)) R) ->
  (forall p, p `notin` L ->
     typing D ((p ~ gen G (typ_Record R) k rk) ++ G) (open_exp_wrt_exp e2 (e_fvar_f p)) T) ->
  exists (L' : vars) (R' : row) (k' : sort_fn) (rk' : rkind_fn),
    (forall p, p `notin` L' ->
       field_typing (extr (ext D (AtomSetImpl.diff (ftv_typ (typ_Record R')) (ftv_ctx G)) k')
                          (AtomSetImpl.diff (frv_typ (typ_Record R')) (frv_ctx G)) rk')
         ((p ~ sch_mono (typ_Record R')) ++ G) (open_fields_wrt_exp fs (e_fvar_f p)) R') /\
    (forall p, p `notin` L' ->
       typing D ((p ~ gen G (typ_Record R') k' rk') ++ G) (open_exp_wrt_exp e2 (e_fvar_f p)) T) /\
    (forall a, a `in` AtomSetImpl.diff (ftv_typ (typ_Record R')) (ftv_ctx G) -> ev a /\ a `notin` B) /\
    (forall a, a `in` AtomSetImpl.diff (frv_typ (typ_Record R')) (frv_ctx G) -> ev a /\ a `notin` B).
Proof.
  intros L D G fs e2 R T k rk S B HS Hu Hfs Ht2.
  destruct (tsubst_gen_core_ren ev mk_rename_even G (typ_Record R) k rk idt idr G B D D S S HS HS
              (kres_id D) (rkres_id D) (ctx_subst_id G) (tr_supp_id B) (tr_compat_id G))
    as (s' & st1 & sr1 & A1 & N & Nr & k' & rk' & Hk1 & Hkr1 & Hcs1 & Hsupp1 & Hcompat1 & HN & HNr
        & HS1 & Hsi & Hbr & Hcx & Hctx & Hagt & Hagr & Hlk & HP & HPr).
  change (ap_typ st1 sr1 (typ_Record R)) with (typ_Record (ap_row st1 sr1 R)) in HN, HNr, Hbr.
  assert (Hext : denv_eq (extr (ext D N k') Nr rk')
    (extr (ext D (AtomSetImpl.diff (ftv_typ (typ_Record (ap_row st1 sr1 R))) (ftv_ctx G)) k')
          (AtomSetImpl.diff (frv_typ (typ_Record (ap_row st1 sr1 R))) (frv_ctx G)) rk')).
  { apply denv_eq_trans with (D2 := extr (ext D (AtomSetImpl.diff (ftv_typ (typ_Record (ap_row st1 sr1 R)))
                                         (ftv_ctx G)) k') Nr rk').
    - apply extr_pw. apply ext_set_eq_d. exact HN.
    - apply extr_set_eq. exact HNr. }
  exists (L `union` dom G), (ap_row st1 sr1 R), k', rk'.
  refine (conj _ (conj _ (conj _ _))).
  - intros p Hp.
    eapply field_typing_pw.
    + apply (proj2 typing_tsubst_gen_mut _ ((p ~ sch_mono (typ_Record R)) ++ G)
               (open_fields_wrt_exp fs (e_fvar_f p)) R (Hfs p ltac:(fsetdec)) st1 sr1
               ((p ~ sch_mono (ap_typ st1 sr1 (typ_Record R))) ++ G) (extr (ext D N k') Nr rk') A1
               (S `union` AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G)
                  `union` AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G))
               (S `union` N `union` Nr)).
      * constructor; [ exact Hu | fsetdec ].
      * apply supp_ok_ext2. exact HS.
      * exact HS1.
      * exact Hk1.
      * exact Hkr1.
      * apply ctx_subst_cons; [ apply sch_subst_mono | exact Hcs1 ].
      * exact Hsupp1.
      * apply tr_compat_cons_mono; exact Hcompat1.
    + exact Hext.
  - intros p Hp.
    apply typing_sch_equiv_ctx with (G := (p ~ s') ++ G).
    + pose proof (proj1 typing_tsubst_gen_mut _ ((p ~ gen G (typ_Record R) k rk) ++ G)
                    (open_exp_wrt_exp e2 (e_fvar_f p)) T (Ht2 p ltac:(fsetdec)) idt idr ((p ~ s') ++ G) D B S S
                    ltac:(constructor; [ exact Hu | fsetdec ]) HS HS (kres_id D) (rkres_id D)
                    ltac:(apply ctx_subst_cons; [ exact Hsi | exact (ctx_subst_id G) ])
                    (tr_supp_id B) (Hcx p)) as H.
      rewrite ap_typ_id in H. exact H.
    + apply ctx_equiv_cons; [ exact Hbr | apply ctx_equiv_refl ].
  - intros a Ha. apply (proj2 (HN a)) in Ha. exact (HP a Ha).
  - intros a Ha. apply (proj2 (HNr a)) in Ha. exact (HPr a Ha).
Qed.
