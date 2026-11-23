(* Completeness of algorithm W, stage 7.7c, part L3: a normal form for [typing]
   (docs/design/phase7-proof-plan.md).

   [ntyping Av D G e T] is [typing D G e T] with one extra demand at each
   [T_Let] and [T_Letrec]: the atoms the binder generalizes are even and outside
   [Av], a set of the atoms live around the binder.  Each rule gives its
   premises the atoms the judgement itself holds (the type, the context and the
   types of the premises' siblings), so [Av] at a binder holds every atom of the
   judgements that enclose it and of the sibling judgements beside it, and the
   generalized atoms avoid all of them.  The completeness induction needs that
   of the derivation: the algorithm's substitution carries the derivation's types
   for the atoms that are still in play, and re-sorting the generalized atoms
   for the binder's first premise must not touch them ([gen_mono_let],
   GoatCompleteLet.v).

   [typing_normal] says every derivation, over an environment of finite support,
   has a normal form at the same judgement and any [Av].  The proof is by
   induction on the size of the term: [typing_let_even] and [typing_letrec_even]
   (GoatCompleteFresh.v) rename a binder's generalized atoms, which replaces the
   premises with derivations that are not subderivations, so the induction
   hypothesis is about terms rather than derivations.  [ntyping_typing] is the
   converse, so the normal form changes no judgement.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatCompleteFresh.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Import ListNotations.

(* ---- the size of a term ---- *)

Fixpoint esz (e : exp) : nat :=
  match e with
  | e_fvar_b _ | e_fvar_f _ | e_num _ | e_dec _ | e_true | e_false | e_unit | e_str _ => 1
  | e_abs e1 => Datatypes.S (esz e1)
  | e_app e1 e2 => Datatypes.S (esz e1 + esz e2)
  | e_let e1 e2 => Datatypes.S (esz e1 + esz e2)
  | e_letrec fs e2 => Datatypes.S (fsz fs + esz e2)
  | e_rec fs => Datatypes.S (fsz fs)
  | e_proj e1 _ => Datatypes.S (esz e1)
  | e_ite e1 e2 e3 => Datatypes.S (esz e1 + esz e2 + esz e3)
  | e_bin e1 _ e2 => Datatypes.S (esz e1 + esz e2)
  | e_tofloat e1 => Datatypes.S (esz e1)
  | e_con _ _ e1 => Datatypes.S (esz e1)
  | e_match _ e1 ars => Datatypes.S (esz e1 + asz ars)
  | e_spread e1 _ e2 => Datatypes.S (esz e1 + esz e2)
  | e_restrict e1 _ => Datatypes.S (esz e1)
  | e_fold e1 => Datatypes.S (esz e1)
  | e_unfold e1 => Datatypes.S (esz e1)
  end
with fsz (fs : fields) : nat :=
  match fs with
  | fs_nil => 0
  | fs_cons _ e fs' => Datatypes.S (esz e + fsz fs')
  | fs_meth _ e fs' => Datatypes.S (esz e + fsz fs')
  end
with asz (ars : arms) : nat :=
  match ars with
  | arms_nil => 0
  | arms_else e => Datatypes.S (esz e)
  | arms_cons _ e ars' => Datatypes.S (esz e + asz ars')
  end.

Lemma esz_open_mut :
  (forall e k x, esz (open_exp_wrt_exp_rec k (e_fvar_f x) e) = esz e) /\
  (forall fs k x, fsz (open_fields_wrt_exp_rec k (e_fvar_f x) fs) = fsz fs) /\
  (forall ars k x, asz (open_arms_wrt_exp_rec k (e_fvar_f x) ars) = asz ars).
Proof.
  apply exp_fields_mutind; intros; simpl; try reflexivity;
    try (rewrite ?H, ?H0, ?H1; reflexivity).
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Lemma esz_open : forall e x, esz (open_exp_wrt_exp e (e_fvar_f x)) = esz e.
Proof. intros e x. exact (proj1 esz_open_mut e 0 x). Qed.

Lemma fsz_open : forall fs x, fsz (open_fields_wrt_exp fs (e_fvar_f x)) = fsz fs.
Proof. intros fs x. exact (proj1 (proj2 esz_open_mut) fs 0 x). Qed.

Lemma arms_find_sz : forall ars tg b, arms_find tg ars = Some b -> esz b < asz ars.
Proof.
  induction ars as [|e|tg0 e ars IH]; simpl; intros tg b H; try discriminate.
  destruct (Nat.eqb tg tg0).
  - injection H as <-. lia.
  - specialize (IH tg b H). lia.
Qed.

Lemma arms_default_sz : forall ars e0, arms_default ars = Some e0 -> esz e0 < asz ars.
Proof.
  induction ars as [|e|tg0 e ars IH]; simpl; intros e0 H; try discriminate.
  - injection H as <-. lia.
  - specialize (IH e0 H). lia.
Qed.

(* ---- the normal form ---- *)

Definition ats (T : typ) : atoms := ftv_typ T `union` frv_typ T.
Definition atc (G : ctx) : atoms := ftv_ctx G `union` frv_ctx G.

(* What a judgement adds to the atoms its premises must avoid. *)
Definition bg (Av : atoms) (G : ctx) (T : typ) : atoms := Av `union` ats T `union` atc G.

Inductive ntyping : atoms -> denv -> ctx -> exp -> typ -> Prop :=
 | N_Var : forall Av D G x s T,
     uniq G -> binds x s G -> inst D T s -> ntyping Av D G (e_fvar_f x) T
 | N_Num : forall Av D G n T, uniq G -> sat D k_Literal T -> ntyping Av D G (e_num n) T
 | N_Dec : forall Av D G d, uniq G -> ntyping Av D G (e_dec d) typ_Float
 | N_True : forall Av D G, uniq G -> ntyping Av D G e_true typ_Bool
 | N_False : forall Av D G, uniq G -> ntyping Av D G e_false typ_Bool
 | N_Abs : forall (L : vars) Av D G e T1 T2,
     (forall x, x `notin` L ->
        ntyping (bg Av G (typ_Arrow T1 T2)) D ((x ~ sch_mono T1) ++ G) (open_exp_wrt_exp e (e_fvar_f x)) T2) ->
     ntyping Av D G (e_abs e) (typ_Arrow T1 T2)
 | N_App : forall Av D G e1 e2 T1 T2,
     ntyping (bg Av G T2 `union` ats T1) D G e1 (typ_Arrow T1 T2) ->
     ntyping (bg Av G T2 `union` ats T1) D G e2 T1 ->
     ntyping Av D G (e_app e1 e2) T2
 | N_Let : forall (L : vars) Av D G e1 e2 T1 T2 (k : sort_fn) (rk : rkind_fn) (Tm : typ),
     is_gen_value e1 = true ->
     lit_pinned e1 (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G))) k ->
     (forall a, a `in` AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G)) ->
        ev a /\ a `notin` bg Av G T2) ->
     (forall a, a `in` AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G)) ->
        ev a /\ a `notin` bg Av G T2) ->
     ntyping (bg Av G T2)
       (extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G))) k)
             (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G))) rk) G e1 T1 ->
     (forall x, x `notin` L ->
        ntyping (bg Av G T2) D ((x ~ gen (pin_ctx Tm G) T1 k rk) ++ G)
          (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
     ntyping Av D G (e_let e1 e2) T2
 | N_LetMono : forall (L : vars) Av D G e1 e2 T1 T2,
     ntyping (bg Av G T2 `union` ats T1) D G e1 T1 ->
     (forall x, x `notin` L ->
        ntyping (bg Av G T2 `union` ats T1) D ((x ~ sch_mono T1) ++ G)
          (open_exp_wrt_exp e2 (e_fvar_f x)) T2) ->
     ntyping Av D G (e_let e1 e2) T2
 | N_Letrec : forall (L : vars) Av D G fs e2 R T (k : sort_fn) (rk : rkind_fn),
     fn_group fs ->
     (forall a, a `in` AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G) ->
        ev a /\ a `notin` bg Av G T) ->
     (forall a, a `in` AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G) ->
        ev a /\ a `notin` bg Av G T) ->
     (forall p, p `notin` L ->
        nfield_typing (bg Av G T)
          (extr (ext D (AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G)) k)
                (AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G)) rk)
          ((p ~ sch_mono (typ_Record R)) ++ G) (open_fields_wrt_exp fs (e_fvar_f p)) R) ->
     (forall p, p `notin` L ->
        ntyping (bg Av G T) D ((p ~ gen G (typ_Record R) k rk) ++ G)
          (open_exp_wrt_exp e2 (e_fvar_f p)) T) ->
     ntyping Av D G (e_letrec fs e2) T
 | N_Record : forall Av D G fs R,
     nfield_typing (bg Av G (typ_Record R)) D G fs R -> no_meth fs = true ->
     ntyping Av D G (e_rec fs) (typ_Record R)
 | N_Obj : forall Av D G fs R Rt,
     nfield_typing (bg Av G (typ_Record R)) D G fs R -> meths_shared (row_tail_with R Rt) fs R ->
     ntyping Av D G (e_rec fs) (typ_Record R)
 | N_Proj : forall Av D G e l T R,
     ntyping (bg Av G T `union` ats (typ_Record (row_Ext l T R))) D G e (typ_Record (row_Ext l T R)) ->
     ntyping Av D G (e_proj e l) T
 | N_ConvD : forall Av D G e T T',
     ntyping (bg Av G T' `union` ats T) D G e T -> teqD D T T' -> ntyping Av D G e T'
 | N_Unit : forall Av D G, uniq G -> ntyping Av D G e_unit typ_Unit
 | N_Str : forall Av D G q, uniq G -> ntyping Av D G (e_str q) typ_String
 | N_If : forall Av D G e1 e2 e3 T,
     ntyping (bg Av G T) D G e1 typ_Bool -> ntyping (bg Av G T) D G e2 T ->
     ntyping (bg Av G T) D G e3 T ->
     ntyping Av D G (e_ite e1 e2 e3) T
 | N_ToFloat : forall Av D G e A,
     ntyping (bg Av G typ_Float `union` ats A) D G e A -> sat D k_Literal A ->
     ntyping Av D G (e_tofloat e) typ_Float
 | N_Bin : forall Av D G e1 o e2 A B R,
     ntyping (bg Av G R `union` ats A `union` ats B) D G e1 A ->
     ntyping (bg Av G R `union` ats A `union` ats B) D G e2 B -> bin_sig D o A B R ->
     ntyping Av D G (e_bin e1 o e2) R
 | N_Spread : forall Av D G e1 l e2 P T R,
     ntyping (bg Av G (typ_Record (row_Ext l T R)) `union` ats (typ_Record (row_Maybe l P T R)))
       D G e1 (typ_Record (row_Maybe l P T R)) ->
     ntyping (bg Av G (typ_Record (row_Ext l T R)) `union` ats (typ_Record (row_Maybe l P T R)))
       D G e2 T ->
     ntyping Av D G (e_spread e1 l e2) (typ_Record (row_Ext l T R))
 | N_SpreadL : forall Av D G e1 l e2 T R,
     ntyping (bg Av G (typ_Record (row_Ext l T R)) `union` ats (typ_Record R)) D G e1 (typ_Record R) ->
     rlacksD D l R = true ->
     ntyping (bg Av G (typ_Record (row_Ext l T R)) `union` ats (typ_Record R)) D G e2 T ->
     ntyping Av D G (e_spread e1 l e2) (typ_Record (row_Ext l T R))
 | N_Restrict : forall Av D G e l R0 T R,
     ntyping (bg Av G (typ_Record R) `union` ats (typ_Record R0)) D G e (typ_Record R0) -> rm l R0 T R ->
     ntyping Av D G (e_restrict e l) (typ_Record R)
 | N_Fold : forall Av D G e Bd,
     lct 0 (typ_Mu Bd) -> guarded Bd ->
     ntyping (bg Av G (typ_Mu Bd) `union` ats (open_typ 0 (typ_Mu Bd) Bd)) D G e (open_typ 0 (typ_Mu Bd) Bd) ->
     ntyping Av D G (e_fold e) (typ_Mu Bd)
 | N_Unfold : forall Av D G e Bd,
     lct 0 (typ_Mu Bd) -> guarded Bd ->
     ntyping (bg Av G (open_typ 0 (typ_Mu Bd) Bd) `union` ats (typ_Mu Bd)) D G e (typ_Mu Bd) ->
     ntyping Av D G (e_unfold e) (open_typ 0 (typ_Mu Bd) Bd)
 | N_Con : forall Av D G w tg e Ts,
     tg < length (gtags w) ->
     ntyping (bg Av G (typ_Grp w (spine Ts)) `union` ats (tag_payload w Ts tg)) D G e (tag_payload w Ts tg) ->
     ntyping Av D G (e_con w tg e) (typ_Grp w (spine Ts))
 | N_Match : forall (L : vars) Av D G w Ts e ars T,
     ntyping (bg Av G T `union` ats (typ_Grp w (spine Ts))) D G e (typ_Grp w (spine Ts)) ->
     arms_wf w ars ->
     (forall tg body, arms_find tg ars = Some body ->
        forall x, x `notin` L ->
          ntyping (bg Av G T `union` ats (typ_Grp w (spine Ts))) D ((x ~ sch_mono (tag_payload w Ts tg)) ++ G)
            (open_exp_wrt_exp body (e_fvar_f x)) T) ->
     (forall e0, arms_default ars = Some e0 ->
        ntyping (bg Av G T `union` ats (typ_Grp w (spine Ts))) D G e0 T) ->
     ntyping Av D G (e_match w e ars) T
with nfield_typing : atoms -> denv -> ctx -> fields -> row -> Prop :=
 | NF_nil : forall Av D G, uniq G -> nfield_typing Av D G fs_nil row_Empty
 | NF_cons : forall Av D G l e T fs R,
     ntyping (bg Av G (typ_Record (row_Ext l T R))) D G e T ->
     nfield_typing (bg Av G (typ_Record (row_Ext l T R))) D G fs R ->
     nfield_typing Av D G (fs_cons l e fs) (row_Ext l T R)
 | NF_meth : forall Av D G l e T fs R,
     ntyping (bg Av G (typ_Record (row_Ext l T R))) D G e T ->
     nfield_typing (bg Av G (typ_Record (row_Ext l T R))) D G fs R ->
     nfield_typing Av D G (fs_meth l e fs) (row_Ext l T R).

Scheme ntyping_mut := Induction for ntyping Sort Prop
with nfield_typing_mut := Induction for nfield_typing Sort Prop.
Combined Scheme ntyping_field_mutind from ntyping_mut, nfield_typing_mut.

(* The normal form is a derivation of [typing]. *)
Lemma ntyping_typing :
  (forall Av D G e T, ntyping Av D G e T -> typing D G e T) /\
  (forall Av D G fs R, nfield_typing Av D G fs R -> field_typing D G fs R).
Proof.
  apply ntyping_field_mutind.
  - intros Av D G x s T Hu Hb Hi. eapply T_Var; eassumption.
  - intros Av D G n T Hu Hs. apply T_Num; assumption.
  - intros Av D G d Hu. apply T_Dec; assumption.
  - intros Av D G Hu. apply T_True; assumption.
  - intros Av D G Hu. apply T_False; assumption.
  - intros L Av D G e T1 T2 Hb IH. apply T_Abs with (L := L). exact IH.
  - intros Av D G e1 e2 T1 T2 H1 IH1 H2 IH2. eapply T_App; eassumption.
  - intros L Av D G e1 e2 T1 T2 k rk Tm Hgv Hlp Hev Hevr Hp IHp Hb IHb.
    apply T_Let with (L := L) (T1 := T1) (k := k) (rk := rk) (Tm := Tm); assumption.
  - intros L Av D G e1 e2 T1 T2 H1 IH1 Hb IHb.
    apply T_LetMono with (L := L) (T1 := T1); assumption.
  - intros L Av D G fs e2 R T k rk Hfg Hev Hevr Hf IHf Hb IHb.
    apply T_Letrec with (L := L) (R := R) (k := k) (rk := rk); assumption.
  - intros Av D G fs R Hf IH Hnm. apply T_Record; assumption.
  - intros Av D G fs R Rt Hf IH Hms. apply T_Obj with (Rt := Rt); assumption.
  - intros Av D G e l T R H IH. eapply T_Proj; eassumption.
  - intros Av D G e T T' H IH Ht. eapply T_ConvD; eassumption.
  - intros Av D G Hu. apply T_Unit; assumption.
  - intros Av D G q Hu. apply T_Str; assumption.
  - intros Av D G e1 e2 e3 T H1 IH1 H2 IH2 H3 IH3. apply T_If; assumption.
  - intros Av D G e A H IH Hs. eapply T_ToFloat; eassumption.
  - intros Av D G e1 o e2 A B R H1 IH1 H2 IH2 Hs. eapply T_Bin; eassumption.
  - intros Av D G e1 l e2 P T R H1 IH1 H2 IH2. eapply T_Spread; eassumption.
  - intros Av D G e1 l e2 T R H1 IH1 Hl H2 IH2. apply T_SpreadL; assumption.
  - intros Av D G e l R0 T R H IH Hr. eapply T_Restrict; eassumption.
  - intros Av D G e Bd Hl Hg H IH. apply T_Fold; assumption.
  - intros Av D G e Bd Hl Hg H IH. apply T_Unfold; assumption.
  - intros Av D G w tg e Ts Ht H IH. apply T_Con; assumption.
  - intros L Av D G w Ts e ars T H IH Hwf Ha IHa Hd IHd.
    apply T_Match with (L := L) (w := w) (Ts := Ts); assumption.
  - intros Av D G Hu. apply FT_nil; assumption.
  - intros Av D G l e T fs R H IH Hf IHf. apply FT_cons; assumption.
  - intros Av D G l e T fs R H IH Hf IHf. apply FT_meth; assumption.
Qed.

(* ---- every derivation has a normal form ---- *)

Lemma esz_pos : forall e, 0 < esz e.
Proof. intros e. destruct e; simpl; lia. Qed.

Definition NfBound (n : nat) : Prop :=
  (forall e, esz e < n -> forall D G T, typing D G e T -> forall Sd, supp_ok D Sd ->
     forall Av, ntyping Av D G e T) /\
  (forall fs, fsz fs < n -> forall D G R, field_typing D G fs R -> forall Sd, supp_ok D Sd ->
     forall Av, nfield_typing Av D G fs R).

Lemma NfBound_step : forall n, NfBound n -> NfBound (Datatypes.S n).
Proof.
  intros n [IHe IHf].
  assert (Hmut :
    (forall D G e T, typing D G e T -> esz e < Datatypes.S n -> forall Sd, supp_ok D Sd ->
       forall Av, ntyping Av D G e T) /\
    (forall D G fs R, field_typing D G fs R -> fsz fs < Datatypes.S n -> forall Sd, supp_ok D Sd ->
       forall Av, nfield_typing Av D G fs R)).
  { apply typing_field_mutind.
    - intros D G x s T Hu Hb Hi Hsz Sd HS Av. eapply N_Var; eassumption.
    - intros D G i T Hu Hs Hsz Sd HS Av. apply N_Num; assumption.
    - intros D G d Hu Hsz Sd HS Av. apply N_Dec; assumption.
    - intros D G Hu Hsz Sd HS Av. apply N_True; assumption.
    - intros D G Hu Hsz Sd HS Av. apply N_False; assumption.
    - intros L D G e T1 T2 Hb IH Hsz Sd HS Av. simpl in Hsz.
      apply N_Abs with (L := L). intros x Hx.
      apply (IH x Hx ltac:(rewrite esz_open; lia) Sd HS).
    - intros D G e1 e2 T1 T2 H1 IH1 H2 IH2 Hsz Sd HS Av. simpl in Hsz.
      apply N_App with (T1 := T1).
      + apply (IH1 ltac:(lia) Sd HS).
      + apply (IH2 ltac:(lia) Sd HS).
    - intros L D G e1 e2 T1 T2 k rk Tm Hgv Hlp Hty1 IH1 Hb IHb Hsz Sd HS Av. simpl in Hsz.
      destruct (typing_let_even L D G e1 e2 T1 T2 k rk Tm Sd (bg Av G T2) HS
                  (typing_uniq _ _ _ _ Hty1) Hlp Hty1 Hb)
        as (L' & T1' & k' & rk' & Hlp' & Hty1' & Hb' & Hev & Hevr).
      apply N_Let with (L := L') (T1 := T1') (k := k') (rk := rk') (Tm := Tm); try assumption.
      + apply (IHe e1 ltac:(lia) _ _ _ Hty1' _ (supp_ok_ext2 _ _ _ _ _ _ HS)).
      + intros x Hx. apply (IHe (open_exp_wrt_exp e2 (e_fvar_f x)) ltac:(rewrite esz_open; lia) _ _ _ (Hb' x Hx) Sd HS).
    - intros L D G e1 e2 T1 T2 H1 IH1 Hb IHb Hsz Sd HS Av. simpl in Hsz.
      apply N_LetMono with (L := L) (T1 := T1).
      + apply (IH1 ltac:(lia) Sd HS).
      + intros x Hx. apply (IHb x Hx ltac:(rewrite esz_open; lia) Sd HS).
    - intros L D G fs e2 R T k rk Hfg Hf IHf' Hb IHb Hsz Sd HS Av. simpl in Hsz.
      pick fresh p for L.
      pose proof (typing_uniq _ _ _ _ (Hb p Fr)) as Hu'. apply uniq_app_2 in Hu'.
      destruct (typing_letrec_even L D G fs e2 R T k rk Sd (bg Av G T) HS Hu' Hf Hb)
        as (L' & R' & k' & rk' & Hf' & Hb' & Hev & Hevr).
      apply N_Letrec with (L := L') (R := R') (k := k') (rk := rk'); try assumption.
      + intros q Hq. apply (IHf (open_fields_wrt_exp fs (e_fvar_f q)) ltac:(rewrite fsz_open; lia) _ _ _ (Hf' q Hq) _ (supp_ok_ext2 _ _ _ _ _ _ HS)).
      + intros q Hq. apply (IHe (open_exp_wrt_exp e2 (e_fvar_f q)) ltac:(rewrite esz_open; lia) _ _ _ (Hb' q Hq) Sd HS).
    - intros D G fs R Hf IH Hnm Hsz Sd HS Av. simpl in Hsz.
      apply N_Record; [ | exact Hnm ]. apply (IH ltac:(lia) Sd HS).
    - intros D G fs R Rt Hf IH Hms Hsz Sd HS Av. simpl in Hsz.
      apply N_Obj with (Rt := Rt); [ | exact Hms ]. apply (IH ltac:(lia) Sd HS).
    - intros D G e l T R H IH Hsz Sd HS Av. simpl in Hsz.
      apply N_Proj with (R := R). apply (IH ltac:(lia) Sd HS).
    - intros D G e T T' H IH Ht Hsz Sd HS Av.
      apply N_ConvD with (T := T); [ apply (IH Hsz Sd HS) | exact Ht ].
    - intros D G Hu Hsz Sd HS Av. apply N_Unit; assumption.
    - intros D G q Hu Hsz Sd HS Av. apply N_Str; assumption.
    - intros D G e1 e2 e3 T H1 IH1 H2 IH2 H3 IH3 Hsz Sd HS Av. simpl in Hsz.
      apply N_If.
      + apply (IH1 ltac:(lia) Sd HS).
      + apply (IH2 ltac:(lia) Sd HS).
      + apply (IH3 ltac:(lia) Sd HS).
    - intros D G e A H IH Hs Hsz Sd HS Av. simpl in Hsz.
      apply N_ToFloat with (A := A); [ | exact Hs ]. apply (IH ltac:(lia) Sd HS).
    - intros D G e1 o e2 A B R H1 IH1 H2 IH2 Hs Hsz Sd HS Av. simpl in Hsz.
      apply N_Bin with (A := A) (B := B); [ | | exact Hs ].
      + apply (IH1 ltac:(lia) Sd HS).
      + apply (IH2 ltac:(lia) Sd HS).
    - intros D G e1 l e2 P T R H1 IH1 H2 IH2 Hsz Sd HS Av. simpl in Hsz.
      apply N_Spread with (P := P).
      + apply (IH1 ltac:(lia) Sd HS).
      + apply (IH2 ltac:(lia) Sd HS).
    - intros D G e1 l e2 T R H1 IH1 Hl H2 IH2 Hsz Sd HS Av. simpl in Hsz.
      apply N_SpreadL; [ | exact Hl | ].
      + apply (IH1 ltac:(lia) Sd HS).
      + apply (IH2 ltac:(lia) Sd HS).
    - intros D G e l R0 T R H IH Hr Hsz Sd HS Av. simpl in Hsz.
      apply N_Restrict with (R0 := R0) (T := T); [ | exact Hr ]. apply (IH ltac:(lia) Sd HS).
    - intros D G e Bd Hl Hg H IH Hsz Sd HS Av. simpl in Hsz.
      apply N_Fold; [ exact Hl | exact Hg | ]. apply (IH ltac:(lia) Sd HS).
    - intros D G e Bd Hl Hg H IH Hsz Sd HS Av. simpl in Hsz.
      apply N_Unfold; [ exact Hl | exact Hg | ]. apply (IH ltac:(lia) Sd HS).
    - intros D G w tg e Ts Ht H IH Hsz Sd HS Av. simpl in Hsz.
      apply N_Con; [ exact Ht | ]. apply (IH ltac:(lia) Sd HS).
    - intros L D G w Ts e ars T H IH Hwf Ha IHa Hd IHd Hsz Sd HS Av. simpl in Hsz.
      apply N_Match with (L := L) (w := w) (Ts := Ts).
      + apply (IH ltac:(lia) Sd HS).
      + exact Hwf.
      + intros tg body Hf x Hx. pose proof (arms_find_sz _ _ _ Hf) as Hs.
        apply (IHa tg body Hf x Hx ltac:(rewrite esz_open; lia) Sd HS).
      + intros e0 Hd0. pose proof (arms_default_sz _ _ Hd0) as Hs.
        apply (IHd e0 Hd0 ltac:(lia) Sd HS).
    - intros D G Hu Hsz Sd HS Av. apply NF_nil; assumption.
    - intros D G l e T fs R H IH Hf IHf' Hsz Sd HS Av. simpl in Hsz.
      apply NF_cons.
      + apply (IH ltac:(lia) Sd HS).
      + apply (IHf' ltac:(lia) Sd HS).
    - intros D G l e T fs R H IH Hf IHf' Hsz Sd HS Av. simpl in Hsz.
      apply NF_meth.
      + apply (IH ltac:(lia) Sd HS).
      + apply (IHf' ltac:(lia) Sd HS). }
  destruct Hmut as [Hm1 Hm2]. split.
  - intros e Hsz D G T Hty Sd HS Av. exact (Hm1 D G e T Hty Hsz Sd HS Av).
  - intros fs Hsz D G R Hty Sd HS Av. exact (Hm2 D G fs R Hty Hsz Sd HS Av).
Qed.

Lemma NfBound_all : forall n, NfBound n.
Proof.
  induction n as [|n IH]; [ | exact (NfBound_step n IH) ].
  split; intros; lia.
Qed.

(* Every derivation over an environment of finite support has a normal form at
   the same judgement, whatever the atoms to avoid. *)
Theorem typing_normal : forall D G e T, typing D G e T ->
  forall Sd, supp_ok D Sd -> forall Av, ntyping Av D G e T.
Proof.
  intros D G e T H Sd HS Av.
  exact (proj1 (NfBound_all (Datatypes.S (esz e))) e (Nat.lt_succ_diag_r _) D G T H Sd HS Av).
Qed.

Theorem typing_normal_fields : forall D G fs R, field_typing D G fs R ->
  forall Sd, supp_ok D Sd -> forall Av, nfield_typing Av D G fs R.
Proof.
  intros D G fs R H Sd HS Av.
  exact (proj2 (NfBound_all (Datatypes.S (fsz fs))) fs (Nat.lt_succ_diag_r _) D G R H Sd HS Av).
Qed.
