(* Sorts in algorithm W (GoatInfer.v): the invariant on the kinding
   environment the algorithm threads, and what [upd], [inst_den] and [gen_sk]
   do to it.  A fresh variable is the only thing that gets a sort, so the
   environment always has [Any] on the atoms the algorithm has not used. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatDefs.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Stdlib.Lists.List.
From Stdlib Require Import Lia.
Import ListNotations.

Lemma aset_in : forall a l, a `in` aset l <-> In a l.
Proof.
  intros a l. induction l as [|b l IH]; simpl.
  - split; [ fsetdec | intros [] ].
  - rewrite AtomSetFacts.add_iff, IH. split.
    + intros [H|H]; [left; auto | right; auto].
    + intros [H|H]; [left; auto | right; auto].
Qed.

(* ------------------------------------------------------------------ *)
(* The environment is Any beyond the first n even atoms                 *)
(* ------------------------------------------------------------------ *)

Definition DOk (D : denv) (n : nat) : Prop :=
  forall a, (forall m, m < n -> a <> ea m) -> D a = k_Any.

Lemma ea_inj : forall m n, ea m = ea n -> m = n.
Proof.
  intros m n H. unfold ea in H. apply idx_atom_inj in H. lia.
Qed.

Lemma DOk_mono : forall D n n', DOk D n -> n <= n' -> DOk D n'.
Proof.
  intros D n n' H Hle a Ha. apply H. intros m Hm. apply Ha. lia.
Qed.

Lemma DOk_ea : forall D n m, DOk D n -> n <= m -> D (ea m) = k_Any.
Proof.
  intros D n m H Hle. apply H. intros m' Hm' Heq. apply ea_inj in Heq. lia.
Qed.

Lemma DOk_odd : forall D n a, DOk D n -> od a -> D a = k_Any.
Proof.
  intros D n a H Ho. apply H. intros m Hm Heq. subst. exact (ev_od _ (ev_ea m) Ho).
Qed.

Lemma d_any_DOk : forall n, DOk d_any n.
Proof. intros n a _. reflexivity. Qed.

Lemma DOk_supp : forall D n, DOk D n -> exists S, supp_ok D S.
Proof.
  intros D n H. exists (aset (List.map ea (seq 0 n))).
  intros a Ha. apply H. intros m Hm Heq. apply Ha. apply aset_in.
  subst. apply in_map_iff. exists m. split; [reflexivity | apply in_seq; lia].
Qed.

Lemma upd_same : forall D a k, upd D a k a = k.
Proof. intros. unfold upd. destruct (Atom.eq_dec a a); [reflexivity | contradiction]. Qed.

Lemma upd_other : forall D a k b, b <> a -> upd D a k b = D b.
Proof. intros. unfold upd. destruct (Atom.eq_dec b a); [contradiction | reflexivity]. Qed.

Lemma DOk_upd : forall D n k, DOk D n -> DOk (upd D (ea n) k) (S n).
Proof.
  intros D n k H a Ha. rewrite upd_other.
  - apply H. intros m Hm. apply Ha. lia.
  - apply Ha. lia.
Qed.

(* A refinement of the environment is the identity substitution respecting it. *)
Lemma kres_upd : forall D n k, DOk D n -> kres D (upd D (ea n) k) idt.
Proof.
  intros D n k H a. unfold idt. simpl.
  destruct (Atom.eq_dec a (ea n)) as [->|Hne].
  - rewrite (DOk_ea D n n H (le_n n)). apply finer_any.
  - rewrite upd_other by exact Hne. apply finer_refl.
Qed.

Lemma kres_sid : forall D, kres D D (sT sid).
Proof. intros D. apply kres_id. Qed.

Lemma kres_scomp : forall D D' D'' s1 s2,
  kres D D' (sT s1) -> kres D' D'' (sT s2) -> kres D D'' (sT (scomp s2 s1)).
Proof.
  intros D D' D'' s1 s2 H1 H2 a. unfold scomp, tcomp. simpl.
  apply (sat_ap D' D'' (D a) (sT s1 a) (sT s2) (sR s2) H2). apply H1.
Qed.

Lemma kres_idt_trans : forall D D' D'',
  kres D D' idt -> kres D' D'' idt -> kres D D'' idt.
Proof.
  intros D D' D'' H1 H2. pose proof (kres_scomp D D' D'' sid sid H1 H2) as H.
  intros a. specialize (H a). exact H.
Qed.

(* A refinement of the environment on either side keeps a substitution's
   respect. *)
Lemma kres_refine_l : forall D0 D D' st,
  kres D0 D idt -> kres D D' st -> kres D0 D' st.
Proof.
  intros D0 D D' st H0 H a.
  pose proof (H0 a) as Ha. unfold idt in Ha. simpl in Ha.
  apply (sat_finer D' (D0 a) (D a) (st a)); [ exact Ha | apply H ].
Qed.

Lemma kres_refine_r : forall D D' D'' st,
  kres D D' st -> kres D' D'' idt -> kres D D'' st.
Proof.
  intros D D' D'' st H H1 a.
  pose proof (sat_ap D' D'' (D a) (st a) idt idr H1 (H a)) as Hs.
  assert (Heq : ap_typ idt idr (st a) = st a)
    by (apply ap_typ_pointwise_id; reflexivity).
  rewrite Heq in Hs. exact Hs.
Qed.

(* ------------------------------------------------------------------ *)
(* Extension of the environment on a set of atoms                       *)
(* ------------------------------------------------------------------ *)

Lemma ext_in : forall D V k a, a `in` V -> ext D V k a = k a.
Proof.
  intros D V k a H. unfold ext. rewrite (proj1 (AtomSetFacts.mem_iff _ _) H). reflexivity.
Qed.

Lemma ext_out : forall D V k a, a `notin` V -> ext D V k a = D a.
Proof.
  intros D V k a H. unfold ext.
  destruct (AtomSetImpl.mem a V) eqn:E; [ | reflexivity ].
  apply AtomSetFacts.mem_iff in E. contradiction.
Qed.

Lemma sat_ext_out : forall D V k0 k T,
  sat D k T -> (forall b, T = typ_Var b -> b `notin` V) -> sat (ext D V k0) k T.
Proof.
  intros D V k0 k T H Hout. destruct T; simpl in *; try exact H.
  rewrite ext_out; [ exact H | apply Hout; reflexivity ].
Qed.

Lemma supp_ok_ext_set : forall D S V k,
  supp_ok D S -> supp_ok (ext D V k) (S `union` V).
Proof.
  intros D S V k HS a Ha. rewrite ext_out by fsetdec. apply HS. fsetdec.
Qed.

(* ------------------------------------------------------------------ *)
(* Instantiation                                                        *)
(* ------------------------------------------------------------------ *)

Lemma idx_lt : forall a l, In a l -> idx a l < length l.
Proof.
  intros a l. induction l as [|b l IH]; intros H; [ inversion H | ]. simpl.
  destruct (Atom.eq_dec a b) as [->|Hne]; [ lia | ].
  destruct H as [H|H]; [ congruence | ]. specialize (IH H). lia.
Qed.

Lemma idx_inj : forall a b l, In a l -> In b l -> idx a l = idx b l -> a = b.
Proof.
  intros a b l. induction l as [|c l IH]; intros Ha Hb H; [ inversion Ha | ]. simpl in H.
  destruct (Atom.eq_dec a c) as [->|Hac]; destruct (Atom.eq_dec b c) as [->|Hbc].
  - reflexivity.
  - discriminate.
  - discriminate.
  - destruct Ha as [Ha|Ha]; [ congruence | ]. destruct Hb as [Hb|Hb]; [ congruence | ].
    apply IH; [ exact Ha | exact Hb | lia ].
Qed.

Lemma key_dec : forall (key : atom -> atom) (b : atom) (l : list atom),
  {a | In a l /\ b = key a} + {forall a, In a l -> b <> key a}.
Proof.
  intros key b l. induction l as [|c l IH].
  - right. intros a Ha. inversion Ha.
  - destruct (Atom.eq_dec b (key c)) as [Heq|Hne].
    + left. exists c. split; [ left; reflexivity | exact Heq ].
    + destruct IH as [[a [Ha Hb]]|IH].
      * left. exists a. split; [ right; exact Ha | exact Hb ].
      * right. intros a [Ha|Ha]; [ subst; exact Hne | apply IH; exact Ha ].
Defined.

Lemma sel_out : forall (key : atom -> atom) (val : atom -> sort) b d l,
  (forall a, In a l -> b <> key a) ->
  fold_right (fun a acc => if Atom.eq_dec b (key a) then val a else acc) d l = d.
Proof.
  intros key val b d l H. induction l as [|a l IH]; [ reflexivity | ]. simpl.
  destruct (Atom.eq_dec b (key a)) as [Heq|Hne].
  - exfalso. exact (H a (or_introl eq_refl) Heq).
  - apply IH. intros a' Ha'. apply H. right. exact Ha'.
Qed.

Lemma sel_at : forall (key : atom -> atom) (val : atom -> sort) b d l a,
  In a l -> b = key a ->
  (forall a', In a' l -> key a' = key a -> val a' = val a) ->
  fold_right (fun a acc => if Atom.eq_dec b (key a) then val a else acc) d l = val a.
Proof.
  intros key val b d l a Ha Hb Hinj. induction l as [|c l IH]; [ inversion Ha | ]. simpl.
  destruct (Atom.eq_dec b (key c)) as [Heq|Hne].
  - apply Hinj; [ left; reflexivity | congruence ].
  - destruct Ha as [Ha|Ha].
    + subst c. exfalso. apply Hne. exact Hb.
    + apply IH; [ exact Ha | intros a' Ha' H'; apply Hinj; [ right; exact Ha' | exact H' ] ].
Qed.

Section InstDen.
Variables (D : denv) (s : scheme) (n : nat).
Let lq := AtomSetImpl.elements (s_tq s).
Let key (a : atom) := ea (n + idx a lq).

Lemma inst_den_out : forall b,
  (forall a, In a lq -> b <> ea (n + idx a lq)) -> inst_den D s n b = D b.
Proof. intros b H. unfold inst_den. fold lq. apply (sel_out key (s_sk s) b (D b) lq H). Qed.

Lemma inst_den_at : forall a, In a lq -> inst_den D s n (ea (n + idx a lq)) = s_sk s a.
Proof.
  intros a Ha. unfold inst_den. fold lq.
  apply (sel_at key (s_sk s) (ea (n + idx a lq)) (D (ea (n + idx a lq))) lq a Ha eq_refl).
  intros a' Ha' Hk. unfold key in Hk. apply ea_inj in Hk.
  assert (idx a' lq = idx a lq) by lia. rewrite (idx_inj a' a lq Ha' Ha H). reflexivity.
Qed.

Lemma DOk_inst_den : DOk D n ->
  DOk (inst_den D s n) (n + length lq + length (AtomSetImpl.elements (s_rq s))).
Proof.
  intros H b Hb. rewrite inst_den_out.
  - apply H. intros m Hm. apply Hb. lia.
  - intros a Ha Heq. apply (Hb (n + idx a lq)); [ | exact Heq ].
    pose proof (idx_lt a lq Ha). lia.
Qed.

Lemma kres_inst_den : DOk D n -> kres D (inst_den D s n) idt.
Proof.
  intros H b. unfold idt. simpl.
  destruct (key_dec key b lq) as [[a [Ha Hb]]|Hn].
  - rewrite Hb. unfold key. rewrite (DOk_ea D n _ H) by lia. apply finer_any.
  - rewrite inst_den_out by exact Hn. apply finer_refl.
Qed.

End InstDen.

(* ------------------------------------------------------------------ *)
(* The sorts of a generalization                                        *)
(* ------------------------------------------------------------------ *)

Lemma gen_sk_at : forall D la a, In a la ->
  gen_sk D la (oa (idx a la)) = D a.
Proof.
  intros D la a Ha. unfold gen_sk.
  apply (sel_at (fun a => oa (idx a la)) D (oa (idx a la)) k_Any la a Ha eq_refl).
  intros a' Ha' Hk. apply idx_atom_inj in Hk.
  assert (idx a' la = idx a la) by lia. rewrite (idx_inj a' a la Ha' Ha H). reflexivity.
Qed.

(* A substitution that fixes the context's variables, applied between two
   environments it respects. *)
Lemma typing_tsubst_fix_k : forall D D' S S' G e T st sr A,
  typing D G e T -> supp_ok D S -> supp_ok D' S' -> kres D D' st -> tr_supp st sr A ->
  (forall a, a `in` ftv_ctx G -> st a = typ_Var a) ->
  (forall r, r `in` frv_ctx G -> sr r = row_Var r) ->
  typing D' G e (ap_typ st sr T).
Proof.
  intros D D' S S' G e T st sr A Hty HS HS' Hk Hsupp Hfa Hfr.
  apply (proj1 typing_tsubst_gen_mut D G e T Hty st sr G D' A S S').
  - eapply typing_uniq; exact Hty.
  - exact HS.
  - exact HS'.
  - exact Hk.
  - apply ctx_subst_fix; assumption.
  - exact Hsupp.
  - unfold tr_compat. repeat split.
    + intros a Ha. rewrite (Hfa a Ha). simpl. fsetdec.
    + intros a Ha. rewrite (Hfa a Ha). simpl. fsetdec.
    + intros r Hr. rewrite (Hfr r Hr). simpl. fsetdec.
    + intros r Hr. rewrite (Hfr r Hr). simpl. fsetdec.
Qed.

(* ------------------------------------------------------------------ *)
(* The boolean tests of the algorithm                                   *)
(* ------------------------------------------------------------------ *)

Lemma finer_b_sound : forall k1 k2, finer_b k1 k2 = true -> finer k1 k2.
Proof. intros [] []; simpl; intros H; try discriminate; constructor. Qed.

Lemma finer_b_total : forall k1 k2, finer_b k1 k2 = false -> finer k2 k1.
Proof. intros [] []; simpl; intros H; try discriminate; constructor. Qed.

Lemma sat_b_sound : forall D k T, sat_b D k T = true -> sat D k T.
Proof.
  intros D k T H. destruct T; simpl in *; try exact I.
  1-5: destruct k; [ reflexivity | discriminate | discriminate ].
  apply finer_b_sound. exact H.
Qed.

Lemma is_literal_sound : forall D T,
  is_literal D T = true -> exists a, T = typ_Var a /\ D a = k_Literal.
Proof.
  intros D T H. destruct T; simpl in H; try discriminate.
  destruct (D a) eqn:E; try discriminate. exists a. split; [ reflexivity | exact E ].
Qed.
