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

Lemma ea_inj : forall m n, ea m = ea n -> m = n.
Proof.
  intros m n H. unfold ea in H. apply idx_atom_inj in H. lia.
Qed.

(* Beyond the first [n] even atoms, a type variable has sort [Any] and a row
   variable has the kind [rk_any]: only a fresh variable gets either. *)
Definition DOk (D : denv) (n : nat) : Prop :=
  (forall a, (forall m, m < n -> a <> ea m) -> D a = k_Any) /\
  (forall a, (forall m, m < n -> a <> ea m) -> drk D a = rk_any).

Lemma DOk_mono : forall D n n', DOk D n -> n <= n' -> DOk D n'.
Proof.
  intros D n n' [H Hr] Hle. split; intros a Ha; [ apply H | apply Hr ]; intros m Hm; apply Ha; lia.
Qed.

Lemma DOk_ea : forall D n m, DOk D n -> n <= m -> D (ea m) = k_Any.
Proof.
  intros D n m [H _] Hle. apply H. intros m' Hm' Heq. apply ea_inj in Heq. lia.
Qed.

Lemma DOk_rea : forall D n m, DOk D n -> n <= m -> drk D (ea m) = rk_any.
Proof.
  intros D n m [_ H] Hle. apply H. intros m' Hm' Heq. apply ea_inj in Heq. lia.
Qed.

Lemma DOk_odd : forall D n a, DOk D n -> od a -> D a = k_Any.
Proof.
  intros D n a [H _] Ho. apply H. intros m Hm Heq. subst. exact (ev_od _ (ev_ea m) Ho).
Qed.

Lemma DOk_rodd : forall D n a, DOk D n -> od a -> drk D a = rk_any.
Proof.
  intros D n a [_ H] Ho. apply H. intros m Hm Heq. subst. exact (ev_od _ (ev_ea m) Ho).
Qed.

Lemma d_any_DOk : forall n, DOk d_any n.
Proof. intros n. split; intros a _; reflexivity. Qed.

Lemma DOk_supp : forall D n, DOk D n -> exists S, supp_ok D S.
Proof.
  intros D n [H Hr]. exists (aset (List.map ea (seq 0 n))).
  assert (Hin : forall a, a `notin` aset (List.map ea (seq 0 n)) -> forall m, m < n -> a <> ea m).
  { intros a Ha m Hm Heq. apply Ha. apply aset_in. subst. apply in_map_iff.
    exists m. split; [reflexivity | apply in_seq; lia]. }
  intros a Ha. split; [ apply H | apply Hr ]; apply Hin; exact Ha.
Qed.

Lemma upd_same : forall D a k, upd D a k a = k.
Proof. intros. unfold upd. simpl. destruct (Atom.eq_dec a a); [reflexivity | contradiction]. Qed.

Lemma upd_other : forall D a k b, b <> a -> upd D a k b = D b.
Proof. intros. unfold upd. simpl. destruct (Atom.eq_dec b a); [contradiction | reflexivity]. Qed.

Lemma rupd_same : forall D a K, drk (rupd D a K) a = K.
Proof. intros. unfold rupd. simpl. destruct (Atom.eq_dec a a); [reflexivity | contradiction]. Qed.

Lemma rupd_other : forall D a K b, b <> a -> drk (rupd D a K) b = drk D b.
Proof. intros. unfold rupd. simpl. destruct (Atom.eq_dec b a); [contradiction | reflexivity]. Qed.

Lemma DOk_upd : forall D n k, DOk D n -> DOk (upd D (ea n) k) (S n).
Proof.
  intros D n k [H Hr]. split.
  - intros a Ha. rewrite upd_other.
    + apply H. intros m Hm. apply Ha. lia.
    + apply Ha. lia.
  - intros r Hr'. cbn [drk upd]. apply Hr. intros m Hm. apply Hr'. lia.
Qed.

Lemma DOk_rupd : forall D n K, DOk D n -> DOk (rupd D (ea n) K) (S n).
Proof.
  intros D n K [H Hr]. split; [ intros a Ha; apply H; intros m Hm; apply Ha; lia | ].
  intros a Ha. rewrite rupd_other.
  - apply Hr. intros m Hm. apply Ha. lia.
  - apply Ha. lia.
Qed.

(* A substitution respects the kinds of two environments when it respects the
   sorts of its type variables and the kinds of its row variables. *)
Definition KR (D D' : denv) (s : sub) : Prop := kres D D' (sT s) /\ rkres D D' (sR s).

Lemma KR_id : forall D, KR D D sid.
Proof. intros D. split; [ apply kres_id | intros r; exact (rkok_self D r) ]. Qed.

(* A refinement of the environment is the identity substitution respecting it. *)
Lemma KR_upd : forall D n k, DOk D n -> KR D (upd D (ea n) k) sid.
Proof.
  intros D n k H. split.
  - intros a. cbn [sT sid]. unfold idt. cbn [sat].
    destruct (Atom.eq_dec a (ea n)) as [->|Hne].
    + rewrite (DOk_ea D n n H (le_n n)). apply finer_any.
    + rewrite upd_other by exact Hne. apply finer_refl.
  - intros r. exact (rkok_self (upd D (ea n) k) r).
Qed.

Lemma KR_rupd : forall D n K, DOk D n -> KR D (rupd D (ea n) K) sid.
Proof.
  intros D n K H. split.
  - intros a. cbn [sT sid]. unfold idt. cbn [sat]. apply finer_refl.
  - intros r. change (sR sid r) with (row_Var r). split.
    + cbn [rsat]. destruct (Atom.eq_dec r (ea n)) as [->|Hne].
      * rewrite (DOk_rea D n n H (le_n n)). apply finer_any.
      * rewrite rupd_other by exact Hne. apply finer_refl.
    + intros l Hl. cbn [rlacksD]. destruct (Atom.eq_dec r (ea n)) as [->|Hne].
      * rewrite (DOk_rea D n n H (le_n n)) in Hl. cbn in Hl. discriminate Hl.
      * rewrite rupd_other by exact Hne. exact Hl.
Qed.

Lemma KR_comp : forall D D' D'' s1 s2,
  KR D D' s1 -> KR D' D'' s2 -> KR D D'' (scomp s2 s1).
Proof.
  intros D D' D'' s1 s2 [H1 Hr1] [H2 Hr2]. split.
  - intros a. unfold scomp, tcomp. simpl.
    apply (sat_ap D' D'' (D a) (sT s1 a) (sT s2) (sR s2) H2 Hr2). apply H1.
  - intros r. unfold scomp, rcomp. simpl.
    apply (rkok_ap D' D'' (sT s2) (sR s2) (drk D r) (sR s1 r) H2 Hr2). apply Hr1.
Qed.

Lemma KR_idl : forall D D' D'' s, KR D D' sid -> KR D' D'' s -> KR D D'' s.
Proof.
  intros D D' D'' s H1 H2. pose proof (KR_comp _ _ _ _ _ H1 H2) as [Hk Hr]. split.
  - intros a. exact (Hk a).
  - intros r. exact (Hr r).
Qed.

Lemma KR_idr : forall D D' D'' s, KR D D' s -> KR D' D'' sid -> KR D D'' s.
Proof.
  intros D D' D'' s H1 H2. pose proof (KR_comp _ _ _ _ _ H1 H2) as [Hk Hr]. split.
  - intros a. specialize (Hk a). unfold scomp, tcomp in Hk. simpl in Hk.
    assert (Heq : ap_typ idt idr (sT s a) = sT s a) by (apply ap_typ_pointwise_id; reflexivity).
    rewrite Heq in Hk. exact Hk.
  - intros r. specialize (Hr r). unfold scomp, rcomp in Hr. simpl in Hr.
    assert (Heq : ap_row idt idr (sR s r) = sR s r)
      by (apply (proj2 ap_pointwise_id_mut); reflexivity).
    rewrite Heq in Hr. exact Hr.
Qed.

(* A step from environment [D] with supply [n] to [D'] with supply [n'],
   applying [s]: [D] is [Any] beyond [n], [s] is a substitution of the
   algorithm, the supply only grows, [D'] refines [D], and [s] respects the
   kinds. *)
Definition Good (D : denv) (n : nat) (s : sub) (D' : denv) (n' : nat) : Prop :=
  DOk D n /\ OkS s /\ DOk D' n' /\ n <= n' /\ KR D D' sid /\ KR D D' s.

Lemma Good_id : forall D n, DOk D n -> Good D n sid D n.
Proof.
  intros D n H.
  exact (conj H (conj OkS_id (conj H (conj (le_n n) (conj (KR_id D) (KR_id D)))))).
Qed.

Lemma Good_comp : forall D n s1 D1 n1 s2 D2 n2,
  Good D n s1 D1 n1 -> Good D1 n1 s2 D2 n2 -> Good D n (scomp s2 s1) D2 n2.
Proof.
  intros D n s1 D1 n1 s2 D2 n2 (Hd & Hs1 & Hd1 & Hl1 & Hi1 & Hk1) (_ & Hs2 & Hd2 & Hl2 & Hi2 & Hk2).
  exact (conj Hd (conj (OkS_comp _ _ Hs2 Hs1) (conj Hd2 (conj (Nat.le_trans _ _ _ Hl1 Hl2)
    (conj (KR_idl _ _ _ _ Hi1 Hi2) (KR_comp _ _ _ _ _ Hk1 Hk2)))))).
Qed.

Lemma Good_unify : forall D n s n',
  OkS s -> KR D D s -> n <= n' -> DOk D n -> Good D n s D n'.
Proof.
  intros D n s n' Hs Hk Hl Hd.
  exact (conj Hd (conj Hs (conj (DOk_mono D n n' Hd Hl) (conj Hl (conj (KR_id D) Hk))))).
Qed.

Lemma Good_lift : forall D n D' n' s D'' n'',
  Good D n sid D' n' -> Good D' n' s D'' n'' -> Good D n s D'' n''.
Proof.
  intros D n D' n' s D'' n'' (Hd & _ & Hd1 & Hl1 & Hi1 & _) (_ & Hs & Hd2 & Hl2 & Hi2 & Hk2).
  exact (conj Hd (conj Hs (conj Hd2 (conj (Nat.le_trans _ _ _ Hl1 Hl2)
    (conj (KR_idl _ _ _ _ Hi1 Hi2) (KR_idl _ _ _ _ Hi1 Hk2)))))).
Qed.

Lemma Good_upd : forall D n k, DOk D n -> Good D n sid (upd D (ea n) k) (S n).
Proof.
  intros D n k H.
  exact (conj H (conj OkS_id (conj (DOk_upd D n k H) (conj (le_S _ _ (le_n n))
    (conj (KR_upd D n k H) (KR_upd D n k H)))))).
Qed.

Lemma Good_rupd : forall D n K, DOk D n -> Good D n sid (rupd D (ea n) K) (S n).
Proof.
  intros D n K H.
  exact (conj H (conj OkS_id (conj (DOk_rupd D n K H) (conj (le_S _ _ (le_n n))
    (conj (KR_rupd D n K H) (KR_rupd D n K H)))))).
Qed.

Lemma Good_pre : forall D n m s D' n',
  n <= m -> DOk D n -> Good D m s D' n' -> Good D n s D' n'.
Proof.
  intros D n m s D' n' Hnm Hd (_ & Hs & Hd' & Hl & Hi & Hk).
  exact (conj Hd (conj Hs (conj Hd' (conj (Nat.le_trans _ _ _ Hnm Hl) (conj Hi Hk))))).
Qed.

Lemma Good_KR : forall D n s D' n', Good D n s D' n' -> KR D D' s.
Proof. intros D n s D' n' (_ & _ & _ & _ & _ & H). exact H. Qed.

Lemma Good_kres : forall D n s D' n', Good D n s D' n' -> kres D D' (sT s).
Proof. intros D n s D' n' H. exact (proj1 (Good_KR _ _ _ _ _ H)). Qed.

Lemma Good_rkres : forall D n s D' n', Good D n s D' n' -> rkres D D' (sR s).
Proof. intros D n s D' n' H. exact (proj2 (Good_KR _ _ _ _ _ H)). Qed.

Lemma Good_dok : forall D n s D' n', Good D n s D' n' -> DOk D' n'.
Proof. intros D n s D' n' (_ & _ & H & _). exact H. Qed.

(* What a unifier promises of its supply and environments: the supply grows,
   and from a well-kept environment the step is [Good].  The unifiers' own
   statements about types need no environment, so the second half is an
   implication. *)
Definition GoodU (D : denv) (n : nat) (s : sub) (D' : denv) (n' : nat) : Prop :=
  n <= n' /\ (DOk D n -> Good D n s D' n').

Lemma GoodU_pre : forall D n m s D' n', DOk D n -> GoodU D m s D' n' -> n <= m -> Good D n s D' n'.
Proof.
  intros D n m s D' n' Hd [_ H] Hnm.
  exact (Good_pre D n m s D' n' Hnm Hd (H (DOk_mono D n m Hd Hnm))).
Qed.

Lemma GoodU_id :forall D n, GoodU D n sid D n.
Proof. intros D n. split; [ lia | exact (Good_id D n) ]. Qed.

Lemma GoodU_same : forall D n s n', OkS s -> KR D D s -> n <= n' -> GoodU D n s D n'.
Proof. intros D n s n' Hs Hk Hl. split; [ exact Hl | intros Hd; exact (Good_unify D n s n' Hs Hk Hl Hd) ]. Qed.

Lemma GoodU_comp : forall D n s1 D1 n1 s2 D2 n2,
  GoodU D n s1 D1 n1 -> GoodU D1 n1 s2 D2 n2 -> GoodU D n (scomp s2 s1) D2 n2.
Proof.
  intros D n s1 D1 n1 s2 D2 n2 [Hl1 H1] [Hl2 H2]. split; [ lia | ].
  intros Hd. pose proof (H1 Hd) as G1.
  exact (Good_comp _ _ _ _ _ _ _ _ G1 (H2 (proj1 (proj2 (proj2 G1))))).
Qed.

Lemma GoodU_rupd : forall D n K, GoodU D n sid (rupd D (ea n) K) (S n).
Proof. intros D n K. split; [ lia | intros H; exact (Good_rupd D n K H) ]. Qed.

(* ------------------------------------------------------------------ *)
(* Extension of the environment on a set of atoms                      *)
(* ------------------------------------------------------------------ *)

Lemma ext_in : forall D V k a, a `in` V -> ext D V k a = k a.
Proof.
  intros D V k a H. unfold ext. simpl. rewrite (proj1 (AtomSetFacts.mem_iff _ _) H). reflexivity.
Qed.

Lemma ext_out : forall D V k a, a `notin` V -> ext D V k a = D a.
Proof.
  intros D V k a H. unfold ext. simpl.
  destruct (AtomSetImpl.mem a V) eqn:E; [ | reflexivity ].
  apply AtomSetFacts.mem_iff in E. contradiction.
Qed.

Lemma sat_ext_out_mut : forall D V k0,
  (forall T, (forall k, sat D k T -> (forall b, b `in` ftv_typ T -> b `notin` V) ->
                sat (ext D V k0) k T) /\
             (forall w j, spine_sat D w j T -> (forall b, b `in` ftv_typ T -> b `notin` V) ->
                spine_sat (ext D V k0) w j T)) /\
  (forall R k, rsat D k R -> (forall b, b `in` ftv_row R -> b `notin` V) ->
     rsat (ext D V k0) k R).
Proof.
  intros D V k0. apply typ_row_mutind; cbn [sat rsat spine_sat ftv_typ ftv_row].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - intros T1 [IH1 _] T2 [_ IH2]. split; [ intros; assumption | ].
    intros w j [Hu Hs] Hv. split.
    + intros Hc. apply (IH1 k_Eq (Hu Hc)). intros b Hb. apply Hv. fsetdec.
    + apply (IH2 w (S j) Hs). intros b Hb. apply Hv. fsetdec.
  - intros R IH. split; [ | intros; contradiction ]. intros k.
    destruct k; [ intros _ _; exact I | | | intros HH; contradiction ];
      (intros Hs Hv; apply IH; assumption).
  - intros a. split; [ | intros; contradiction ]. intros k Hs Hv.
    rewrite ext_out; [ assumption | apply Hv; fsetdec ].
  - intros i. split; intros; first [ assumption | contradiction ].
  - intros B IH. split; [ | intros; contradiction ]. intros k Hs Hv.
    destruct k; try exact I; try contradiction. exact (proj1 IH k_Eq Hs Hv).
  - intros w A IH. split; [ | intros; contradiction ]. intros k Hs Hv.
    destruct k; try exact I; try contradiction. exact (proj2 IH w 0 Hs Hv).
  - intros k _ _. exact I.
  - intros r k Hs Hv. exact Hs.
  - intros l T [IHT _] R IHR k [Hs1 Hs2] Hv. split.
    + apply IHT; [ exact Hs1 | intros b Hb; apply Hv; fsetdec ].
    + apply IHR; [ exact Hs2 | intros b Hb; apply Hv; fsetdec ].
  - intros l P _ T _ R _ k Hs Hv. exact Hs.
Qed.

Lemma sat_ext_out : forall D V k0 k T,
  sat D k T -> (forall b, b `in` ftv_typ T -> b `notin` V) -> sat (ext D V k0) k T.
Proof.
  intros D V k0 k T H Hout. exact (proj1 (proj1 (sat_ext_out_mut D V k0) T) k H Hout).
Qed.

Lemma supp_ok_ext_set : forall D S V k,
  supp_ok D S -> supp_ok (ext D V k) (S `union` V).
Proof.
  intros D S V k HS. exact (supp_ok_ext D S V k HS).
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

Lemma sel_out : forall {A : Type} (key : atom -> atom) (val : atom -> A) b d l,
  (forall a, In a l -> b <> key a) ->
  fold_right (fun a acc => if Atom.eq_dec b (key a) then val a else acc) d l = d.
Proof.
  intros A key val b d l H. induction l as [|a l IH]; [ reflexivity | ]. simpl.
  destruct (Atom.eq_dec b (key a)) as [Heq|Hne].
  - exfalso. exact (H a (or_introl eq_refl) Heq).
  - apply IH. intros a' Ha'. apply H. right. exact Ha'.
Qed.

Lemma sel_at : forall {A : Type} (key : atom -> atom) (val : atom -> A) b d l a,
  In a l -> b = key a ->
  (forall a', In a' l -> key a' = key a -> val a' = val a) ->
  fold_right (fun a acc => if Atom.eq_dec b (key a) then val a else acc) d l = val a.
Proof.
  intros A key val b d l a Ha Hb Hinj. induction l as [|c l IH]; [ inversion Ha | ]. simpl.
  destruct (Atom.eq_dec b (key c)) as [Heq|Hne].
  - apply Hinj; [ left; reflexivity | congruence ].
  - destruct Ha as [Ha|Ha].
    + subst c. exfalso. apply Hne. exact Hb.
    + apply IH; [ exact Ha | intros a' Ha' H'; apply Hinj; [ right; exact Ha' | exact H' ] ].
Qed.

Section InstDen.
Variables (D : denv) (s : scheme) (n : nat).
Let lq := AtomSetImpl.elements (s_tq s).
Let lr := AtomSetImpl.elements (s_rq s).
Let key (a : atom) := ea (n + idx a lq).
Let rkey (r : atom) := ea (n + length lq + idx r lr).

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

Lemma inst_rden_out : forall b,
  (forall r, In r lr -> b <> ea (n + length lq + idx r lr)) -> drk (inst_den D s n) b = drk D b.
Proof.
  intros b H. unfold inst_den. simpl. fold lq. fold lr.
  apply (sel_out rkey (s_rk s) b (drk D b) lr H).
Qed.

Lemma inst_rden_at : forall r, In r lr ->
  drk (inst_den D s n) (ea (n + length lq + idx r lr)) = s_rk s r.
Proof.
  intros r Hr. unfold inst_den. simpl. fold lq. fold lr.
  apply (sel_at rkey (s_rk s) (ea (n + length lq + idx r lr)) (drk D (ea (n + length lq + idx r lr))) lr r Hr eq_refl).
  intros r' Hr' Hk. unfold rkey in Hk. apply ea_inj in Hk.
  assert (idx r' lr = idx r lr) by lia. rewrite (idx_inj r' r lr Hr' Hr H). reflexivity.
Qed.

Lemma DOk_inst_den : DOk D n ->
  DOk (inst_den D s n) (n + length lq + length lr).
Proof.
  intros [H Hr]. split.
  - intros b Hb. rewrite inst_den_out.
    + apply H. intros m Hm. apply Hb. lia.
    + intros a Ha Heq. apply (Hb (n + idx a lq)); [ | exact Heq ].
      pose proof (idx_lt a lq Ha). lia.
  - intros b Hb. rewrite inst_rden_out.
    + apply Hr. intros m Hm. apply Hb. lia.
    + intros r Hrr Heq. apply (Hb (n + length lq + idx r lr)); [ | exact Heq ].
      pose proof (idx_lt r lr Hrr). lia.
Qed.

Lemma KR_inst_den : DOk D n -> KR D (inst_den D s n) sid.
Proof.
  intros H. split.
  - intros b. cbn [sT sid]. unfold idt. cbn [sat].
    destruct (key_dec key b lq) as [[a [Ha Hb]]|Hn].
    + rewrite Hb. unfold key. rewrite (DOk_ea D n _ H) by lia. apply finer_any.
    + rewrite inst_den_out by exact Hn. apply finer_refl.
  - intros b. change (sR sid b) with (row_Var b).
    destruct (key_dec rkey b lr) as [[r [Hr Hb]]|Hn].
    + rewrite Hb. unfold rkey. rewrite (DOk_rea D n _ H) by lia. apply rkok_any.
    + rewrite <- (inst_rden_out b Hn). apply rkok_self.
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

Lemma gen_rk_at : forall D lr r, In r lr ->
  gen_rk D lr (oa (idx r lr)) = drk D r.
Proof.
  intros D lr r Hr. unfold gen_rk.
  apply (sel_at (fun r => oa (idx r lr)) (drk D) (oa (idx r lr)) rk_any lr r Hr eq_refl).
  intros r' Hr' Hk. apply idx_atom_inj in Hk.
  assert (idx r' lr = idx r lr) by lia. rewrite (idx_inj r' r lr Hr' Hr H). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The environment a scheme's quantified variables live in             *)
(* ------------------------------------------------------------------ *)

(* [D] extended with the sorts and kinds a scheme records for the variables it
   quantifies: the environment a [let]'s bound term is typed in. *)
Definition Dsc (D : denv) (sc : scheme) : denv :=
  extr (ext D (s_tq sc) (s_sk sc)) (s_rq sc) (s_rk sc).

Lemma Dsc_sort_in : forall D sc a, a `in` s_tq sc -> Dsc D sc a = s_sk sc a.
Proof.
  intros D sc a H. unfold Dsc. rewrite extr_dsort. apply ext_in. exact H.
Qed.

Lemma Dsc_sort_out : forall D sc a, a `notin` s_tq sc -> Dsc D sc a = D a.
Proof.
  intros D sc a H. unfold Dsc. rewrite extr_dsort. apply ext_out. exact H.
Qed.

Lemma Dsc_rk_in : forall D sc r, r `in` s_rq sc -> drk (Dsc D sc) r = s_rk sc r.
Proof. intros D sc r H. unfold Dsc. apply extr_in. exact H. Qed.

Lemma Dsc_rk_out : forall D sc r, r `notin` s_rq sc -> drk (Dsc D sc) r = drk D r.
Proof. intros D sc r H. unfold Dsc. rewrite extr_out by exact H. reflexivity. Qed.

Lemma denv_eq_sets : forall D V V' Vr Vr' k rk,
  V [=] V' -> Vr [=] Vr' ->
  denv_eq (extr (ext D V k) Vr rk) (extr (ext D V' k) Vr' rk).
Proof.
  intros D V V' Vr Vr' k rk H Hr.
  eapply denv_eq_trans; [ apply extr_pw; apply ext_set_eq_d; exact H | apply extr_set_eq; exact Hr ].
Qed.

Lemma env_mono_Dsc : forall D n sc, DOk D n ->
  (forall a, a `in` s_tq sc -> od a) -> (forall r, r `in` s_rq sc -> od r) ->
  env_mono D (Dsc D sc).
Proof.
  intros D n sc HD Ht Hr. unfold Dsc.
  eapply env_mono_trans.
  - apply env_mono_ext_d. intros a Ha. exact (DOk_odd D n a HD (Ht a Ha)).
  - apply env_mono_extr_d. intros r Hr0. exact (DOk_rodd D n r HD (Hr r Hr0)).
Qed.

(* A step of the algorithm carries over to the environments that record a
   scheme's quantified variables, which it does not touch. *)
Lemma KR_Dsc_lift : forall D D' n n' s sc,
  OkS s -> DOk D n -> DOk D' n' ->
  (forall a, a `in` s_tq sc -> od a) -> (forall r, r `in` s_rq sc -> od r) ->
  KR D D' s -> KR (Dsc D sc) (Dsc D' sc) s.
Proof.
  intros D D' n n' s sc Hs HD HD' Ht Hr [Hk Hkr].
  pose proof (env_mono_Dsc D' n' sc HD' Ht Hr) as Hm.
  destruct Hs as [_ [_ [_ [Hfx Hfxr]]]]. split.
  - intros a.
    destruct (AtomSetImpl.mem a (s_tq sc)) eqn:Em.
    + apply AtomSetFacts.mem_iff in Em. rewrite (Dsc_sort_in D sc a Em).
      rewrite (Hfx a (not_ev_od a (Ht a Em))). cbn [sat]. rewrite (Dsc_sort_in D' sc a Em). apply finer_refl.
    + assert (Hn : a `notin` s_tq sc) by (apply AtomSetFacts.not_mem_iff; exact Em).
      rewrite (Dsc_sort_out D sc a Hn). exact (sat_mono _ _ _ _ Hm (Hk a)).
  - intros r.
    destruct (AtomSetImpl.mem r (s_rq sc)) eqn:Em.
    + apply AtomSetFacts.mem_iff in Em. rewrite (Dsc_rk_in D sc r Em).
      rewrite (Hfxr r (not_ev_od r (Hr r Em))).
      rewrite <- (Dsc_rk_in D' sc r Em). exact (rkok_self _ _).
    + assert (Hn : r `notin` s_rq sc) by (apply AtomSetFacts.not_mem_iff; exact Em).
      rewrite (Dsc_rk_out D sc r Hn). exact (rkok_mono _ _ _ _ Hm (Hkr r)).
Qed.

(* A substitution that fixes the context's variables, applied between two
   environments it respects. *)
Lemma typing_tsubst_fix_k : forall D D' S S' G e T st sr A,
  typing D G e T -> supp_ok D S -> supp_ok D' S' -> kres D D' st -> rkres D D' sr ->
  tr_supp st sr A ->
  (forall a, a `in` ftv_ctx G -> st a = typ_Var a) ->
  (forall r, r `in` frv_ctx G -> sr r = row_Var r) ->
  typing D' G e (ap_typ st sr T).
Proof.
  intros D D' S S' G e T st sr A Hty HS HS' Hk Hkr Hsupp Hfa Hfr.
  apply (proj1 typing_tsubst_gen_mut D G e T Hty st sr G D' A S S').
  - eapply typing_uniq; exact Hty.
  - exact HS.
  - exact HS'.
  - exact Hk.
  - exact Hkr.
  - apply ctx_subst_fix; [ assumption | assumption | exact (proj2 (proj2 Hsupp)) ].
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

Lemma sat_b_sound_mut : forall D,
  (forall T k, sat_b D k T = true -> sat D k T) /\
  (forall R k, rsat_b D k R = true -> rsat D k R).
Proof.
  intros D. apply typ_row_mutind; simpl.
  - intros k _. exact I.
  - intros k _. exact I.
  - intros k. destruct k; first [ (left; reflexivity) | (right; reflexivity) | discriminate ].
  - intros k. destruct k; first [ (left; reflexivity) | (right; reflexivity) | discriminate ].
  - intros k. destruct k; first [ (left; reflexivity) | (right; reflexivity) | discriminate ].
  - intros T1 _ T2 _ k. destruct k; first [ reflexivity | discriminate ].
  - intros R IH k. destruct k; [ intros _; exact I | apply IH | apply IH | discriminate ].
  - intros a k. apply finer_b_sound.
  - intros i k. destruct k; first [ (left; reflexivity) | discriminate ].
  - intros B _ k. destruct k; first [ (intros _; exact I) | discriminate ].
  - intros w A _ k. destruct k; first [ (intros _; exact I) | discriminate ].
  - intros k _. exact I.
  - intros r k. apply finer_b_sound.
  - intros l T IHT R IHR k H. apply Bool.andb_true_iff in H as [H1 H2]. split; auto.
  - intros l P _ T _ R _ k. destruct k; first [ reflexivity | discriminate ].
Qed.

Lemma sat_b_sound : forall D k T, sat_b D k T = true -> sat D k T.
Proof. intros D k T H. exact (proj1 (sat_b_sound_mut D) T k H). Qed.

