(* Runs of function declarations in a block (GoatDen.v, [DK_group_hoist] and
   [DK_group_late]). A run is split into groups: the least prefix every cut of
   which a mention crosses, and no member of which names a function after it.
   [run_blk] says a run always denotes something; [hoist_run] says what it
   denotes when no member uses an earlier value, which is every function
   hoisted. *)

From Stdlib Require Import String List Arith Lia Bool.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatDen.
Open Scope string_scope.
Open Scope list_scope.

(* ---- the list half: the least closed prefix of a run ---- *)

Lemma mentions_any_iff : forall ns v,
  mentions_any ns v = true <-> exists y, List.In y ns /\ mentions y v = true.
Proof. intros ns v. unfold mentions_any. apply existsb_exists. Qed.

Lemma in_firstn_incl : forall (A : Type) (l : list A) j x, List.In x (firstn j l) -> List.In x l.
Proof.
  intros A l j x H. rewrite <- (firstn_skipn j l). apply in_or_app. left. exact H.
Qed.

Lemma in_firstn_mono : forall (A : Type) (l : list A) j m x,
  j <= m -> List.In x (firstn j l) -> List.In x (firstn m l).
Proof.
  intros A l j m x Hjm H. apply (in_firstn_incl A (firstn m l) j).
  rewrite firstn_firstn. replace (Nat.min j m) with j by lia. exact H.
Qed.

Lemma mentions_none : forall vs, existsb (mentions_any []) vs = false.
Proof.
  intros vs. apply Bool.not_true_iff_false. rewrite existsb_exists. intros (x & _ & Hx).
  simpl in Hx. discriminate Hx.
Qed.

(* A run's names [R] and bodies [vs]: the least [m] such that no member of the
   first [m] names a function after them, and every cut before [m] is crossed
   by a mention. *)
Lemma run_split : forall (R : list termvar) (vs : list exp),
  R <> [] -> length vs = length R ->
  exists m, 1 <= m /\ m <= length R /\
    existsb (mentions_any (skipn m R)) (firstn m vs) = false /\
    run_linked (firstn m R) (firstn m vs).
Proof.
  intros R vs HR Hlen.
  set (P := fun j => (Nat.leb 1 j) && negb (existsb (mentions_any (skipn j R)) (firstn j vs)) = true).
  assert (Hdec : forall j, P j \/ ~ P j) by (intro j; unfold P;
    destruct (Nat.leb 1 j && negb (existsb (mentions_any (skipn j R)) (firstn j vs)));
    [ left; reflexivity | right; discriminate ]).
  assert (Hall : P (length R)).
  { unfold P. rewrite skipn_all, mentions_none.
    destruct R as [| r R']; [ contradiction | reflexivity ]. }
  assert (Hex : exists j, P j) by (exists (length R); exact Hall).
  destruct (dec_inh_nat_subset_has_unique_least_element P Hdec Hex) as (m & [Hspec Hleast] & _).
  assert (Hmin : forall j, j < m -> ~ P j).
  { intros j Hj HPj. pose proof (Hleast j HPj). lia. }
  assert (Hle : m <= length R) by exact (Hleast _ Hall).
  unfold P in Hspec. apply andb_prop in Hspec as [H1 Hclosed].
  apply Nat.leb_le in H1. apply negb_true_iff in Hclosed.
  exists m. split; [ exact H1 | split; [ exact Hle | split; [ exact Hclosed | ] ] ].
  intros j Hj0 Hjm. rewrite length_firstn in Hjm.
  assert (Hjm' : j < m) by lia.
  assert (HnP : ~ P j) by exact (Hmin j Hjm').
  unfold P in HnP.
  assert (Hopen : existsb (mentions_any (skipn j R)) (firstn j vs) = true).
  { destruct (existsb (mentions_any (skipn j R)) (firstn j vs)) eqn:E; [ reflexivity | exfalso; apply HnP ].
    assert (H1j : (Nat.leb 1 j) = true) by (apply Nat.leb_le; lia).
    rewrite H1j. reflexivity. }
  rewrite existsb_exists in Hopen. destruct Hopen as (v & Hv & Hmv).
  apply mentions_any_iff in Hmv. destruct Hmv as (y & Hy & Hyv).
  unfold cut_linked. apply existsb_exists. exists v. split.
  - rewrite firstn_firstn. replace (Nat.min j m) with j by lia. exact Hv.
  - apply mentions_any_iff. exists y. split; [ | exact Hyv ].
    rewrite <- (firstn_skipn m R) in Hy.
    rewrite skipn_app in Hy. rewrite length_firstn in Hy.
    replace (Nat.min m (length R)) with m in Hy by lia.
    replace (j - m) with 0 in Hy by lia. simpl in Hy.
    apply in_app_or in Hy. destruct Hy as [Hy | Hy]; [ exact Hy | exfalso ].
    assert (Hfalse : existsb (mentions_any (skipn m R)) (firstn m vs) = true).
    { apply existsb_exists. exists v. split.
      - exact (in_firstn_mono _ vs j m v (Nat.lt_le_incl _ _ Hjm') Hv).
      - apply mentions_any_iff. exists y. split; [ exact Hy | exact Hyv ]. }
    rewrite Hclosed in Hfalse. discriminate Hfalse.
Qed.

(* ---- function declarations ---- *)

Lemma fn_decl_name_decl : forall d, fn_decl_name d <> None -> is_fn_decl d = true.
Proof.
  intros d H. destruct (is_fn_decl d) eqn:E; [ reflexivity | exfalso; apply H ].
  unfold fn_decl_name. destruct d as [k | r cs]; [ reflexivity | ].
  destruct r; try reflexivity.
  destruct cs as [| [tk | rn cn] rest]; try reflexivity.
  destruct rn; try reflexivity.
  destruct cn as [| [tk | rn' cn'] [| t' cn'']]; try reflexivity.
  destruct tk; try reflexivity.
  all: try (rewrite E; reflexivity).
  all: try (destruct tk; reflexivity).
Qed.

Lemma fn_decl_name_nonfn : forall d, is_fn_decl d = false -> fn_decl_name d = None.
Proof.
  intros d E. unfold fn_decl_name. destruct d as [k | r cs]; [ reflexivity | ].
  destruct r; try reflexivity.
  destruct cs as [| [tk | rn cn] rest]; try reflexivity.
  destruct rn; try reflexivity.
  destruct cn as [| [tk | rn' cn'] [| t' cn'']]; try reflexivity.
  destruct tk; try reflexivity.
  all: try (rewrite E; reflexivity).
  all: try (destruct tk; reflexivity).
Qed.

Section Runs.

  Context {TT : TagTable}.
  Variable var_of : string -> termvar.
  Variable tbl : list string.

  Lemma fdecls_len : forall ds xs vs, Den_fdecls var_of tbl ds xs vs ->
    length xs = length ds /\ length vs = length ds.
  Proof.
    intros ds xs vs H. induction H as [| d x v ds xs vs _ _ _ [IH1 IH2]]; simpl; auto.
  Qed.

  Lemma fdecls_split : forall ds xs vs, Den_fdecls var_of tbl ds xs vs -> forall m,
    Den_fdecls var_of tbl (firstn m ds) (firstn m xs) (firstn m vs) /\
    Den_fdecls var_of tbl (skipn m ds) (skipn m xs) (skipn m vs).
  Proof.
    intros ds xs vs H. induction H as [| d x v ds xs vs Hd Hfn Hrest IH]; intros m.
    - destruct m; simpl; split; apply DF_nil.
    - destruct m as [| m]; simpl.
      + split; [ apply DF_nil | apply DF_cons; assumption ].
      + destruct (IH m) as [IH1 IH2]. split; [ apply DF_cons; assumption | exact IH2 ].
  Qed.

  Lemma decl_name_is : forall d x v, Den_decl var_of tbl d x v ->
    fn_decl_name d = if is_fn_decl d then Some x else None.
  Proof. intros d x v H. inversion H; subst; reflexivity. Qed.

  Lemma fdecls_names : forall ds xs vs, Den_fdecls var_of tbl ds xs vs -> forall rest,
    fn_run_names var_of (ds ++ rest) = List.map var_of xs ++ fn_run_names var_of rest.
  Proof.
    intros ds xs vs H. induction H as [| d x v ds xs vs Hd Hfn _ IH]; intros rest; [ reflexivity | ].
    simpl. inversion Hd; subst; unfold fn_decl_name, ident; simpl in Hfn |- *; rewrite Hfn;
      rewrite IH; reflexivity.
  Qed.

  Lemma fdecls_single_or_group : forall g xg vg, Den_fdecls var_of tbl g xg vg -> g <> [] ->
    (exists d x v, g = [d] /\ xg = [x] /\ vg = [v] /\
       Den_decl var_of tbl d x v /\ is_fn_decl d = true)
    \/ 1 < length g.
  Proof.
    intros g xg vg H Hne. inversion H as [| d x v ds xs vs Hd Hfn Hrest]; subst; [ contradiction | ].
    inversion Hrest; subst.
    - left. exists d, x, v. repeat split; assumption.
    - right. simpl. lia.
  Qed.

  (* The least closed prefix of a nonempty run, with the rest of it. *)
  Lemma run_prefix : forall ds xs vs, Den_fdecls var_of tbl ds xs vs -> ds <> [] ->
    exists g ds1 xg xs1 vg vs1,
      ds = g ++ ds1 /\ xs = xg ++ xs1 /\ vs = vg ++ vs1 /\
      Den_fdecls var_of tbl g xg vg /\ Den_fdecls var_of tbl ds1 xs1 vs1 /\
      g <> [] /\
      run_linked (List.map var_of xg) vg /\
      existsb (mentions_any (List.map var_of xs1)) vg = false.
  Proof.
    intros ds xs vs H Hne.
    destruct (fdecls_len _ _ _ H) as [Hx Hv].
    assert (HR : List.map var_of xs <> []).
    { destruct xs as [| x xs']; simpl; [ | discriminate ].
      destruct ds; [ contradiction | simpl in Hx; discriminate ]. }
    destruct (run_split (List.map var_of xs) vs HR) as (m & Hm1 & Hm2 & Hclosed & Hlinked).
    { rewrite length_map. lia. }
    rewrite length_map in Hm2.
    destruct (fdecls_split _ _ _ H m) as [Hg Hd1].
    exists (firstn m ds), (skipn m ds), (firstn m xs), (skipn m xs), (firstn m vs), (skipn m vs).
    repeat split.
    - rewrite firstn_skipn. reflexivity.
    - rewrite firstn_skipn. reflexivity.
    - rewrite firstn_skipn. reflexivity.
    - exact Hg.
    - exact Hd1.
    - intros Hnil. apply (f_equal (@length GoatPeg.tree)) in Hnil. rewrite length_firstn in Hnil.
      simpl in Hnil. lia.
    - rewrite <- firstn_map. exact Hlinked.
    - rewrite <- skipn_map. exact Hclosed.
  Qed.

  Lemma run_names_app : forall tl k,
    fn_run_names var_of tl = [] -> fn_run_names var_of k = [] ->
    fn_run_names var_of (tl ++ k) = [].
  Proof.
    intros tl k Htl Hk. induction tl as [| a tl IH]; [ exact Hk | ].
    simpl in Htl |- *. destruct (fn_decl_name a); [ discriminate | reflexivity ].
  Qed.

  (* The function declarations that open a block, and what follows them. *)
  Lemma run_decompose : forall d cs, fn_decl_name d <> None ->
    exists fr tl, d :: cs = fr ++ tl /\ fr <> [] /\
      Forall (fun d => fn_decl_name d <> None) fr /\ fn_run_names var_of tl = [].
  Proof.
    intros d cs. revert d. induction cs as [| d2 cs IH]; intros d Hd.
    - exists [d], []. repeat split; [ discriminate | constructor; [ exact Hd | constructor ] ].
    - destruct (fn_decl_name d2) eqn:E2.
      + destruct (IH d2 ltac:(rewrite E2; discriminate)) as (fr & tl & Heq & Hne & Hfr & Htl).
        exists (d :: fr), tl. repeat split.
        * simpl. rewrite Heq. reflexivity.
        * discriminate.
        * constructor; assumption.
        * exact Htl.
      + exists [d], (d2 :: cs). repeat split.
        * discriminate.
        * constructor; [ exact Hd | constructor ].
        * simpl. rewrite E2. reflexivity.
  Qed.

  Lemma fdecls_of : forall fr,
    Forall (fun d => is_fn_decl d = true /\ exists x v, Den_decl var_of tbl d x v) fr ->
    exists xs vs, Den_fdecls var_of tbl fr xs vs.
  Proof.
    intros fr H. induction H as [| d fr [Hfn (x & v & Hd)] _ (xs & vs & IH)].
    - exists [], []. apply DF_nil.
    - exists (x :: xs), (v :: vs). apply DF_cons; assumption.
  Qed.

  (* ---- every run denotes something ---- *)

  Lemma run_blk : forall ds xs vs, Den_fdecls var_of tbl ds xs vs ->
    forall rest, fn_run_names var_of rest = [] ->
    (forall ctx fin, exists ys gs b, Den_blk var_of tbl ctx fin rest ys gs b) ->
    forall ctx fin, exists ys gs b, Den_blk var_of tbl ctx fin (ds ++ rest) ys gs b.
  Proof.
    intros ds. remember (length ds) as n eqn:Hn. revert ds Hn.
    induction n as [n IH] using lt_wf_ind.
    intros ds Hn xs vs Hden rest Hrest Htot ctx fin.
    destruct (match ds with [] => true | _ => false end) eqn:Hnil.
    { destruct ds; [ | discriminate ]. exact (Htot ctx fin). }
    assert (Hne : ds <> []) by (intros ->; discriminate Hnil).
    destruct (run_prefix ds xs vs Hden Hne)
      as (g & ds1 & xg & xs1 & vg & vs1 & Hds & Hxs & Hvs & Hg & Hd1 & Hgne & Hlink & Hclosed).
    subst ds xs vs.
    assert (Hlen : length ds1 < n).
    { rewrite Hn, length_app. destruct g; [ contradiction | simpl; lia ]. }
    assert (Hnames : fn_run_names var_of (ds1 ++ rest) = List.map var_of xs1).
    { rewrite (fdecls_names _ _ _ Hd1), Hrest, app_nil_r. reflexivity. }
    assert (Htot1 := IH (length ds1) Hlen ds1 eq_refl xs1 vs1 Hd1 rest Hrest Htot).
    rewrite app_assoc.
    rewrite <- Hnames in Hclosed.
    destruct (fdecls_single_or_group g xg vg Hg Hgne)
      as [(d & x & v & -> & -> & -> & Hd & Hfn) | Hmany].
    - simpl in Hclosed. rewrite orb_false_r in Hclosed. simpl.
      destruct (mentions_any ctx v) eqn:Hm.
      + destruct (Htot1 (var_of x :: ctx) (e_fvar_f (var_of x))) as (ys & gs & b & Hb).
        exists ys, gs, (fn_place (var_of x) v b).
        eapply DK_late; eassumption.
      + destruct (Htot1 ctx (e_fvar_f (var_of x))) as (ys & gs & b & Hb).
        exists (x :: ys), (v :: gs), b.
        eapply DK_hoist; eassumption.
    - destruct (existsb (mentions_any ctx) vg) eqn:Hm.
      + destruct (Htot1 (List.map var_of xg ++ ctx) (e_fvar_f (var_of (List.last xg "")))) as (ys & gs & b & Hb).
        exists ys, gs, (wrap_group (List.map var_of xg) vg b).
        eapply DK_group_late; eassumption.
      + destruct (Htot1 ctx (e_fvar_f (var_of (List.last xg "")))) as (ys & gs & b & Hb).
        exists (xg ++ ys), (vg ++ gs), b.
        eapply DK_group_hoist; eassumption.
  Qed.

  (* ---- a run that uses no earlier value is hoisted, however it splits ---- *)

  Lemma hoist_run : forall ctx ds xs vs, Den_fdecls var_of tbl ds xs vs ->
    existsb (mentions_any ctx) vs = false ->
    forall rest, fn_run_names var_of rest = [] ->
    forall ys gs b, (forall fin, Den_blk var_of tbl ctx fin rest ys gs b) ->
    forall fin, Den_blk var_of tbl ctx fin (ds ++ rest) (xs ++ ys) (vs ++ gs) b.
  Proof.
    intros ctx ds. remember (length ds) as n eqn:Hn. revert ds Hn.
    induction n as [n IH] using lt_wf_ind.
    intros ds Hn xs vs Hden Hctx rest Hrest ys gs b Hb fin.
    destruct (match ds with [] => true | _ => false end) eqn:Hnil.
    { destruct ds; [ | discriminate ].
      inversion Hden; subst. exact (Hb fin). }
    assert (Hne : ds <> []) by (intros ->; discriminate Hnil).
    destruct (run_prefix ds xs vs Hden Hne)
      as (g & ds1 & xg & xs1 & vg & vs1 & Hds & Hxs & Hvs & Hg & Hd1 & Hgne & Hlink & Hclosed).
    subst ds xs vs.
    assert (Hlen : length ds1 < n).
    { rewrite Hn, length_app. destruct g; [ contradiction | simpl; lia ]. }
    assert (Hnames : fn_run_names var_of (ds1 ++ rest) = List.map var_of xs1).
    { rewrite (fdecls_names _ _ _ Hd1), Hrest, app_nil_r. reflexivity. }
    rewrite existsb_app in Hctx. apply orb_false_iff in Hctx as [Hctxg Hctx1].
    assert (IH1 := IH (length ds1) Hlen ds1 eq_refl xs1 vs1 Hd1 Hctx1 rest Hrest ys gs b Hb).
    rewrite app_assoc. rewrite app_assoc. rewrite app_assoc.
    rewrite <- Hnames in Hclosed.
    destruct (fdecls_single_or_group g xg vg Hg Hgne)
      as [(d & x & v & -> & -> & -> & Hd & Hfn) | Hmany].
    - simpl in Hclosed, Hctxg. rewrite orb_false_r in Hclosed, Hctxg. simpl.
      eapply DK_hoist; [ exact Hd | exact Hfn | exact Hctxg | exact Hclosed | exact (IH1 _) ].
    - eapply DK_group_hoist; [ exact Hg | exact Hmany | exact Hlink | exact Hclosed
                             | exact Hctxg | exact (IH1 _) ].
  Qed.

End Runs.
