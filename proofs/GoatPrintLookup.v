(* The tag table a printed program builds: each tag of each group of [D] is found
   by its name, and no name the printer gives a binder or a group member is a
   tag. *)

From Stdlib Require Import String Ascii List Arith Lia Bool.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintDen.
Require Import Goat.GoatPrintRecover.
Open Scope string_scope.
Open Scope list_scope.

Definition entries_of (w : gdecl) : tagtab :=
  List.map (fun tg => (cn w tg, (w, tg))) (List.seq 0 (List.length (snd w))).

(* The table the declarations of [D] build. *)
Definition tab (D : list gdecl) : tagtab := List.flat_map decl_entries (print_decls D).

Lemma tab_eq : forall D,
  Forall WfGroup D -> tab D = List.flat_map entries_of D.
Proof.
  induction D as [| w D IH]; intros Hwf; [ reflexivity | ].
  inversion Hwf as [| ? ? Hw Hrest]; subst.
  unfold tab, print_decls in *. cbn [List.map List.flat_map].
  rewrite (decl_entries_print w Hw). unfold entries_of at 1. f_equal. exact (IH Hrest).
Qed.

Lemma tag_lookup_app_some : forall A B x v,
  tag_lookup A x = Some v -> tag_lookup (A ++ B) x = Some v.
Proof.
  induction A as [| [y u] A IH]; intros B x v H; [ discriminate H | ].
  cbn [tag_lookup app] in *. destruct (String.eqb x y); [ exact H | exact (IH _ _ _ H) ].
Qed.

Lemma tag_lookup_app_none : forall A B x,
  tag_lookup A x = None -> tag_lookup (A ++ B) x = tag_lookup B x.
Proof.
  induction A as [| [y u] A IH]; intros B x H; [ reflexivity | ].
  cbn [tag_lookup app] in *. destruct (String.eqb x y); [ discriminate H | exact (IH _ _ H) ].
Qed.

Lemma tag_lookup_none : forall tt x,
  (forall (k : string) (v : gdecl * nat), List.In (k, v) tt -> k <> x) -> tag_lookup tt x = None.
Proof.
  induction tt as [| [y u] tt IH]; intros x H; [ reflexivity | ].
  cbn [tag_lookup]. destruct (String.eqb x y) eqn:E.
  - apply String.eqb_eq in E. exfalso. exact (H y u (or_introl eq_refl) (eq_sym E)).
  - apply IH. intros k v Hk. apply (H k v). right. exact Hk.
Qed.

Lemma gname_inj : forall w w',
  Forall (fun b => b < 256) (fst w) -> Forall (fun b => b < 256) (fst w') ->
  gname w = gname w' -> fst w = fst w'.
Proof.
  intros w w' H H' E.
  rewrite <- (bytes_name (fst w) H), <- (bytes_name (fst w') H'). unfold gname in E.
  rewrite E. reflexivity.
Qed.

Lemma lookup_entries : forall (w : gdecl) n s tg,
  s <= tg -> tg < s + n ->
  tag_lookup (List.map (fun t => (cn w t, (w, t))) (List.seq s n)) (cn w tg) = Some (w, tg).
Proof.
  intros w n. induction n as [| n IH]; intros s tg Hs Ht; [ lia | ].
  cbn [List.seq List.map tag_lookup]. destruct (String.eqb (cn w tg) (cn w s)) eqn:E.
  - apply String.eqb_eq in E. destruct (cn_inj _ _ _ _ E) as [-> _]. reflexivity.
  - apply IH; [ | lia ].
    destruct (Nat.eq_dec s tg) as [-> | Hne].
    + rewrite String.eqb_refl in E. discriminate E.
    + lia.
Qed.

Lemma lookup_cn_other : forall (w w' : gdecl) tg,
  Forall (fun b => b < 256) (fst w) -> Forall (fun b => b < 256) (fst w') ->
  fst w <> fst w' ->
  tag_lookup (entries_of w') (cn w tg) = None.
Proof.
  intros w w' tg Hb Hb' Hne. apply tag_lookup_none. intros k v Hin Heq.
  unfold entries_of in Hin. apply List.in_map_iff in Hin. destruct Hin as (tg' & Hv & _).
  injection Hv as <- _. destruct (cn_inj _ _ _ _ Heq) as [_ Hg].
  exact (Hne (gname_inj _ _ Hb Hb' (eq_sym Hg))).
Qed.

Lemma lookup_cn : forall D w tg,
  WfTable D -> List.In w D -> tg < List.length (snd w) ->
  tag_lookup (tab D) (cn w tg) = Some (w, tg).
Proof.
  intros D w tg (Hwf & Hnd). rewrite (tab_eq D Hwf). revert Hwf Hnd.
  induction D as [| w0 D IH]; intros Hwf Hnd Hin Htg; [ destruct Hin | ].
  inversion Hwf as [| ? ? Hw0 Hrest]; subst. inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  cbn [List.flat_map]. destruct Hin as [-> | Hin].
  - apply tag_lookup_app_some. unfold entries_of. apply lookup_entries; lia.
  - assert (Hne : fst w <> fst w0).
    { intros Heq. apply Hnotin. rewrite <- Heq. apply List.in_map. exact Hin. }
    assert (Hbw : Forall (fun b => b < 256) (fst w))
      by exact (proj1 ((proj1 (Forall_forall _ _) Hrest) w Hin)).
    assert (Hbw0 : Forall (fun b => b < 256) (fst w0)) by exact (proj1 Hw0).
    rewrite (tag_lookup_app_none _ _ _ (lookup_cn_other w w0 tg Hbw Hbw0 Hne)).
    exact (IH Hrest Hnd' Hin Htg).
Qed.
