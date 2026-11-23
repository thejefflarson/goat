(* The token at the start of an input does not depend on what follows a run of
   whitespace it ends before (phase 8, stage 1).  [step_stab] is the lemma the
   edit theorem ([GoatLexEdit.v]) is built from. *)

From Stdlib Require Import List String Ascii Arith Bool Lia.
Import ListNotations.
Require Import Goat.GoatLex.
Require Import Goat.GoatLexSpec.
Require Import Goat.GoatLexBarrier.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

Lemma string_body_pos : forall r esc m, string_body esc r = Some m -> 1 <= m.
Proof.
  induction r as [|c t IH]; intros esc m H; [discriminate|].
  cbn [string_body] in H. destruct esc.
  - destruct (string_body false t); cbn [option_map] in H; [|discriminate].
    inversion H; lia.
  - destruct (c =? 34); [inversion H; lia|].
    destruct (string_body (c =? 92) t); cbn [option_map] in H; [|discriminate].
    inversion H; lia.
Qed.

(* A string that closes inside [a] closes there whatever follows. *)
Lemma string_body_stable : forall a b b' esc m,
  string_body esc (a ++ b) = Some m -> m <= List.length a ->
  string_body esc (a ++ b') = Some m.
Proof.
  induction a as [|c t IH]; intros b b' esc m H Hm.
  - simpl in *. pose proof (string_body_pos _ _ _ H). lia.
  - cbn [app string_body] in *. destruct esc.
    + destruct (string_body false (t ++ b)) as [m1|] eqn:E; cbn [option_map] in H; [|discriminate].
      inversion H; subst. simpl in Hm.
      rewrite (IH b b' false m1 E ltac:(lia)). reflexivity.
    + destruct (c =? 34); [exact H|].
      destruct (string_body (c =? 92) (t ++ b)) as [m1|] eqn:E; cbn [option_map] in H; [|discriminate].
      inversion H; subst. simpl in Hm.
      rewrite (IH b b' (c =? 92) m1 E ltac:(lia)). reflexivity.
Qed.

Lemma prefixb_app_le : forall w a b,
  List.length w <= List.length a -> prefixb w (a ++ b) = prefixb w a.
Proof.
  induction w as [|x w IH]; intros a b H; [reflexivity|].
  destruct a as [|y a]; simpl in H; [lia|]. simpl.
  destruct (x =? y); [|reflexivity]. simpl. apply IH. lia.
Qed.

Section Stab.
  Variables (hs hc : nat -> bool).

  Lemma pick_ext : forall cl r r' acc,
    (forall k m, In (k, m) cl -> m r = m r') -> pick cl r acc = pick cl r' acc.
  Proof.
    induction cl as [|[k m] cl IH]; intros r r' acc H; [reflexivity|].
    cbn [pick]. rewrite (H k m (or_introl eq_refl)).
    apply IH. intros k0 m0 Hin. exact (H k0 m0 (or_intror Hin)).
  Qed.

  Lemma lens_eq_step : forall r r',
    (forall k m, In (k, m) (classes hs hc) -> m r = m r') -> step hs hc r = step hs hc r'.
  Proof.
    intros r r' H. unfold step. rewrite (pick_ext _ r r' (KUnknown, 0) H). reflexivity.
  Qed.

  (* The only class that matches a whitespace, hash or quote start is the one
     those characters open. *)
  Lemma head_class : forall c t k m,
    In (k, m) (classes hs hc) -> m (c :: t) <> 0 ->
    (c = 35 -> k = KComment) /\ (c = 34 -> k = KString) /\ (is_ws c = true -> k = KWhitespace).
  Proof.
    intros c t k m Hin Hm.
    destruct (in_classes hs hc k m Hin) as
      [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> [-> | ->]]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]];
      repeat split; intro Hc; try reflexivity; exfalso; apply Hm;
      first [ (subst c; reflexivity)
            | (destruct (ws_cases c Hc) as [-> | [-> | [-> | ->]]]; reflexivity) ].
  Qed.

  Lemma pick_zeros : forall cl r acc,
    (forall k m, In (k, m) cl -> m r = 0) -> pick cl r acc = acc.
  Proof.
    induction cl as [|[k m] cl IH]; intros r acc H; [reflexivity|].
    cbn [pick]. rewrite (H k m (or_introl eq_refl)).
    assert (Hn : (snd acc <? 0) = false) by (apply Nat.ltb_ge; lia). rewrite Hn.
    apply IH. intros k0 m0 Hin. exact (H k0 m0 (or_intror Hin)).
  Qed.

  Lemma tail_not_ws : forall k m, In (k, m) (tl (classes hs hc)) -> k <> KWhitespace.
  Proof.
    intros k m H. unfold classes in H. simpl in H.
    repeat (destruct H as [H|H]; [inversion H; subst; discriminate|]); contradiction.
  Qed.

  (* A run of whitespace not followed by whitespace is one token. *)
  Lemma step_ws : forall c t, is_ws c = true ->
    step hs hc (c :: t) = (KWhitespace, span is_ws (c :: t)).
  Proof.
    intros c t Hc.
    assert (Hn : 0 < span is_ws (c :: t)) by (simpl; rewrite Hc; lia).
    assert (Hcl : classes hs hc = (KWhitespace, whitespace_len) :: tl (classes hs hc)) by reflexivity.
    unfold step. rewrite Hcl. cbn [pick].
    replace (snd (KUnknown, 0) <? whitespace_len (c :: t)) with true
      by (symmetry; apply Nat.ltb_lt; exact Hn).
    rewrite pick_zeros.
    - assert (E : (span is_ws (c :: t) =? 0) = false) by (apply Nat.eqb_neq; lia).
      unfold whitespace_len. rewrite E. reflexivity.
    - intros k m Hin.
      destruct (m (c :: t)) eqn:Em; [reflexivity|].
      exfalso. assert (Hin' : In (k, m) (classes hs hc)) by (rewrite Hcl; right; exact Hin).
      destruct (head_class c t k m Hin' ltac:(rewrite Em; discriminate)) as (_ & _ & Hw).
      exact (tail_not_ws k m Hin (Hw Hc)).
  Qed.

  Lemma comment_eq : forall x z z',
    x <> [] -> comment_len (x ++ z) <= List.length x ->
    (comment_len (x ++ z) = List.length x -> stops not_nl z' = true) ->
    comment_len (x ++ z') = comment_len (x ++ z).
  Proof.
    intros x z z' Hx Hle Hg.
    destruct x as [|c x']; [contradiction|].
    cbn [app comment_len] in *.
    destruct (c =? 35); [|reflexivity].
    cbn [List.length] in *.
    destruct (Nat.lt_ge_cases (span not_nl (x' ++ z)) (List.length x')) as [Hlt|Hge].
    - rewrite (span_stable_inside not_nl x' z z' Hlt). reflexivity.
    - assert (Heq : span not_nl (x' ++ z) = List.length x') by lia.
      rewrite (span_stable_end not_nl x' z z' Heq (Hg ltac:(lia))). rewrite Heq. reflexivity.
  Qed.

  Lemma string_eq : forall x z z',
    x <> [] -> string_len (x ++ z) <= List.length x ->
    (forall x', x = 34 :: x' -> string_len (x ++ z) <> 0) ->
    string_len (x ++ z') = string_len (x ++ z).
  Proof.
    intros x z z' Hx Hle Hq.
    destruct x as [|c x']; [contradiction|].
    destruct (c =? 34) eqn:Ec; [|unfold string_len; cbn [app]; rewrite Ec; reflexivity].
    apply Nat.eqb_eq in Ec. subst c.
    specialize (Hq x' eq_refl).
    cbn [app string_len] in *.
    destruct (string_body false (x' ++ z)) as [m|] eqn:E; [|exfalso; apply Hq; reflexivity].
    rewrite Nat.eqb_refl in Hq, Hle |- *. cbn [List.length] in Hle.
    rewrite (string_body_stable x' z z' false m E ltac:(lia)). reflexivity.
  Qed.

  Lemma word_len_one : forall w r,
    word_len hc [w] r = (if word_fits hc w r then List.length w else 0).
  Proof. intros w r. unfold word_len. simpl. destruct (word_fits hc w r); reflexivity. Qed.

  Lemma barb_boundary : forall b,
    barb b = true -> match b with c :: _ => negb (xc hc c) | [] => true end = true.
  Proof.
    intros [|c b] H; [reflexivity|]. simpl in H |- *. rewrite (xc_ws hc c H). reflexivity.
  Qed.

  Lemma word_fits_app_le : forall w x z z',
    List.length w <= List.length x -> barb z = true -> barb z' = true ->
    word_fits hc w (x ++ z') = word_fits hc w (x ++ z).
  Proof.
    intros w x z z' Hl Hz Hz'. unfold word_fits.
    rewrite (prefixb_app_le w x z Hl), (prefixb_app_le w x z' Hl).
    destruct (prefixb w x); [|reflexivity]. simpl. unfold boundary.
    rewrite (skipn_app_le _ _ _ Hl), (skipn_app_le _ _ _ Hl).
    destruct (skipn (List.length w) x) as [|e x'']; simpl;
      [|reflexivity].
    rewrite (barb_boundary z Hz), (barb_boundary z' Hz'). reflexivity.
  Qed.

  Lemma prefixb_split : forall u a b,
    prefixb u (a ++ b) = true -> List.length a <= List.length u ->
    prefixb (firstn (List.length a) u) a = true /\ prefixb (skipn (List.length a) u) b = true.
  Proof.
    intros u a. revert u. induction a as [|y a IH]; intros u b H Hl; [simpl in *; auto|].
    destruct u as [|v u]; simpl in Hl; [lia|].
    cbn [app prefixb] in H. apply andb_true_iff in H as [Hv H].
    cbn [List.length firstn skipn prefixb]. rewrite Hv. simpl.
    apply (IH u b H). lia.
  Qed.

  Lemma prefixb_eq : forall u a, prefixb u a = true -> List.length u = List.length a -> u = a.
  Proof.
    induction u as [|v u IH]; intros [|y a] H Hl; simpl in *; try lia; try reflexivity.
    apply andb_true_iff in H as [Hv H]. apply Nat.eqb_eq in Hv. subst.
    f_equal. apply IH; [exact H|lia].
  Qed.

  Lemma start_at_eq : start_at = [115; 116; 97; 114; 116; 32; 97; 116].
  Proof. reflexivity. Qed.

  Lemma start_ws_index : forall l, l < 8 -> is_ws (nth l start_at 0) = true -> l = 5.
  Proof.
    intros l Hl H. rewrite start_at_eq in H.
    destruct l as [|[|[|[|[|[|[|[|l]]]]]]]]; simpl in H; try discriminate; try reflexivity; lia.
  Qed.

  (* Only [start] can be the start of [start at] that a whitespace run
     finishes. *)
  Lemma startat_prefix : forall x z',
    List.length x < 8 -> barb z' = true -> prefixb start_at (x ++ z') = true ->
    x = cps "start".
  Proof.
    intros x z' Hl Hb H.
    destruct (prefixb_split start_at x z' H ltac:(rewrite start_at_eq; simpl; lia)) as [H1 H2].
    assert (Hx : firstn (List.length x) start_at = x)
      by (apply prefixb_eq; [exact H1|rewrite length_firstn; rewrite start_at_eq; simpl; lia]).
    destruct (skipn (List.length x) start_at) as [|v u] eqn:Esk.
    - assert (Hlen : List.length (skipn (List.length x) start_at) = 8 - List.length x)
        by (rewrite length_skipn; rewrite start_at_eq; reflexivity).
      rewrite Esk in Hlen. cbn [List.length] in Hlen. lia.
    - destruct z' as [|e z'']; [discriminate|]. simpl in H2, Hb.
      apply andb_true_iff in H2 as [Hve _]. apply Nat.eqb_eq in Hve. subst e.
      assert (Hnth : nth (List.length x) start_at 0 = v).
      { rewrite <- (firstn_skipn (List.length x) start_at) at 1.
        rewrite app_nth2 by (rewrite length_firstn; rewrite start_at_eq; simpl; lia).
        rewrite length_firstn, Esk.
        replace (List.length x - Nat.min (List.length x) (List.length start_at)) with 0
          by (rewrite start_at_eq; simpl; lia).
        reflexivity. }
      assert (Hl5 : List.length x = 5)
        by (apply start_ws_index; [exact Hl|rewrite Hnth; exact Hb]).
      rewrite <- Hx, Hl5. reflexivity.
  Qed.

  Lemma startat_name : forall z, barb z = true -> name_len hs hc (cps "start" ++ z) = 5.
  Proof.
    intros z H. unfold name_len.
    rewrite (name_sm_stable hs hc (cps "start") z None H). reflexivity.
  Qed.

  Lemma startat_eq : forall x z z' n,
    barb z = true -> barb z' = true -> x <> [] ->
    word_len hc [start_at] (x ++ z) <= n -> name_len hs hc (x ++ z) <= n -> n <= List.length x ->
    (n = List.length x -> word_fits hc start_at (x ++ z') = false) ->
    word_len hc [start_at] (x ++ z') = word_len hc [start_at] (x ++ z).
  Proof.
    intros x z z' n Hz Hz' Hx Hw Hname Hn Hg.
    rewrite !word_len_one. rewrite word_len_one in Hw.
    destruct (Nat.le_gt_cases 8 (List.length x)) as [H8|H8].
    - rewrite (word_fits_app_le start_at x z z' ltac:(rewrite start_at_eq; simpl; lia) Hz Hz').
      reflexivity.
    - assert (Hf : word_fits hc start_at (x ++ z) = false).
      { destruct (word_fits hc start_at (x ++ z)) eqn:E; [|reflexivity].
        try rewrite E in Hw. rewrite start_at_eq in Hw. simpl in Hw. lia. }
      rewrite Hf.
      destruct (word_fits hc start_at (x ++ z')) eqn:E'; [|reflexivity].
      exfalso.
      assert (Hp : prefixb start_at (x ++ z') = true)
        by (unfold word_fits in E'; exact (proj1 (andb_prop _ _ E'))).
      pose proof (startat_prefix x z' H8 Hz' Hp) as Hxs.
      subst x. rewrite (startat_name z Hz) in Hname.
      assert (Hnx : n = List.length (cps "start")) by (simpl in *; lia).
      pose proof (Hg Hnx) as Hc. try rewrite E' in Hc. discriminate Hc.
  Qed.

  Lemma class_string : forall m, In (KString, m) (classes hs hc) -> m = string_len.
  Proof.
    intros m H. destruct (in_classes hs hc _ _ H) as
      [[Hk _]|[[Hk _]|[[_ Hm]|[[Hk _]|[[Hk _]|[[Hk _]|[[Hk _]|[[Hk _]|[Hk _]]]]]]]]];
      try discriminate. exact Hm.
  Qed.

  (* The token at the start of [x ++ z] is the token at the start of [x ++ z']
     when it ends inside [x] and both [z] and [z'] are empty or start with
     whitespace.  The two guards say when a comment or [start at] could reach
     into [z']: a comment token that ends with [x] needs a line break next, and
     [start] needs no [ at] after it. *)
  Theorem step_stab : forall x z z' k n,
    barb z = true -> barb z' = true -> x <> [] ->
    step hs hc (x ++ z) = (k, n) -> k <> KUnknown -> k <> KWhitespace ->
    n <= List.length x ->
    (forall x', x = 35 :: x' -> n = List.length x -> stops not_nl z' = true) ->
    (n = List.length x -> word_fits hc start_at (x ++ z') = false) ->
    step hs hc (x ++ z') = (k, n).
  Proof.
    intros x z z' k n Hz Hz' Hx Hs Hk Hkw Hn Gc Gs.
    rewrite <- Hs. apply lens_eq_step. intros k' m' Hin.
    pose proof (step_longest hs hc _ _ _ Hs k' m' Hin) as Hlong.
    destruct (step_class hs hc _ _ _ Hs Hk) as (pre & m & post & Hcl & Hm & _).
    assert (Hwin : In (k, m) (classes hs hc))
      by (rewrite Hcl; apply in_or_app; right; left; reflexivity).
    pose proof (step_pos hs hc _ _ _ Hs) as Hn0.
    destruct x as [|c x']; [contradiction|].
    destruct (head_class c (x' ++ z) k m Hwin ltac:(cbn [app] in Hm; rewrite Hm; exact Hn0))
      as (Hh35 & Hh34 & Hhws).
    assert (Hcws : is_ws c = false)
      by (destruct (is_ws c) eqn:E; [exfalso; apply Hkw; apply Hhws; reflexivity|reflexivity]).
    destruct (in_classes hs hc k' m' Hin) as
      [[_ ->]|[[_ ->]|[[_ ->]|[[_ ->]|[[_ ->]|[[_ [-> | ->]]|[[_ ->]|[[_ ->]|[_ ->]]]]]]]]].
    - unfold whitespace_len. cbn [app span]. rewrite Hcws. reflexivity.
    - apply comment_eq; [discriminate|exact (Nat.le_trans _ _ _ Hlong Hn)|].
      intros Hc.
      assert (Hc35 : c = 35).
      { destruct (c =? 35) eqn:E35; [apply Nat.eqb_eq; exact E35|].
        exfalso. unfold comment_len in Hc. cbn [app] in Hc. rewrite E35 in Hc.
        cbn [List.length] in Hc. discriminate. }
      subst c. apply (Gc x' eq_refl).
      rewrite Hc in Hlong. exact (Nat.le_antisymm _ _ Hn Hlong).
    - apply string_eq; [discriminate|exact (Nat.le_trans _ _ _ Hlong Hn)|].
      intros x'' Hx''. inversion Hx''; subst c x''.
      specialize (Hh34 eq_refl). subst k.
      rewrite (class_string m Hwin) in Hm. intro Hz0. apply Hn0. rewrite <- Hm. exact Hz0.
    - rewrite (number_stable (c :: x') z Hz), (number_stable (c :: x') z' Hz'). reflexivity.
    - rewrite (word_len_stable hc literals (c :: x') z literals_wsfree Hz),
              (word_len_stable hc literals (c :: x') z' literals_wsfree Hz'). reflexivity.
    - rewrite (word_len_stable hc _ (c :: x') z keywords_wsfree Hz),
              (word_len_stable hc _ (c :: x') z' keywords_wsfree Hz'). reflexivity.
    - apply startat_eq with (n := n); try assumption.
      exact (step_longest hs hc _ _ _ Hs KName _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))).
    - unfold name_len. rewrite (name_sm_stable hs hc (c :: x') z None Hz),
                               (name_sm_stable hs hc (c :: x') z' None Hz'). reflexivity.
    - rewrite (prefix_len_stable operators (c :: x') z operators_wsfree Hz),
              (prefix_len_stable operators (c :: x') z' operators_wsfree Hz'). reflexivity.
    - rewrite (prefix_len_stable puncts (c :: x') z puncts_wsfree Hz),
              (prefix_len_stable puncts (c :: x') z' puncts_wsfree Hz'). reflexivity.
  Qed.

End Stab.
