(* What makes [lex] a lexer (phase 8, stage 1): no gap and no overlap, the
   longest match, and word boundaries.  Every theorem holds for any answer of
   the two Unicode predicates. *)

From Stdlib Require Import List String Ascii Arith Bool Lia.
Import ListNotations.
Require Import Goat.GoatLex.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

Lemma ws_cases : forall c, is_ws c = true -> c = 32 \/ c = 9 \/ c = 10 \/ c = 13.
Proof.
  intros c H. unfold is_ws in H.
  repeat rewrite orb_true_iff in H. repeat rewrite Nat.eqb_eq in H. tauto.
Qed.

Section Bounds.
  Variables (hs hc : nat -> bool).

  Lemma xs_ws : forall c, is_ws c = true -> xs hs c = false.
  Proof using hs. intros c H. destruct (ws_cases c H) as [-> | [-> | [-> | ->]]]; reflexivity. Qed.

  Lemma xc_ws : forall c, is_ws c = true -> xc hc c = false.
  Proof using hc. intros c H. destruct (ws_cases c H) as [-> | [-> | [-> | ->]]]; reflexivity. Qed.

  Lemma span_le : forall p r, span p r <= List.length r.
  Proof. intros p r. induction r as [|c t IH]; simpl; [lia|]. destruct (p c); lia. Qed.

  Lemma string_body_le : forall r esc n, string_body esc r = Some n -> n <= List.length r.
  Proof.
    induction r as [|c t IH]; intros esc n H; [discriminate|].
    cbn [string_body] in H.
    destruct esc.
    - destruct (string_body false t) as [m|] eqn:E; cbn [option_map] in H; [|discriminate].
      inversion H; subst. apply IH in E. simpl; lia.
    - destruct (c =? 34); [inversion H; simpl; lia|].
      destruct (string_body (c =? 92) t) as [m|] eqn:E; cbn [option_map] in H; [|discriminate].
      inversion H; subst. apply IH in E. simpl; lia.
  Qed.

  Lemma comment_le : forall r, comment_len r <= List.length r.
  Proof.
    intros [|c t]; simpl; [lia|].
    destruct (c =? 35); [|lia]. pose proof (span_le not_nl t). lia.
  Qed.

  Lemma string_le : forall r, string_len r <= List.length r.
  Proof.
    intros [|c t]; simpl; [lia|].
    destruct (c =? 34); [|lia].
    destruct (string_body false t) as [n|] eqn:E; [|lia].
    apply string_body_le in E. lia.
  Qed.

  Lemma frac_le : forall r, frac_len r <= List.length r.
  Proof.
    intros [|c t]; simpl; [lia|].
    destruct (c =? 46); [|lia]. pose proof (span_le is_digit t). lia.
  Qed.

  Lemma exp_le : forall r, exp_len r <= List.length r.
  Proof.
    intros [|c t]; simpl; [lia|].
    destruct ((c =? 101) || (c =? 69)); [|lia].
    assert (Hsg : exp_sign t <= List.length t)
      by (unfold exp_sign; destruct t as [|d t']; simpl; [lia|]; destruct ((d =? 43) || (d =? 45)); lia).
    pose proof (span_le is_digit (skipn (exp_sign t) t)) as H. rewrite length_skipn in H.
    destruct (0 <? span is_digit (skipn (exp_sign t) t)); lia.
  Qed.

  Lemma mant_le : forall r, mant_len r <= List.length r.
  Proof.
    intro r. unfold mant_len. pose proof (span_le is_digit r) as Hw.
    destruct (0 <? span is_digit r).
    - pose proof (frac_le (skipn (span is_digit r) r)) as Hf. rewrite length_skipn in Hf. lia.
    - destruct r as [|c t]; [simpl; lia|].
      destruct (c =? 46); [|simpl; lia].
      pose proof (span_le is_digit t) as Hd.
      destruct (0 <? span is_digit t); simpl in *; lia.
  Qed.

  Lemma number_le : forall r, number_len r <= List.length r.
  Proof.
    intro r. unfold number_len. pose proof (mant_le r) as Hm.
    destruct (mant_len r =? 0); [lia|].
    pose proof (exp_le (skipn (mant_len r) r)) as He. rewrite length_skipn in He. lia.
  Qed.

  Lemma name_sm_le : forall r st, name_sm hs hc st r <= List.length r.
  Proof.
    induction r as [|c t IH]; intro st; [destruct st as [[|?]|]; simpl; lia|].
    destruct st as [[|k]|]; cbn [name_sm List.length].
    - destruct (xs hs c); [|lia]. specialize (IH (Some name_run)). lia.
    - destruct (xc hc c); [specialize (IH (Some k)); lia|].
      destruct (xs hs c); [|lia]. specialize (IH (Some name_run)). lia.
    - destruct (xs hs c); [|lia]. specialize (IH (Some name_run)). lia.
  Qed.

  Lemma prefixb_le : forall w r, prefixb w r = true -> List.length w <= List.length r.
  Proof.
    induction w as [|a w IH]; intros [|b r] H; simpl in *; try lia; try discriminate.
    apply andb_true_iff in H as [_ H]. apply IH in H. lia.
  Qed.

  Lemma fold_max_le : forall l a N,
    a <= N -> Forall (fun x => x <= N) l -> fold_left Nat.max l a <= N.
  Proof.
    induction l as [|x l IH]; intros a N Ha HF; simpl; [exact Ha|].
    inversion HF; subst. apply IH; [|assumption]. apply Nat.max_lub; assumption.
  Qed.

  Lemma word_le : forall ws r, word_len hc ws r <= List.length r.
  Proof.
    intros ws r. unfold word_len. apply fold_max_le; [lia|].
    apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (w & <- & _).
    destruct (word_fits hc w r) eqn:E; [|lia].
    unfold word_fits in E. apply andb_true_iff in E as [E _]. exact (prefixb_le _ _ E).
  Qed.

  Lemma prefix_le : forall cs r, prefix_len cs r <= List.length r.
  Proof.
    intros cs r. unfold prefix_len. apply fold_max_le; [lia|].
    apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (w & <- & _).
    destruct (prefixb w r) eqn:E; [|lia]. exact (prefixb_le _ _ E).
  Qed.

  Lemma classes_le : forall k m, In (k, m) (classes hs hc) -> forall r, m r <= List.length r.
  Proof.
    intros k m H r. unfold classes in H. simpl in H.
    repeat (destruct H as [H|H]; [inversion H; subst; clear H|]);
      first [ contradiction
            | apply span_le | apply comment_le | apply string_le | apply number_le
            | apply word_le | apply name_sm_le | apply prefix_le ].
  Qed.

  Lemma pick_le : forall cl r N acc,
    snd acc <= N -> (forall k m, In (k, m) cl -> m r <= N) -> snd (pick cl r acc) <= N.
  Proof.
    induction cl as [|[k m] cl IH]; intros r N acc Hacc H; simpl; [exact Hacc|].
    assert (Hm : m r <= N) by exact (H k m (or_introl eq_refl)).
    apply IH.
    - destruct (snd acc <? m r); simpl; lia.
    - intros k' m' Hin. exact (H k' m' (or_intror Hin)).
  Qed.

  Lemma step_range : forall r, r <> [] ->
    1 <= snd (step hs hc r) <= List.length r.
  Proof.
    intros r Hr. unfold step.
    destruct (pick (classes hs hc) r (KUnknown, 0)) as [k n] eqn:E.
    assert (Hn : n <= List.length r).
    { change n with (snd (k, n)). rewrite <- E. apply pick_le; [simpl; lia|].
      intros k' m' Hin. apply (classes_le k' m' Hin). }
    destruct (n =? 0) eqn:E0; simpl.
    - destruct r; [contradiction|]. simpl. lia.
    - apply Nat.eqb_neq in E0. lia.
  Qed.

End Bounds.

Section Tiling.
  Variables (hs hc : nat -> bool).

  Lemma lex_go_concat : forall fuel r,
    List.length r <= fuel -> text (lex_go hs hc fuel r) = r.
  Proof.
    induction fuel as [|f IH]; intros r Hl.
    - destruct r; [reflexivity|simpl in Hl; lia].
    - destruct r as [|c t]; [reflexivity|].
      assert (Hne : c :: t <> []) by discriminate.
      pose proof (step_range hs hc (c :: t) Hne) as Hr.
      cbn [lex_go].
      destruct (step hs hc (c :: t)) as [k n] eqn:Es. simpl in Hr.
      unfold text in *. cbn [flat_map tx].
      rewrite (IH (skipn n (c :: t))).
      + apply firstn_skipn.
      + rewrite length_skipn. cbn [List.length] in *. lia.
  Qed.

  Lemma push_text : forall t acc, text (push t acc) = tx t ++ text acc.
  Proof.
    intros t [|u acc]; unfold push; [reflexivity|].
    destruct (kind_eqb (kd t) KUnknown && kind_eqb (kd u) KUnknown);
      unfold text; cbn [flat_map tx]; [|reflexivity].
    simpl. rewrite app_assoc. reflexivity.
  Qed.

  Lemma merge_text : forall ts, text (fold_right push [] ts) = text ts.
  Proof.
    induction ts as [|t ts IH]; [reflexivity|].
    cbn [fold_right]. rewrite push_text, IH. reflexivity.
  Qed.

  (* No gap and no overlap: the tokens, in order, spell the source. *)
  Theorem lex_concat : forall s, text (lex hs hc s) = s.
  Proof.
    intro s. unfold lex. rewrite merge_text. apply lex_go_concat. lia.
  Qed.

  Lemma lex_go_nonempty : forall fuel r,
    Forall (fun t => tx t <> []) (lex_go hs hc fuel r).
  Proof.
    induction fuel as [|f IH]; intros r; [constructor|].
    destruct r as [|c t]; [constructor|].
    assert (Hne : c :: t <> []) by discriminate.
    pose proof (step_range hs hc (c :: t) Hne) as Hr.
    cbn [lex_go]. destruct (step hs hc (c :: t)) as [k n] eqn:Es. simpl in Hr.
    constructor; [|apply IH].
    simpl. destruct n as [|n]; [lia|]. cbn [firstn]. discriminate.
  Qed.

  Lemma push_nonempty : forall t acc,
    tx t <> [] -> Forall (fun u => tx u <> []) acc ->
    Forall (fun u => tx u <> []) (push t acc).
  Proof.
    intros t [|u acc] Ht Hacc; unfold push; [constructor; [exact Ht|constructor]|].
    inversion Hacc; subst.
    destruct (kind_eqb (kd t) KUnknown && kind_eqb (kd u) KUnknown);
      constructor; try assumption.
    simpl. destruct (tx t); [contradiction|]. discriminate.
  Qed.

  Lemma merge_nonempty : forall ts,
    Forall (fun t => tx t <> []) ts ->
    Forall (fun t => tx t <> []) (fold_right push [] ts).
  Proof.
    induction ts as [|t ts IH]; intro H; [constructor|].
    inversion H; subst. cbn [fold_right]. apply push_nonempty; auto.
  Qed.

  (* Every token spans at least one code point, so the spans are a partition
     of the source into non-empty consecutive ranges. *)
  Theorem lex_nonempty : forall s, Forall (fun t => tx t <> []) (lex hs hc s).
  Proof. intro s. apply merge_nonempty, lex_go_nonempty. Qed.

End Tiling.

Section Longest.
  Variables (hs hc : nat -> bool).

  Lemma pick_spec : forall cl r acc k n,
    pick cl r acc = (k, n) ->
    (forall k' m, In (k', m) cl -> m r <= n) /\ snd acc <= n /\
    ((k, n) = acc \/
     exists pre m post, cl = pre ++ (k, m) :: post /\ m r = n /\ snd acc < n /\
       forall k' m', In (k', m') pre -> m' r < n).
  Proof.
    induction cl as [|[k0 m0] cl IH]; intros r acc k n H.
    - simpl in H. subst. repeat split; [intros; contradiction|simpl; lia|left; reflexivity].
    - cbn [pick] in H.
      destruct (snd acc <? m0 r) eqn:Elt.
      + apply Nat.ltb_lt in Elt.
        destruct (IH r _ _ _ H) as (Hall & Hacc & Hcase). simpl in Hacc.
        repeat split.
        * intros k' m' [Hin|Hin]; [inversion Hin; subst; lia|exact (Hall k' m' Hin)].
        * lia.
        * destruct Hcase as [Heq|(pre & m & post & Hcl & Hm & Hlt & Hpre)].
          -- right. inversion Heq; subst. exists [], m0, cl. simpl in *.
             repeat split; [lia|intros; contradiction].
          -- right. exists ((k0, m0) :: pre), m, post. simpl in *.
             repeat split; [rewrite Hcl; reflexivity|exact Hm|lia|].
             intros k' m' [Hin|Hin]; [inversion Hin; subst; lia|exact (Hpre k' m' Hin)].
      + apply Nat.ltb_ge in Elt.
        destruct (IH r _ _ _ H) as (Hall & Hacc & Hcase).
        repeat split.
        * intros k' m' [Hin|Hin]; [inversion Hin; subst; lia|exact (Hall k' m' Hin)].
        * lia.
        * destruct Hcase as [Heq|(pre & m & post & Hcl & Hm & Hlt & Hpre)].
          -- left. exact Heq.
          -- right. exists ((k0, m0) :: pre), m, post. simpl in *.
             repeat split; [rewrite Hcl; reflexivity|exact Hm|lia|].
             intros k' m' [Hin|Hin]; [inversion Hin; subst; lia|exact (Hpre k' m' Hin)].
  Qed.

  (* The token is the longest any class matches. *)
  Theorem step_longest : forall r k n,
    step hs hc r = (k, n) ->
    forall k' m, In (k', m) (classes hs hc) -> m r <= n.
  Proof.
    intros r k n H k' m Hin. unfold step in H.
    destruct (pick (classes hs hc) r (KUnknown, 0)) as [k1 n1] eqn:E.
    destruct (pick_spec _ _ _ _ _ E) as (Hall & _ & _).
    pose proof (Hall k' m Hin) as Hm.
    destruct (n1 =? 0) eqn:E0; [apply Nat.eqb_eq in E0|]; inversion H; subst; lia.
  Qed.

  (* A class that matches the token's length, no earlier class matches that
     much, and a code point no class matches is a token of unknown kind. *)
  Theorem step_class : forall r k n,
    step hs hc r = (k, n) -> k <> KUnknown ->
    exists pre m post,
      classes hs hc = pre ++ (k, m) :: post /\ m r = n /\
      forall k' m', In (k', m') pre -> m' r < n.
  Proof.
    intros r k n H Hk. unfold step in H.
    destruct (pick (classes hs hc) r (KUnknown, 0)) as [k1 n1] eqn:E.
    destruct (pick_spec _ _ _ _ _ E) as (_ & _ & Hcase).
    destruct (n1 =? 0) eqn:E0.
    - inversion H; subst. contradiction.
    - inversion H; subst.
      destruct Hcase as [Heq|(pre & m & post & Hcl & Hm & _ & Hpre)].
      + inversion Heq; subst. simpl in E0. discriminate.
      + exists pre, m, post. repeat split; assumption.
  Qed.

  Theorem step_unknown : forall r,
    (forall k m, In (k, m) (classes hs hc) -> m r = 0) ->
    step hs hc r = (KUnknown, 1).
  Proof.
    intros r H. unfold step.
    destruct (pick (classes hs hc) r (KUnknown, 0)) as [k1 n1] eqn:E.
    destruct (pick_spec _ _ _ _ _ E) as (Hall & _ & Hcase).
    destruct (n1 =? 0) eqn:E0; [reflexivity|].
    apply Nat.eqb_neq in E0.
    destruct Hcase as [Heq|(pre & m & post & Hcl & Hm & _ & _)].
    - inversion Heq; subst. contradiction.
    - assert (Hin : In (k1, m) (classes hs hc)) by (rewrite Hcl; apply in_or_app; right; left; reflexivity).
      pose proof (H _ _ Hin). lia.
  Qed.

  Lemma in_classes : forall k m, In (k, m) (classes hs hc) ->
    (k = KWhitespace /\ m = whitespace_len) \/
    (k = KComment /\ m = comment_len) \/
    (k = KString /\ m = string_len) \/
    (k = KNumber /\ m = number_len) \/
    (k = KLiteral /\ m = word_len hc literals) \/
    (k = KKeyword /\ (m = word_len hc (fn_keywords ++ plain_keywords) \/ m = word_len hc [start_at])) \/
    (k = KName /\ m = name_len hs hc) \/
    (k = KOperator /\ m = prefix_len operators) \/
    (k = KPunct /\ m = prefix_len puncts).
  Proof.
    intros k m H. unfold classes in H. simpl in H.
    repeat (destruct H as [H|H]; [inversion H; subst; clear H|]);
      first [ contradiction | tauto ].
  Qed.

  Lemma fold_max_attained : forall l a n,
    fold_left Nat.max l a = n -> n = a \/ In n l.
  Proof.
    induction l as [|x l IH]; intros a n H; simpl in H; [left; auto|].
    destruct (IH _ _ H) as [E|E].
    - destruct (Nat.max_spec a x) as [[_ Hm]|[_ Hm]]; rewrite Hm in E;
        [right; left; symmetry; exact E|left; exact E].
    - right. right. exact E.
  Qed.

  Lemma word_len_spec : forall ws r n,
    word_len hc ws r = n -> n <> 0 ->
    exists w, In w ws /\ word_fits hc w r = true /\ List.length w = n.
  Proof.
    intros ws r n H Hn. unfold word_len in H.
    destruct (fold_max_attained _ _ _ H) as [E|E]; [lia|].
    apply in_map_iff in E as (w & Hw & Hin).
    exists w. destruct (word_fits hc w r) eqn:Ef; [|lia].
    repeat split; auto.
  Qed.

  Lemma step_pos : forall r k n, step hs hc r = (k, n) -> n <> 0.
  Proof.
    intros r k n H. unfold step in H.
    destruct (pick (classes hs hc) r (KUnknown, 0)) as [k1 n1] eqn:E.
    destruct (n1 =? 0) eqn:E0; inversion H; subst; [discriminate|].
    apply Nat.eqb_neq in E0. exact E0.
  Qed.

  (* Word boundary: a reserved word or [true]/[false] is never directly
     followed by an identifier character, so [done] is a keyword and [doner]
     is a name. *)
  Theorem word_boundary : forall r k n,
    step hs hc r = (k, n) -> (k = KKeyword \/ k = KLiteral) ->
    boundary hc n r = true.
  Proof.
    intros r k n H Hk.
    assert (Hu : k <> KUnknown) by (destruct Hk; subst; discriminate).
    destruct (step_class _ _ _ H Hu) as (pre & m & post & Hcl & Hm & _).
    assert (Hin : In (k, m) (classes hs hc)) by (rewrite Hcl; apply in_or_app; right; left; reflexivity).
    assert (Hn : n <> 0) by exact (step_pos _ _ _ H).
    destruct (in_classes _ _ Hin) as [[Hk1 _]|[[Hk1 _]|[[Hk1 _]|[[Hk1 _]|[[Hk1 Hm1]|[[Hk1 Hm1]|[[Hk1 _]|[[Hk1 _]|[Hk1 _]]]]]]]]];
      subst k; try (destruct Hk; discriminate).
    - subst m. destruct (word_len_spec _ _ _ Hm Hn) as (w & _ & Hf & Hl).
      unfold word_fits in Hf. apply andb_true_iff in Hf as [_ Hb]. rewrite <- Hl. exact Hb.
    - destruct Hm1 as [Hm1|Hm1]; subst m;
        destruct (word_len_spec _ _ _ Hm Hn) as (w & _ & Hf & Hl);
        unfold word_fits in Hf; apply andb_true_iff in Hf as [_ Hb]; rewrite <- Hl; exact Hb.
  Qed.

  Lemma name_sm_stop : forall r st n,
    name_sm hs hc st r = n ->
    match skipn n r with c :: _ => xs hs c = false | [] => True end.
  Proof.
    induction r as [|c t IH]; intros st n H; [simpl in H; subst; exact I|].
    cbn [name_sm] in H.
    destruct st as [[|k]|].
    - destruct (xs hs c) eqn:Exs; [|subst; simpl; exact Exs].
      subst n. simpl. exact (IH _ _ eq_refl).
    - destruct (xc hc c) eqn:Exc; [subst n; simpl; exact (IH _ _ eq_refl)|].
      destruct (xs hs c) eqn:Exs; [subst n; simpl; exact (IH _ _ eq_refl)|].
      subst n. simpl. exact Exs.
    - destruct (xs hs c) eqn:Exs; [|subst; simpl; exact Exs].
      subst n. simpl. exact (IH _ _ eq_refl).
  Qed.

  (* A name is maximal: no name-start character follows it. *)
  Theorem name_maximal : forall r n,
    step hs hc r = (KName, n) ->
    match skipn n r with c :: _ => xs hs c = false | [] => True end.
  Proof.
    intros r n H.
    destruct (step_class _ _ _ H ltac:(discriminate)) as (pre & m & post & Hcl & Hm & _).
    assert (Hin : In (KName, m) (classes hs hc)) by (rewrite Hcl; apply in_or_app; right; left; reflexivity).
    destruct (in_classes _ _ Hin) as [[Hk _]|[[Hk _]|[[Hk _]|[[Hk _]|[[Hk _]|[[Hk _]|[[_ Hm1]|[[Hk _]|[Hk _]]]]]]]]];
      try discriminate.
    subst m. exact (name_sm_stop _ _ _ Hm).
  Qed.

  Lemma span_stop : forall p r, match skipn (span p r) r with c :: _ => p c = false | [] => True end.
  Proof.
    intros p r. induction r as [|c t IH]; [exact I|]. simpl.
    destruct (p c) eqn:E; [exact IH|]. simpl. exact E.
  Qed.

  (* Whitespace is maximal: a whitespace token is never followed by whitespace. *)
  Theorem whitespace_maximal : forall r n,
    step hs hc r = (KWhitespace, n) ->
    match skipn n r with c :: _ => is_ws c = false | [] => True end.
  Proof.
    intros r n H.
    destruct (step_class _ _ _ H ltac:(discriminate)) as (pre & m & post & Hcl & Hm & _).
    assert (Hin : In (KWhitespace, m) (classes hs hc)) by (rewrite Hcl; apply in_or_app; right; left; reflexivity).
    destruct (in_classes _ _ Hin) as [[_ Hm1]|[[Hk _]|[[Hk _]|[[Hk _]|[[Hk _]|[[Hk _]|[[Hk _]|[[Hk _]|[Hk _]]]]]]]]];
      try discriminate.
    subst m. unfold whitespace_len in Hm. rewrite <- Hm. apply span_stop.
  Qed.

End Longest.

Section Examples.
  Variables (hs hc : nat -> bool).

  Example done_is_a_keyword :
    lex hs hc (cps "done") = [mk KKeyword (cps "done")].
  Proof. reflexivity. Qed.

  Example doner_is_a_name :
    lex hs hc (cps "doner") = [mk KName (cps "doner")].
  Proof. reflexivity. Qed.

  Example start_at_is_one_keyword :
    lex hs hc (cps "start at") = [mk KKeyword (cps "start at")].
  Proof. reflexivity. Qed.

  Example a_numeral_is_maximal :
    lex hs hc (cps "1.5e+3") = [mk KNumber (cps "1.5e+3")].
  Proof. reflexivity. Qed.

  Example five_minus_one :
    lex hs hc (cps "5 -1") =
      [mk KNumber (cps "5"); mk KWhitespace (cps " "); mk KOperator (cps "-");
       mk KNumber (cps "1")].
  Proof. reflexivity. Qed.

End Examples.
