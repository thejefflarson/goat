(* A whitespace edit leaves the token stream alone (phase 8, stage 1).

   The formatter ([editor/format.goat], ADR 0041) returns edits that replace a
   gap of whitespace with other whitespace, and the host refuses an edit over a
   byte that is not whitespace.  That check does not say a token cannot merge
   with its neighbour or a comment swallow the next line: a comment followed by
   a space instead of a line break does the second, and [start] followed by one
   space before [at] does the first.  This file says exactly when an edit is
   safe.

   [edit1 ts ts'] replaces one whitespace token of the lexed [ts] by a non-empty
   run of whitespace.  The run must keep a line break after a comment and must
   not make [start at] out of a token [start] and the next token ([gap_guard]).
   [Edits] is any number of such edits; [edits_preserve_tokens] says the text of
   the result lexes to the result, so its tokens other than whitespace are the
   tokens of the original, and [edits_preserve_parse] says it parses the same.

   Inserting or deleting a gap (an edit over an empty range, or one that leaves
   no whitespace) can join two tokens or split one, and is not covered here: the
   theorem is about the gaps the source already has.  The text must lex without
   an unrecognized code point, which is the only text the formatter edits. *)

From Stdlib Require Import List String Ascii Arith Bool Lia Relations.Relation_Operators.
Import ListNotations.
Require Import Goat.GoatLex.
Require Import Goat.GoatLexSpec.
Require Import Goat.GoatLexBarrier.
Require Import Goat.GoatLexStep.
Require Import Goat.GoatLexText.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

Definition nonU (t : token) : Prop := kd t <> KUnknown.

Definition ws_gap (g : list nat) : Prop := g <> [] /\ forallb is_ws g = true.

(* A gap of [newlines] line breaks and then [indent] spaces: what an edit of
   the formatter writes. *)
Definition gap_of (newlines indent : nat) : list nat :=
  repeat 10 newlines ++ repeat 32 indent.

Lemma gap_of_ws : forall newlines indent,
  0 < newlines + indent -> ws_gap (gap_of newlines indent).
Proof.
  intros nl ind H. unfold gap_of, ws_gap. split.
  - destruct nl; simpl; [destruct ind; [lia|discriminate]|discriminate].
  - rewrite forallb_app. apply andb_true_iff. split;
      apply forallb_forall; intros c Hc;
      [apply repeat_spec in Hc|apply repeat_spec in Hc]; subst; reflexivity.
Qed.

Lemma stops_app : forall p g B,
  g <> [] -> stops p g = true -> stops p (g ++ B) = true.
Proof. intros p [|c g] B H Hs; [contradiction|]. exact Hs. Qed.

Lemma flat_map_nil_tokens : forall (ts : list token),
  Forall (fun t => tx t <> []) ts -> flat_map tx ts = [] -> ts = [].
Proof.
  intros ts H E. destruct ts as [|t ts]; [reflexivity|].
  inversion H; subst. simpl in E. destruct (tx t); [contradiction|discriminate].
Qed.

Section Edit.
  Variables (hs hc : nat -> bool).

  Inductive Steps : list nat -> list token -> Prop :=
    | StepsNil : Steps [] []
    | StepsCons : forall r k n ts, r <> [] -> step hs hc r = (k, n) ->
        Steps (skipn n r) ts -> Steps r (mk k (firstn n r) :: ts).

  Lemma steps_text : forall r ts, Steps r ts -> text ts = r.
  Proof.
    intros r ts H. induction H; [reflexivity|].
    unfold text in *. cbn [flat_map tx]. rewrite IHSteps. apply firstn_skipn.
  Qed.

  Lemma steps_nonempty : forall r ts, Steps r ts -> Forall (fun t => tx t <> []) ts.
  Proof.
    intros r ts H. induction H; [constructor|].
    constructor; [|exact IHSteps].
    simpl. pose proof (step_pos hs hc _ _ _ H0) as Hn.
    destruct r as [|c r']; [contradiction|]. destruct n as [|n]; [lia|]. discriminate.
  Qed.

  Lemma steps_inv : forall r t ts, Steps r (t :: ts) ->
    r <> [] /\ exists n, step hs hc r = (kd t, n) /\ tx t = firstn n r /\ Steps (skipn n r) ts.
  Proof.
    intros r t ts H. inversion H; subst. split; [assumption|].
    exists n. simpl. auto.
  Qed.

  Lemma lex_go_steps : forall fuel r, List.length r <= fuel -> Steps r (lex_go hs hc fuel r).
  Proof.
    induction fuel as [|f IH]; intros r Hl.
    - destruct r; [constructor|simpl in Hl; lia].
    - destruct r as [|c t]; [constructor|].
      assert (Hne : c :: t <> []) by discriminate.
      pose proof (step_range hs hc (c :: t) Hne) as Hr.
      cbn [lex_go]. destruct (step hs hc (c :: t)) as [k n] eqn:Es. simpl in Hr.
      econstructor; [exact Hne|exact Es|]. apply IH.
      rewrite length_skipn. cbn [List.length] in *. lia.
  Qed.

  Lemma steps_det : forall r ts1, Steps r ts1 -> forall ts2, Steps r ts2 -> ts1 = ts2.
  Proof.
    intros r ts1 H1.
    induction H1 as [|r k n ts Hne Hstep Hrest IH]; intros ts2 H2.
    - inversion H2 as [|r2 k2 n2 ts2' Hne2 Hstep2 Hrest2]; subst; [reflexivity|].
      exfalso. apply Hne2. reflexivity.
    - inversion H2 as [|r2 k2 n2 ts2' Hne2 Hstep2 Hrest2]; subst; [exfalso; apply Hne; reflexivity|].
      rewrite Hstep in Hstep2. inversion Hstep2; subst.
      f_equal. f_equal. apply IH. exact Hrest2.
  Qed.

  Lemma push_nonU : forall t acc, nonU t -> push t acc = t :: acc.
  Proof.
    intros t acc H. unfold push. destruct acc as [|u acc]; [reflexivity|].
    destruct (kind_eqb (kd t) KUnknown && kind_eqb (kd u) KUnknown) eqn:E; [|reflexivity].
    exfalso. apply andb_true_iff in E as [E _].
    unfold nonU in H. destruct (kd t); simpl in E; try discriminate. apply H. reflexivity.
  Qed.

  Lemma push_unknown : forall t acc, kd t = KUnknown ->
    exists u acc', push t acc = u :: acc' /\ kd u = KUnknown.
  Proof.
    intros t acc H. unfold push. destruct acc as [|u acc].
    - exists t, []. auto.
    - destruct (kind_eqb (kd t) KUnknown && kind_eqb (kd u) KUnknown) eqn:E.
      + exists (mk KUnknown (tx t ++ tx u)), acc. split; reflexivity.
      + exists t, (u :: acc). auto.
  Qed.

  Lemma fold_push_nonU : forall l,
    Forall nonU (fold_right push [] l) -> fold_right push [] l = l /\ Forall nonU l.
  Proof.
    induction l as [|t l IH]; intro H; [split; [reflexivity|constructor]|].
    cbn [fold_right] in *.
    destruct (kd t) eqn:Ekd; try (
      destruct (push_unknown t (fold_right push [] l) Ekd) as (u & acc' & Hp & Hu);
      rewrite Hp in H; inversion H; subst; exfalso; apply H2; exact Hu).
    all: rewrite (push_nonU t _ ltac:(unfold nonU; rewrite Ekd; discriminate)) in H;
      inversion H; subst; destruct (IH H3) as [E F];
      rewrite (push_nonU t _ ltac:(unfold nonU; rewrite Ekd; discriminate)), E;
      split; [reflexivity|constructor; [unfold nonU; rewrite Ekd; discriminate|exact F]].
  Qed.

  Lemma fold_push_id : forall l, Forall nonU l -> fold_right push [] l = l.
  Proof.
    induction l as [|t l IH]; intro H; [reflexivity|].
    inversion H; subst. cbn [fold_right]. rewrite (IH H3). apply push_nonU. exact H2.
  Qed.

  (* The text of a stepwise tokenization without unknown tokens lexes to it. *)
  Lemma steps_lex : forall ts,
    Steps (text ts) ts -> Forall nonU ts -> lex hs hc (text ts) = ts.
  Proof.
    intros ts Hs Hn. unfold lex.
    assert (Hg := lex_go_steps (List.length (text ts)) (text ts) (Nat.le_refl _)).
    rewrite (steps_det _ _ Hg ts Hs). apply fold_push_id. exact Hn.
  Qed.

  Lemma lex_steps : forall s,
    Forall nonU (lex hs hc s) -> Steps s (lex hs hc s).
  Proof.
    intros s H. unfold lex in *.
    destruct (fold_push_nonU _ H) as [E _]. rewrite E.
    apply lex_go_steps. lia.
  Qed.

  Lemma ws_token_all : forall r n,
    step hs hc r = (KWhitespace, n) -> forallb is_ws (firstn n r) = true.
  Proof.
    intros r n H.
    destruct (step_class hs hc _ _ _ H ltac:(discriminate)) as (pre & m & post & Hcl & Hm & _).
    assert (Hin : In (KWhitespace, m) (classes hs hc))
      by (rewrite Hcl; apply in_or_app; right; left; reflexivity).
    destruct (in_classes hs hc _ _ Hin) as
      [[_ Hm1]|[[Hk _]|[[Hk _]|[[Hk _]|[[Hk _]|[[Hk _]|[[Hk _]|[[Hk _]|[Hk _]]]]]]]]];
      try discriminate. subst m. unfold whitespace_len in Hm. rewrite <- Hm.
    clear. induction r as [|c t IH]; [reflexivity|]. simpl.
    destruct (is_ws c) eqn:E; simpl; [rewrite E; exact IH|reflexivity].
  Qed.

  Definition wsok (t : token) : Prop := kd t = KWhitespace -> ws_gap (tx t).

  Lemma steps_wsok : forall r ts, Steps r ts -> Forall wsok ts.
  Proof.
    intros r ts H. induction H; [constructor|].
    constructor; [|exact IHSteps].
    unfold wsok. simpl. intro Hk. subst k. split.
    - pose proof (step_pos hs hc _ _ _ H0) as Hn.
      destruct r as [|c r']; [contradiction|]. destruct n as [|n]; [lia|]. discriminate.
    - exact (ws_token_all _ _ H0).
  Qed.

  Lemma span_all : forall p a, forallb p a = true -> span p a = List.length a.
  Proof.
    induction a as [|c t IH]; intro H; [reflexivity|].
    simpl in H. apply andb_true_iff in H as [Hc Ht]. simpl. rewrite Hc, (IH Ht). reflexivity.
  Qed.

  (* A non-empty run of whitespace that no whitespace follows is one token. *)
  Lemma step_ws_run : forall g T,
    ws_gap g -> stops is_ws T = true ->
    step hs hc (g ++ T) = (KWhitespace, List.length g).
  Proof.
    intros g T [Hne Hall] HT.
    destruct g as [|c g']; [contradiction|].
    simpl in Hall. apply andb_true_iff in Hall as [Hc Hg'].
    cbn [app]. rewrite (step_ws hs hc c (g' ++ T) Hc).
    cbn [span]. rewrite Hc.
    assert (E : span is_ws (g' ++ T) = List.length g').
    { rewrite (span_stable is_ws g' T HT). apply span_all. exact Hg'. }
    rewrite E. reflexivity.
  Qed.

  Lemma skipn_len_app : forall (a b : list nat), skipn (List.length a) (a ++ b) = b.
  Proof. induction a; simpl; auto. Qed.

  Lemma firstn_len_app : forall (a b : list nat), firstn (List.length a) (a ++ b) = a.
  Proof. induction a; simpl; [reflexivity|]. intro b. rewrite IHa. reflexivity. Qed.

  (* What an edit may not do to the token before the gap it changes. *)
  Definition guard_p (p : token) (g' : list nat) (B : list token) : Prop :=
    (forall x', tx p = 35 :: x' -> stops not_nl g' = true) /\
    word_fits hc start_at (tx p ++ g' ++ text B) = false.

  Fixpoint gap_guard (A : list token) (g' : list nat) (B : list token) : Prop :=
    match A with
    | [] => True
    | [p] => guard_p p g' B
    | _ :: A' => gap_guard A' g' B
    end.

  Lemma gap_guard_cons : forall t A' g' B,
    gap_guard (t :: A') g' B ->
    (A' = [] -> guard_p t g' B) /\ gap_guard A' g' B.
  Proof.
    intros t [|a A''] g' B H; simpl in H; [split; [auto|exact I]|].
    split; [intro E; discriminate|exact H].
  Qed.

  Lemma steps_cons_intro : forall tt R ts kt,
    tt <> [] -> step hs hc (tt ++ R) = (kt, List.length tt) -> Steps R ts ->
    Steps (tt ++ R) (mk kt tt :: ts).
  Proof.
    intros tt R ts kt Hne Hstep Hs.
    replace (mk kt tt) with (mk kt (firstn (List.length tt) (tt ++ R)))
      by (rewrite firstn_len_app; reflexivity).
    econstructor.
    - destruct tt; [contradiction|discriminate].
    - exact Hstep.
    - rewrite skipn_len_app. exact Hs.
  Qed.

  Lemma barb_gap : forall g B, ws_gap g -> barb (g ++ B) = true.
  Proof.
    intros g B [Hne Hall]. destruct g as [|c g0]; [contradiction|].
    simpl in Hall |- *. exact (proj1 (andb_prop _ _ Hall)).
  Qed.

  (* The token before the gap, and the tokens between it and the gap, lex as
     they did when the gap is replaced. *)
  Lemma step_keep : forall tt A' g g' B kt,
    tt <> [] -> Forall (fun t => tx t <> []) A' -> kt <> KUnknown ->
    ws_gap g -> ws_gap g' -> (A' = [] -> guard_p (mk kt tt) g' B) ->
    step hs hc (tt ++ flat_map tx (A' ++ mk KWhitespace g :: B)) = (kt, List.length tt) ->
    step hs hc (tt ++ flat_map tx (A' ++ mk KWhitespace g' :: B)) = (kt, List.length tt).
  Proof.
    intros tt A' g g' B kt Htt HA Hku Hg Hg' Hgd Hstep.
    destruct (kind_eqb kt KWhitespace) eqn:Ekw.
    - destruct kt; simpl in Ekw; try discriminate. clear Ekw.
      pose proof (ws_token_all _ _ Hstep) as Hall. rewrite firstn_len_app in Hall.
      assert (Hgt : ws_gap tt) by (split; assumption).
      pose proof (whitespace_maximal hs hc _ _ Hstep) as Hmax.
      rewrite skipn_len_app in Hmax.
      destruct A' as [|a1 A''].
      + exfalso. cbn [app flat_map tx] in Hmax.
        destruct Hg as [Hgne Hgall]. destruct g as [|c g0]; [contradiction|].
        simpl in Hmax, Hgall. rewrite (proj1 (andb_prop _ _ Hgall)) in Hmax. discriminate.
      + inversion HA as [|? ? Hna _]; subst.
        cbn [app flat_map] in Hmax |- *.
        destruct (tx a1) as [|c1 T1]; [contradiction|].
        cbn [app] in Hmax |- *.
        assert (HT : stops is_ws (c1 :: T1 ++ flat_map tx (A'' ++ mk KWhitespace g' :: B)) = true)
          by (simpl; rewrite Hmax; reflexivity).
        exact (step_ws_run tt _ Hgt HT).
    - assert (Hkw : kt <> KWhitespace) by (destruct kt; simpl in Ekw; try discriminate; intro; discriminate).
      assert (E1 : forall h, tt ++ flat_map tx (A' ++ mk KWhitespace h :: B)
                     = (tt ++ flat_map tx A') ++ (h ++ flat_map tx B))
        by (intro h; rewrite flat_map_app; cbn [flat_map tx]; rewrite !app_assoc; reflexivity).
      rewrite E1 in Hstep |- *.
      assert (Hxne : tt ++ flat_map tx A' <> []) by (destruct tt; [contradiction|discriminate]).
      assert (HA0 : List.length tt = List.length (tt ++ flat_map tx A') -> A' = []).
      { intro E. rewrite length_app in E.
        assert (Hl0 : List.length (flat_map tx A') = 0) by lia.
        apply length_zero_iff_nil in Hl0. exact (flat_map_nil_tokens _ HA Hl0). }
      apply (step_stab hs hc (tt ++ flat_map tx A') (g ++ flat_map tx B) (g' ++ flat_map tx B)
               kt (List.length tt) (barb_gap g _ Hg) (barb_gap g' _ Hg') Hxne Hstep Hku Hkw
               ltac:(rewrite length_app; lia)).
      + intros x' Hx35 Hn. pose proof (HA0 Hn) as E. subst A'.
        destruct (Hgd eq_refl) as [Hc _]. cbn [flat_map] in Hx35. rewrite app_nil_r in Hx35.
        apply stops_app; [destruct Hg' as [H0 _]; exact H0|exact (Hc x' Hx35)].
      + intro Hn. pose proof (HA0 Hn) as E. subst A'.
        destruct (Hgd eq_refl) as [_ Hs]. cbn [flat_map]. rewrite app_nil_r.
        cbn [tx] in Hs. unfold text in Hs. exact Hs.
  Qed.

  Lemma replace_gap : forall A g g' B,
    Steps (text (A ++ mk KWhitespace g :: B)) (A ++ mk KWhitespace g :: B) ->
    Forall nonU A -> ws_gap g -> ws_gap g' -> gap_guard A g' B ->
    Steps (text (A ++ mk KWhitespace g' :: B)) (A ++ mk KWhitespace g' :: B).
  Proof.
    induction A as [|[kt tt] A' IH]; intros g g' B Hs HnU Hg Hg' Hguard.
    - cbn [app] in *. unfold text in Hs |- *. cbn [flat_map tx] in *.
      destruct (steps_inv _ _ _ Hs) as (Hne & n & Hstep & Htx & Hrest).
      simpl in Htx.
      assert (Hn : n = List.length g).
      { assert (Hr := step_range hs hc _ Hne). rewrite Hstep in Hr. simpl in Hr.
        assert (Hl := f_equal (@List.length nat) Htx). rewrite length_firstn in Hl. lia. }
      subst n. rewrite skipn_len_app in Hrest.
      pose proof (whitespace_maximal hs hc _ _ Hstep) as Hmax.
      rewrite skipn_len_app in Hmax.
      assert (HT : stops is_ws (flat_map tx B) = true)
        by (destruct (flat_map tx B) as [|c T]; [reflexivity|]; simpl in Hmax |- *; rewrite Hmax; reflexivity).
      refine (steps_cons_intro g' _ _ KWhitespace ltac:(destruct Hg' as [H0 _]; exact H0) (step_ws_run g' _ Hg' HT) Hrest).
    - inversion HnU as [|? ? HnU1 HnU2]; subst.
      cbn [app] in Hs |- *. unfold text in Hs |- *. cbn [flat_map] in Hs |- *.
      destruct (steps_inv _ _ _ Hs) as (Hne & n & Hstep & Htx & Hrest).
      cbn [kd tx] in Hstep, Htx, Hne, Hrest.
      assert (Hn : n = List.length tt).
      { assert (Hr := step_range hs hc _ Hne). rewrite Hstep in Hr. simpl in Hr.
        assert (Hl := f_equal (@List.length nat) Htx). rewrite length_firstn in Hl. lia. }
      subst n. rewrite skipn_len_app in Hrest.
      destruct (gap_guard_cons _ _ _ _ Hguard) as [Hg1 Hg2].
      pose proof (steps_nonempty _ _ Hs) as Hne1. inversion Hne1 as [|? ? Hnt Hne2]; subst.
      cbn [tx] in Hnt.
      assert (Hrest' : Steps (flat_map tx (A' ++ mk KWhitespace g' :: B)) (A' ++ mk KWhitespace g' :: B)).
      { exact (IH g g' B Hrest HnU2 Hg Hg' Hg2). }
      apply Forall_app in Hne2 as [HA _].
      exact (steps_cons_intro tt _ _ kt Hnt (step_keep tt A' g g' B kt Hnt HA HnU1 Hg Hg' Hg1 Hstep) Hrest').
  Qed.

  (* One edit: a whitespace token of the lexed text becomes another non-empty
     run of whitespace that keeps a comment on its own line and does not make
     [start at]. *)
  Definition edit1 (ts ts' : list token) : Prop :=
    exists A g g' B,
      ts = A ++ mk KWhitespace g :: B /\ ts' = A ++ mk KWhitespace g' :: B /\
      ws_gap g' /\ gap_guard A g' B.

  Definition Edits : list token -> list token -> Prop := clos_refl_trans _ edit1.

  Definition Good (ts : list token) : Prop :=
    Steps (text ts) ts /\ Forall nonU ts /\ Forall wsok ts.

  Lemma edit1_good : forall ts ts', Good ts -> edit1 ts ts' -> Good ts'.
  Proof.
    intros ts ts' (Hs & Hn & Hw) (A & g & g' & B & -> & -> & Hg' & Hguard).
    apply Forall_app in Hw as [HwA Hwr]. inversion Hwr as [|? ? Hwg HwB]; subst.
    apply Forall_app in Hn as [HnA Hnr]. inversion Hnr as [|? ? Hng HnB]; subst.
    assert (Hg : ws_gap g) by exact (Hwg eq_refl).
    refine (conj (replace_gap A g g' B Hs HnA Hg Hg' Hguard) (conj _ _)).
    - apply Forall_app. split; [exact HnA|constructor; [unfold nonU; simpl; discriminate|exact HnB]].
    - apply Forall_app. split; [exact HwA|constructor; [intros _; exact Hg'|exact HwB]].
  Qed.

  Lemma edits_good : forall ts ts', Edits ts ts' -> Good ts -> Good ts'.
  Proof.
    intros ts ts' H. induction H as [x y Hxy|x|x y z _ IH1 _ IH2]; intro Hg.
    - exact (edit1_good x y Hg Hxy).
    - exact Hg.
    - exact (IH2 (IH1 Hg)).
  Qed.

  Lemma edit1_sigs : forall ts ts', edit1 ts ts' -> sigs ts' = sigs ts.
  Proof.
    intros ts ts' (A & g & g' & B & -> & -> & _). unfold sigs.
    rewrite !filter_app. reflexivity.
  Qed.

  Lemma edits_sigs : forall ts ts', Edits ts ts' -> sigs ts' = sigs ts.
  Proof.
    intros ts ts' H. induction H as [x y Hxy|x|x y z _ IH1 _ IH2].
    - exact (edit1_sigs x y Hxy).
    - reflexivity.
    - rewrite IH2, IH1. reflexivity.
  Qed.

  Lemma good_lex : forall s, Forall nonU (lex hs hc s) -> Good (lex hs hc s).
  Proof.
    intros s H. unfold Good. rewrite lex_concat.
    pose proof (lex_steps s H) as Hs.
    exact (conj Hs (conj H (steps_wsok _ _ Hs))).
  Qed.

  (* Replacing whitespace tokens, one after another, by whitespace that keeps
     each comment on its own line and does not make [start at], leaves the
     other tokens of the text as they were: the text of the result lexes to the
     result. *)
  Theorem edits_preserve_tokens : forall s ts',
    Forall nonU (lex hs hc s) -> Edits (lex hs hc s) ts' ->
    lex hs hc (text ts') = ts' /\ sigs (lex hs hc (text ts')) = sigs (lex hs hc s).
  Proof.
    intros s ts' Hn He.
    destruct (edits_good _ _ He (good_lex s Hn)) as (Hs & Hn' & _).
    assert (Hl : lex hs hc (text ts') = ts') by exact (steps_lex ts' Hs Hn').
    split; [exact Hl|]. rewrite Hl. exact (edits_sigs _ _ He).
  Qed.

  Lemma nontrivia_sigs : forall l,
    nontrivia l = filter (fun t => negb (kind_eqb (kd t) KComment)) (sigs l).
  Proof.
    induction l as [|t l IH]; [reflexivity|].
    unfold nontrivia, sigs, is_trivia in *. cbn [filter].
    destruct (kind_eqb (kd t) KWhitespace) eqn:E1; destruct (kind_eqb (kd t) KComment) eqn:E2;
      simpl; rewrite ?E1, ?E2; simpl; try rewrite IH; reflexivity.
  Qed.

  (* The parser sees the same tokens, so the program parses to the same trees. *)
  Corollary edits_preserve_parse : forall s ts',
    Forall nonU (lex hs hc s) -> Edits (lex hs hc s) ts' ->
    lex_toks hs hc (text ts') = lex_toks hs hc s /\
    (forall tr, parse_text hs hc (text ts') tr <-> parse_text hs hc s tr).
  Proof.
    intros s ts' Hn He.
    destruct (edits_preserve_tokens s ts' Hn He) as [_ Hsig].
    assert (Hnt : nontrivia (lex hs hc (text ts')) = nontrivia (lex hs hc s))
      by (rewrite !nontrivia_sigs, Hsig; reflexivity).
    split; [exact (lex_toks_trivia_independent hs hc _ _ Hnt)|].
    intro tr. split; intro H.
    - exact (parse_text_trivia_independent hs hc _ _ tr Hnt H).
    - exact (parse_text_trivia_independent hs hc _ _ tr (eq_sym Hnt) H).
  Qed.
End Edit.

