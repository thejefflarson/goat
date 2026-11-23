(* Whitespace is a barrier (phase 8, stage 1): a class of token that never
   contains whitespace reads the input only up to the first whitespace code
   point, or the end.  Two inputs that agree up to a barrier give that class the
   same match.  The edit theorem ([GoatLexEdit.v]) rests on this: replacing a run
   of whitespace by another leaves every such token as it was. *)

From Stdlib Require Import List String Ascii Arith Bool Lia.
Import ListNotations.
Require Import Goat.GoatLex.
Require Import Goat.GoatLexSpec.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

(* [b] is empty or starts with whitespace. *)
Definition barb (b : list nat) : bool :=
  match b with [] => true | c :: _ => is_ws c end.

Definition stops (p : nat -> bool) (b : list nat) : bool :=
  match b with [] => true | c :: _ => negb (p c) end.

Lemma ws_neqb : forall c k, is_ws c = true -> is_ws k = false -> (c =? k) = false.
Proof.
  intros c k Hc Hk. destruct (c =? k) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. subst. rewrite Hc in Hk. discriminate.
Qed.

Lemma ws_digit : forall c, is_ws c = true -> is_digit c = false.
Proof. intros c H. destruct (ws_cases c H) as [-> | [-> | [-> | ->]]]; reflexivity. Qed.

Lemma ws_not_nl : forall c, is_ws c = true -> is_nl c = true \/ is_nl c = false.
Proof. intros c _. destruct (is_nl c); auto. Qed.

Lemma barb_stops : forall p b,
  (forall c, is_ws c = true -> p c = false) -> barb b = true -> stops p b = true.
Proof.
  intros p [|c b] Hp H; [reflexivity|]. simpl in *. rewrite (Hp c H). reflexivity.
Qed.

Lemma span_stable : forall p a b, stops p b = true -> span p (a ++ b) = span p a.
Proof.
  intros p. induction a as [|c t IH]; intros b H; simpl.
  - destruct b as [|d b']; [reflexivity|]. simpl in H |- *.
    destruct (p d); [discriminate|reflexivity].
  - destruct (p c); [rewrite (IH b H); reflexivity|reflexivity].
Qed.

(* A run that ends before the end of [a] ends there whatever follows. *)
Lemma span_stable_inside : forall p a b b',
  span p (a ++ b) < List.length a -> span p (a ++ b') = span p (a ++ b).
Proof.
  intros p. induction a as [|c t IH]; intros b b' H; simpl in *; [lia|].
  destruct (p c); [|reflexivity].
  assert (Ht : span p (t ++ b) < List.length t) by lia.
  rewrite (IH b b' Ht). reflexivity.
Qed.

(* A run that reaches the end of [a] and stops at once stops there again when
   what follows is empty or stops it. *)
Lemma span_stable_end : forall p a b b',
  span p (a ++ b) = List.length a -> stops p b' = true ->
  span p (a ++ b') = List.length a.
Proof.
  intros p a b b' H Hs.
  assert (Hall : span p a = List.length a).
  { assert (Hle := span_le p a). clear Hs.
    revert b H. induction a as [|c t IH]; intros b H; simpl in *; [reflexivity|].
    destruct (p c); [|discriminate].
    assert (Hlt : span p (t ++ b) = List.length t) by lia.
    rewrite (IH ltac:(pose proof (span_le p t); lia) b Hlt). reflexivity. }
  rewrite (span_stable p a b' Hs). exact Hall.
Qed.

Lemma skipn_app_le : forall n (a b : list nat),
  n <= List.length a -> skipn n (a ++ b) = skipn n a ++ b.
Proof.
  induction n as [|n IH]; intros a b H; [reflexivity|].
  destruct a as [|x a]; simpl in H; [lia|]. simpl. apply IH. lia.
Qed.

Section Stable.
  Variables (hs hc : nat -> bool).

  Lemma ws_span_digit : forall b, barb b = true -> stops is_digit b = true.
  Proof. intros b H. apply barb_stops; [exact ws_digit|exact H]. Qed.

  Lemma frac_stable : forall a b, barb b = true -> frac_len (a ++ b) = frac_len a.
  Proof.
    intros a b H. destruct a as [|c t]; simpl.
    - destruct b as [|d b']; [reflexivity|]. simpl in H |- *.
      rewrite (ws_neqb d 46 H eq_refl). reflexivity.
    - destruct (c =? 46); [|reflexivity].
      rewrite (span_stable is_digit t b (ws_span_digit b H)). reflexivity.
  Qed.

  Lemma exp_stable : forall a b, barb b = true -> exp_len (a ++ b) = exp_len a.
  Proof.
    intros a b H. destruct a as [|c t].
    - simpl. destruct b as [|d b']; [reflexivity|]. simpl in H |- *.
      rewrite (ws_neqb d 101 H eq_refl), (ws_neqb d 69 H eq_refl). reflexivity.
    - simpl. destruct ((c =? 101) || (c =? 69)); [|reflexivity].
      assert (Hsg : exp_sign (t ++ b) = exp_sign t).
      { unfold exp_sign. destruct t as [|d t']; [|reflexivity].
        simpl. destruct b as [|e b']; [reflexivity|]. simpl in H |- *.
        rewrite (ws_neqb e 43 H eq_refl), (ws_neqb e 45 H eq_refl). reflexivity. }
      rewrite Hsg.
      assert (Hle : exp_sign t <= List.length t).
      { unfold exp_sign. destruct t as [|d t']; simpl; [lia|].
        destruct ((d =? 43) || (d =? 45)); lia. }
      rewrite (skipn_app_le _ _ _ Hle).
      rewrite (span_stable is_digit (skipn (exp_sign t) t) b (ws_span_digit b H)).
      reflexivity.
  Qed.

  Lemma mant_stable : forall a b, barb b = true -> mant_len (a ++ b) = mant_len a.
  Proof.
    intros a b H. unfold mant_len.
    rewrite (span_stable is_digit a b (ws_span_digit b H)).
    destruct (0 <? span is_digit a) eqn:E0.
    - rewrite (skipn_app_le _ _ _ (span_le is_digit a)).
      rewrite (frac_stable (skipn (span is_digit a) a) b H). reflexivity.
    - destruct a as [|c t].
      + simpl. destruct b as [|d b']; [reflexivity|]. simpl in H |- *.
        rewrite (ws_neqb d 46 H eq_refl). reflexivity.
      + simpl. destruct (c =? 46); [|reflexivity].
        rewrite (span_stable is_digit t b (ws_span_digit b H)). reflexivity.
  Qed.

  Lemma number_stable : forall a b, barb b = true -> number_len (a ++ b) = number_len a.
  Proof.
    intros a b H. unfold number_len. rewrite (mant_stable a b H).
    destruct (mant_len a =? 0); [reflexivity|].
    rewrite (skipn_app_le _ _ _ (mant_le a)).
    rewrite (exp_stable (skipn (mant_len a) a) b H). reflexivity.
  Qed.

  Lemma name_sm_stable : forall a b st, barb b = true ->
    name_sm hs hc st (a ++ b) = name_sm hs hc st a.
  Proof.
    induction a as [|c t IH]; intros b st H.
    - simpl. destruct b as [|d b']; [reflexivity|]. simpl in H.
      cbn [name_sm]. rewrite (xs_ws hs d H), (xc_ws hc d H).
      destruct st as [[|k]|]; reflexivity.
    - cbn [app name_sm]. destruct st as [[|k]|]; cbn [name_sm];
        [| | ]; destruct (xs hs c); try rewrite (IH b _ H); try reflexivity;
        destruct (xc hc c); try rewrite (IH b _ H); try reflexivity.
  Qed.

  Lemma prefixb_stable : forall w a b,
    (forall c, In c w -> is_ws c = false) -> barb b = true ->
    prefixb w (a ++ b) = prefixb w a.
  Proof.
    induction w as [|x w IH]; intros a b Hw H; [reflexivity|].
    destruct a as [|y a].
    - simpl. destruct b as [|d b']; [reflexivity|]. simpl in H.
      assert (Hx : is_ws x = false) by (apply Hw; left; reflexivity).
      rewrite (Nat.eqb_sym x d), (ws_neqb d x H Hx). reflexivity.
    - simpl. destruct (x =? y); [|reflexivity]. simpl.
      apply IH; [intros c Hc; apply Hw; right; exact Hc|exact H].
  Qed.

  Lemma boundary_stable : forall n a b, n <= List.length a -> barb b = true ->
    boundary hc n (a ++ b) = boundary hc n a.
  Proof.
    intros n a b Hn H. unfold boundary. rewrite (skipn_app_le _ _ _ Hn).
    destruct (skipn n a) as [|c a']; simpl; [|reflexivity].
    destruct b as [|d b']; [reflexivity|]. simpl in H. rewrite (xc_ws hc d H). reflexivity.
  Qed.

  (* Words without whitespace. *)
  Definition wsfree (ws : list (list nat)) : Prop :=
    forall w c, In w ws -> In c w -> is_ws c = false.

  Lemma word_fits_stable : forall w a b,
    (forall c, In c w -> is_ws c = false) -> barb b = true ->
    word_fits hc w (a ++ b) = word_fits hc w a.
  Proof.
    intros w a b Hw H. unfold word_fits. rewrite (prefixb_stable w a b Hw H).
    destruct (prefixb w a) eqn:Ep; [|reflexivity].
    simpl. apply boundary_stable; [exact (prefixb_le _ _ Ep)|exact H].
  Qed.

  Lemma word_len_stable : forall ws a b, wsfree ws -> barb b = true ->
    word_len hc ws (a ++ b) = word_len hc ws a.
  Proof.
    intros ws a b Hws H. unfold word_len. f_equal.
    apply map_ext_in. intros w Hw.
    rewrite (word_fits_stable w a b (fun c => Hws w c Hw) H). reflexivity.
  Qed.

  Lemma prefix_len_stable : forall cs a b, wsfree cs -> barb b = true ->
    prefix_len cs (a ++ b) = prefix_len cs a.
  Proof.
    intros cs a b Hcs H. unfold prefix_len. f_equal.
    apply map_ext_in. intros w Hw.
    rewrite (prefixb_stable w a b (fun c => Hcs w c Hw) H). reflexivity.
  Qed.

  Lemma literals_wsfree : wsfree literals.
  Proof.
    intros w c Hw Hc. unfold literals in Hw. simpl in Hw.
    repeat (destruct Hw as [<-|Hw]; [simpl in Hc; repeat (destruct Hc as [<-|Hc]; [reflexivity|]); contradiction|]).
    contradiction.
  Qed.

  Lemma keywords_wsfree : wsfree (fn_keywords ++ plain_keywords).
  Proof.
    intros w c Hw Hc. unfold fn_keywords, plain_keywords in Hw. simpl in Hw.
    repeat (destruct Hw as [<-|Hw]; [simpl in Hc; repeat (destruct Hc as [<-|Hc]; [reflexivity|]); contradiction|]).
    contradiction.
  Qed.

  Lemma operators_wsfree : wsfree operators.
  Proof.
    intros w c Hw Hc. unfold operators in Hw. simpl in Hw.
    repeat (destruct Hw as [<-|Hw]; [simpl in Hc; repeat (destruct Hc as [<-|Hc]; [reflexivity|]); contradiction|]).
    contradiction.
  Qed.

  Lemma puncts_wsfree : wsfree puncts.
  Proof.
    intros w c Hw Hc. unfold puncts in Hw. simpl in Hw.
    repeat (destruct Hw as [<-|Hw]; [simpl in Hc; repeat (destruct Hc as [<-|Hc]; [reflexivity|]); contradiction|]).
    contradiction.
  Qed.

End Stable.
