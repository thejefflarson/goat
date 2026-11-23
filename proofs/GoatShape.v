(* The forests the generated grammar can produce for the core fragment, and the
   shape of the children of each core node (ADR 0030). [gen e ts] says the
   expression [e] can produce the forest [ts] using core rules only; it does not
   look at the input. *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatNum.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatPrec.
Require Import Goat.GoatDen.
From Stdlib Require Import Lia.
Open Scope string_scope.
Open Scope list_scope.

Definition core_rule (r : rule) : bool :=
  match r with
  | R_goat | R_expr | R_value | R_declaration | R_local | R_function | R_params
  | R_call | R_arguments | R_access | R_take | R_name | R_number | R_boolean | R_true_lit
  | R_false_lit | R_record | R_field | R_spread | R_string | R_conditional
  | R_destructure | R_record_pattern | R_rest_binding
  | R_plus | R_minus | R_multiply | R_floor_divide | R_divide | R_remainder
  | R_equal | R_not_equal | R_lte | R_lt | R_gte | R_gt
  | R_and_op | R_or_op | R_not_op | R_negation
  | R_tag_decl | R_tag_kw | R_group_name | R_tag_case | R_type_name | R_infer_type
  | R_list | R_match_expr | R_arm | R_pattern | R_labels | R_literal_pattern
  | R_repeat_loop | R_count_loop | R_each_loop | R_for_kw | R_from_kw | R_to_kw | R_in_kw
  | R_sequel => true
  | _ => false
  end.

Inductive gen : pexpr -> list tree -> Prop :=
  | G_text : forall s,
      gen (E_term (T_text s)) [Leaf (TSym s)]
  | G_word : forall s,
      contextual s = true -> gen (E_term (T_text s)) [Leaf (TName s)]
  | G_name : forall x,
      gen (E_term T_name) [Leaf (TName x)]
  | G_number : forall n,
      gen (E_term T_number) [Leaf (TNum n)]
  | G_decimal : forall d,
      gen (E_term T_number) [Leaf (TDec d)]
  | G_string :
      gen (E_term T_string) [Leaf TStr]
  | G_eoi :
      gen (E_term T_eoi) []
  | G_node : forall r cs,
      silent r = false -> core_rule r = true -> gen (body r) cs ->
      gen (E_rule r) [Node r cs]
  | G_splice : forall r ts,
      silent r = true -> gen (body r) ts ->
      gen (E_rule r) ts
  | G_seq : forall a b ts1 ts2,
      gen a ts1 -> gen b ts2 ->
      gen (E_seq a b) (ts1 ++ ts2)
  | G_alt_left : forall a b ts,
      gen a ts -> gen (E_alt a b) ts
  | G_alt_right : forall a b ts,
      gen b ts -> gen (E_alt a b) ts
  | G_star_nil : forall a,
      gen (E_star a) []
  | G_star_cons : forall a ts1 ts2,
      gen a ts1 -> gen (E_star a) ts2 ->
      gen (E_star a) (ts1 ++ ts2)
  | G_plus : forall a ts,
      gen (E_seq a (E_star a)) ts -> gen (E_plus a) ts
  | G_opt_some : forall a ts,
      gen a ts -> gen (E_opt a) ts
  | G_opt_none : forall a,
      gen (E_opt a) []
  | G_expect : forall a ts,
      gen a ts -> gen (E_expect a) ts.

(* ---- inversions ---- *)

Lemma gen_text_inv : forall {s ts},
  gen (E_term (T_text s)) ts -> contextual s = false -> ts = [Leaf (TSym s)].
Proof. intros s ts H Hc. inversion H; subst; [reflexivity | congruence]. Qed.

Ltac text_inv H :=
  let E := fresh in
  pose proof (gen_text_inv H ltac:(reflexivity)) as E; clear H; rename E into H.

Lemma gen_name_inv : forall {ts}, gen (E_term T_name) ts -> exists x, ts = [Leaf (TName x)].
Proof. intros ts H. inversion H. eauto. Qed.

Lemma gen_number_inv : forall {ts}, gen (E_term T_number) ts ->
  (exists n, ts = [Leaf (TNum n)]) \/ (exists d, ts = [Leaf (TDec d)]).
Proof. intros ts H. inversion H; eauto. Qed.

Lemma gen_node_inv : forall {r ts},
  gen (E_rule r) ts -> silent r = false ->
  exists cs, ts = [Node r cs] /\ core_rule r = true /\ gen (body r) cs.
Proof.
  intros r ts H Hsilent. inversion H; subst.
  - eauto.
  - congruence.
Qed.

Lemma gen_splice_inv : forall {r ts},
  gen (E_rule r) ts -> silent r = true -> gen (body r) ts.
Proof.
  intros r ts H Hsilent. inversion H; subst.
  - congruence.
  - assumption.
Qed.

Lemma gen_seq_inv : forall {a b ts},
  gen (E_seq a b) ts ->
  exists ts1 ts2, ts = ts1 ++ ts2 /\ gen a ts1 /\ gen b ts2.
Proof. intros a b ts H. inversion H; subst. eauto 6. Qed.

Lemma gen_alt_inv : forall {a b ts},
  gen (E_alt a b) ts -> gen a ts \/ gen b ts.
Proof. intros a b ts H. inversion H; subst; auto. Qed.

Lemma gen_opt_inv : forall {a ts},
  gen (E_opt a) ts -> gen a ts \/ ts = [].
Proof. intros a ts H. inversion H; subst; auto. Qed.

Lemma gen_plus_inv : forall {a ts},
  gen (E_plus a) ts -> gen (E_seq a (E_star a)) ts.
Proof. intros a ts H. inversion H; subst. assumption. Qed.

Lemma gen_expect_inv : forall {a ts}, gen (E_expect a) ts -> gen a ts.
Proof. intros a ts H. inversion H; subst. assumption. Qed.

Lemma gen_star_inv : forall {a ts},
  gen (E_star a) ts ->
  ts = [] \/ exists ts1 ts2, ts = ts1 ++ ts2 /\ gen a ts1 /\ gen (E_star a) ts2.
Proof.
  intros a ts H. inversion H; subst.
  - left. reflexivity.
  - right. eauto 6.
Qed.

(* A rule with no core derivation: a rule that makes a node but is outside the
   fragment contributes nothing. *)
Lemma gen_outside : forall {r ts},
  gen (E_rule r) ts -> silent r = false -> core_rule r = false -> False.
Proof.
  intros r ts H Hsilent Hcore.
  destruct (gen_node_inv H Hsilent) as (cs & _ & Hc & _).
  congruence.
Qed.

(* Induction on a star by its parts: the property holds of the empty forest and
   is preserved by prepending a forest the starred expression produces. *)
Lemma gen_star_ind : forall a (P : list tree -> Prop),
  P [] ->
  (forall ts1 ts2, gen a ts1 -> P ts2 -> P (ts1 ++ ts2)) ->
  forall ts, gen (E_star a) ts -> P ts.
Proof.
  intros a P Hnil Hcons ts H.
  remember (E_star a) as e eqn:Heq.
  induction H; try discriminate Heq.
  - exact Hnil.
  - injection Heq as <-.
    apply Hcons; [ assumption | apply IHgen2; reflexivity ].
Qed.

(* ---- the children of each core node ---- *)

Ltac text_leaf H := text_inv H; subst.

Tactic Notation "split_seq" hyp(H) "as" simple_intropattern(p) :=
  destruct (gen_seq_inv H) as p; clear H.

Lemma shape_name : forall cs,
  gen (body R_name) cs -> exists x, cs = [Leaf (TName x)].
Proof. intros cs H. exact (gen_name_inv H). Qed.

Lemma shape_number : forall cs,
  gen (body R_number) cs ->
  (exists n, cs = [Leaf (TNum n)]) \/ (exists d, cs = [Leaf (TDec d)]).
Proof. intros cs H. exact (gen_number_inv H). Qed.

(* a name node, as a child *)
Lemma gen_ident : forall ts,
  gen (E_rule R_name) ts -> exists x, ts = [ident x].
Proof.
  intros ts H.
  destruct (gen_node_inv H eq_refl) as (cs & -> & _ & Hbody).
  destruct (shape_name cs Hbody) as (x & ->).
  exists x. reflexivity.
Qed.

Lemma shape_access : forall cs,
  gen (body R_access) cs -> exists l, cs = [sym "."; ident l].
Proof.
  intros cs H. simpl in H.
  split_seq H as (ts1 & ts2 & -> & H1 & H2). text_leaf H1.
  apply gen_expect_inv in H2.
  destruct (gen_ident _ H2) as (l & ->).
  exists l. reflexivity.
Qed.

Lemma shape_take : forall cs,
  gen (body R_take) cs -> exists l, cs = [sym "::"; ident l].
Proof.
  intros cs H. simpl in H.
  split_seq H as (ts1 & ts2 & -> & H1 & H2). text_leaf H1.
  apply gen_expect_inv in H2.
  destruct (gen_ident _ H2) as (l & ->).
  exists l. reflexivity.
Qed.

Definition has (r : rule) (cs : list tree) : Prop :=
  exists c, In (Node r c) cs.

Ltac absurd_has H :=
  destruct H as (? & Hin); simpl in Hin;
  repeat (destruct Hin as [Hin | Hin]; [ discriminate Hin | ]);
  contradiction.

Lemma gen_node_of : forall {r ts},
  gen (E_rule r) ts -> silent r = false ->
  exists cs, ts = [Node r cs] /\ gen (body r) cs.
Proof.
  intros r ts H Hsilent.
  destruct (gen_node_inv H Hsilent) as (cs & Hts & _ & Hbody).
  exists cs. split; assumption.
Qed.

Lemma shape_declaration : forall cs,
  gen (body R_declaration) cs ->
  exists x c,
    cs = [ident x; sym "="; Node R_value c]
    \/ cs = [ident x; sym "="; Node R_value c; sym ";"].
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsx & ts1 & -> & Hx & H1).
  destruct (gen_ident _ Hx) as (x & ->).
  split_seq H1 as (tseq & ts2 & -> & Hseq & H2). text_leaf Hseq.
  split_seq H2 as (tsv & tssemi & -> & Hv & Hsemi).
  apply gen_expect_inv in Hv.
  destruct (gen_alt_inv Hv) as [Hforeign | Hvalue].
  - exfalso. exact (gen_outside Hforeign eq_refl eq_refl).
  - destruct (gen_node_of Hvalue eq_refl) as (c & -> & _).
    exists x, c.
    destruct (gen_opt_inv Hsemi) as [Hs | ->].
    + text_inv Hs. subst. right. reflexivity.
    + left. reflexivity.
Qed.

Lemma shape_field : forall cs,
  gen (body R_field) cs ->
  exists l c, cs = [ident l; sym ":"; Node R_expr c].
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsl & ts1 & -> & Hl & H1).
  destruct (gen_ident _ Hl) as (l & ->).
  split_seq H1 as (tscolon & ts2 & -> & Hcolon & H2). text_leaf Hcolon.
  apply gen_expect_inv in H2.
  destruct (gen_node_of H2 eq_refl) as (c & -> & _).
  exists l, c. reflexivity.
Qed.

(* A parameter is a name or a record pattern; the fragment reads only names. *)
Definition not_pattern (t : tree) : Prop := forall c, t <> Node R_record_pattern c.

Lemma shape_param : forall ts,
  gen (E_rule R__param) ts -> Forall not_pattern ts -> exists x, ts = [ident x].
Proof.
  intros ts Hx Hplain.
  pose proof (gen_splice_inv Hx eq_refl) as Halt. simpl in Halt.
  destruct (gen_alt_inv Halt) as [Hrec | Hrest].
  - exfalso. destruct (gen_node_of Hrec eq_refl) as (c & -> & _).
    inversion Hplain as [| ? ? Hc _]; subst. exact (Hc c eq_refl).
  - destruct (gen_alt_inv Hrest) as [Hlist | Hname].
    + exfalso. exact (gen_outside Hlist eq_refl eq_refl).
    + exact (gen_ident _ Hname).
Qed.

Lemma shape_params : forall cs,
  gen (body R_params) cs -> Forall not_pattern cs ->
  exists x tail,
    cs = ident x :: tail
    /\ gen (E_star (E_seq (E_term (T_text ",")) (E_rule R__param))) tail
    /\ Forall not_pattern tail.
Proof.
  intros cs H Hplain. simpl in H.
  split_seq H as (tsx & tail & -> & Hx & Htail).
  apply Forall_app in Hplain as [Hplainx Hplaint].
  destruct (shape_param _ Hx Hplainx) as (x & ->).
  exists x, tail. split; [ reflexivity | split; assumption ].
Qed.

Lemma shape_arguments : forall cs,
  gen (body R_arguments) cs ->
  exists c tail fin,
    cs = Node R_expr c :: tail ++ fin
    /\ gen (E_star (E_seq (E_term (T_text ",")) (E_rule R_expr))) tail
    /\ (fin = [] \/ fin = [sym ","]).
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsa & ts1 & -> & Ha & H1).
  destruct (gen_node_of Ha eq_refl) as (c & -> & _).
  split_seq H1 as (tail & fin & -> & Htail & Hfin).
  exists c, tail, fin. split; [ reflexivity | split; [ exact Htail | ] ].
  destruct (gen_opt_inv Hfin) as [Hcomma | ->].
  - text_inv Hcomma. subst. right. reflexivity.
  - left. reflexivity.
Qed.

Lemma shape_call : forall cs,
  gen (body R_call) cs ->
  cs = [sym "("; sym ")"] \/ exists args, cs = [sym "("; Node R_arguments args; sym ")"].
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsl & ts1 & -> & Hl & H1). text_leaf Hl.
  split_seq H1 as (tsa & tsr & -> & Ha & Hr).
  apply gen_expect_inv in Hr. text_leaf Hr.
  destruct (gen_opt_inv Ha) as [Hargs | ->].
  - destruct (gen_node_of Hargs eq_refl) as (args & -> & _).
    right. exists args. reflexivity.
  - left. reflexivity.
Qed.

Definition loop_body_shape (bs : list tree) : Prop :=
  bs = [] \/ exists cb, bs = [Node R_expr cb].

Lemma gen_loop_body : forall ts, gen (E_opt (E_rule R_expr)) ts -> loop_body_shape ts.
Proof.
  intros ts H. destruct (gen_opt_inv H) as [Hbody | ->]; [ | left; reflexivity ].
  destruct (gen_node_of Hbody eq_refl) as (cb & -> & _). right. exists cb. reflexivity.
Qed.

Lemma shape_boolean : forall cs,
  gen (body R_boolean) cs ->
  cs = [Node R_true_lit [sym "true"]] \/ cs = [Node R_false_lit [sym "false"]].
Proof.
  intros cs H. simpl in H.
  destruct (gen_alt_inv H) as [Ht | Hf].
  - left. destruct (gen_node_of Ht eq_refl) as (c & -> & Hc).
    simpl in Hc. text_inv Hc. subst. reflexivity.
  - right. destruct (gen_node_of Hf eq_refl) as (c & -> & Hc).
    simpl in Hc. text_inv Hc. subst. reflexivity.
Qed.

Lemma shape_local : forall cs,
  gen (body R_local) cs ->
  exists d bs, cs = Node R_declaration d :: bs /\ loop_body_shape bs.
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsd & ts1 & -> & Hd & H1).
  destruct (gen_node_of Hd eq_refl) as (d & -> & _).
  exists d, ts1. split; [ reflexivity | exact (gen_loop_body ts1 H1) ].
Qed.

Lemma shape_function : forall cs,
  gen (body R_function) cs ->
  exists kw pso bs,
    cs = [Leaf kw; sym "("] ++ pso ++ [sym ")"; sym "do"] ++ bs ++ [sym "done"]
    /\ (pso = [] \/ exists ps, pso = [Node R_params ps])
    /\ loop_body_shape bs.
Proof.
  intros cs H. simpl in H.
  split_seq H as (tskw & ts1 & -> & Hkw & H1).
  split_seq H1 as (tsl & ts2 & -> & Hl & H2).
  apply gen_expect_inv in Hl. text_leaf Hl.
  split_seq H2 as (tsp & ts3 & -> & Hp & H3).
  split_seq H3 as (tsr & ts4 & -> & Hr & H4).
  apply gen_expect_inv in Hr. text_leaf Hr.
  split_seq H4 as (tsd & ts5 & -> & Hd & H5).
  apply gen_expect_inv in Hd. text_leaf Hd.
  split_seq H5 as (tsb & tsend & -> & Hb & Hend).
  apply gen_expect_inv in Hend. text_leaf Hend.
  assert (Hkw' : exists kw, tskw = [Leaf kw]).
  { destruct (gen_alt_inv Hkw) as [Hk | Hk].
    - text_inv Hk. eauto.
    - destruct (gen_alt_inv Hk) as [Hk' | Hk'];
        text_inv Hk'; eauto. }
  destruct Hkw' as (kw & ->).
  exists kw, tsp, tsb. split; [ reflexivity | split; [ | exact (gen_loop_body tsb Hb) ] ].
  destruct (gen_opt_inv Hp) as [Hps | ->]; [ | left; reflexivity ].
  destruct (gen_node_of Hps eq_refl) as (ps & -> & _).
  right. exists ps. reflexivity.
Qed.

Lemma shape_record_item : forall ts,
  gen (E_rule R__record_item) ts ->
  (exists c, ts = [Node R_field c]) \/ (exists c, ts = [Node R_spread c]).
Proof.
  intros ts H.
  pose proof (gen_splice_inv H eq_refl) as Halt. simpl in Halt.
  destruct (gen_alt_inv Halt) as [Hspread | Hfield].
  - destruct (gen_node_of Hspread eq_refl) as (c & -> & _).
    right. exists c. reflexivity.
  - destruct (gen_node_of Hfield eq_refl) as (c & -> & _).
    left. exists c. reflexivity.
Qed.

Lemma shape_spread : forall cs,
  gen (body R_spread) cs -> exists c, cs = [sym "..."; Node R_expr c].
Proof.
  intros cs H. simpl in H.
  split_seq H as (ts1 & ts2 & -> & H1 & H2). text_leaf H1.
  apply gen_expect_inv in H2.
  destruct (gen_node_of H2 eq_refl) as (c & -> & _).
  exists c. reflexivity.
Qed.

Lemma shape_record : forall cs,
  gen (body R_record) cs ->
  exists rest,
    cs = sym "{" :: rest
    /\ (rest = [sym "}"]
        \/ (exists c tail fin,
              rest = Node R_field c :: tail ++ fin ++ [sym "}"]
              /\ gen (E_star (E_seq (E_term (T_text ",")) (E_rule R__record_item))) tail
              /\ (fin = [] \/ fin = [sym ","]))
        \/ (exists c tail fin,
              rest = Node R_spread c :: tail ++ fin ++ [sym "}"]
              /\ gen (E_star (E_seq (E_term (T_text ",")) (E_rule R__record_item))) tail
              /\ (fin = [] \/ fin = [sym ","]))).
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsl & ts1 & -> & Hl & H1). text_leaf Hl.
  split_seq H1 as (tsi & tsr & -> & Hitems & Hr).
  apply gen_expect_inv in Hr. text_leaf Hr.
  destruct (gen_opt_inv Hitems) as [Hsome | ->].
  - split_seq Hsome as (tsf & ts2 & -> & Hf & H2).
    split_seq H2 as (tail & fin & -> & Htail & Hfin).
    assert (Hfin' : fin = [] \/ fin = [sym ","]).
    { destruct (gen_opt_inv Hfin) as [Hcomma | ->].
      - text_inv Hcomma. subst. right. reflexivity.
      - left. reflexivity. }
    destruct (shape_record_item _ Hf) as [(c & ->) | (c & ->)].
    + exists (Node R_field c :: tail ++ fin ++ [sym "}"]).
      split; [ simpl; rewrite <- app_assoc; reflexivity | right; left ].
      exists c, tail, fin. split; [ reflexivity | split; assumption ].
    + exists (Node R_spread c :: tail ++ fin ++ [sym "}"]).
      split; [ simpl; rewrite <- app_assoc; reflexivity | right; right ].
      exists c, tail, fin. split; [ reflexivity | split; assumption ].
  - exists [sym "}"]. split; [ reflexivity | left; reflexivity ].
Qed.

Lemma shape_rest_binding : forall ts,
  gen (E_rule R_rest_binding) ts -> exists r, ts = [rest_node r].
Proof.
  intros ts H.
  destruct (gen_node_of H eq_refl) as (cs & -> & Hbody). simpl in Hbody.
  split_seq Hbody as (ts1 & ts2 & -> & H1 & H2). text_leaf H1.
  destruct (gen_ident _ H2) as (r & ->).
  exists r. reflexivity.
Qed.

Lemma pat_more : forall star,
  gen (E_star (E_seq (E_term (T_text ",")) (E_rule R_name))) star ->
  forall opt_rest fin,
    (opt_rest = [] \/ exists r, opt_rest = [sym ","; rest_node r]) ->
    (fin = [] \/ fin = [sym ","]) ->
    exists xs ro, Den_pat_more (star ++ opt_rest ++ fin ++ [sym "}"]) xs ro.
Proof.
  intros star H.
  apply (gen_star_ind (E_seq (E_term (T_text ",")) (E_rule R_name))
           (fun star => forall opt_rest fin,
              (opt_rest = [] \/ exists r, opt_rest = [sym ","; rest_node r]) ->
              (fin = [] \/ fin = [sym ","]) ->
              exists xs ro, Den_pat_more (star ++ opt_rest ++ fin ++ [sym "}"]) xs ro));
    [ | | exact H ].
  - intros opt_rest fin Hopt Hfin. simpl.
    destruct Hopt as [-> | (r & ->)]; destruct Hfin as [-> | ->].
    + exists [], None. apply DPM_end.
    + exists [], None. apply DPM_trail.
    + exists [], (Some r). exact (DPM_rest r [] (or_introl eq_refl)).
    + exists [], (Some r). exact (DPM_rest r [sym ","] (or_intror eq_refl)).
  - intros ts1 ts2 Hstep IH opt_rest fin Hopt Hfin.
    split_seq Hstep as (tscomma & tsname & -> & Hcomma & Hname).
    text_inv Hcomma. subst.
    destruct (gen_ident _ Hname) as (y & ->).
    destruct (IH opt_rest fin Hopt Hfin) as (xs & ro & Hmore).
    exists (y :: xs), ro. simpl. apply DPM_name. exact Hmore.
Qed.

Lemma shape_record_pattern : forall cs,
  gen (body R_record_pattern) cs ->
  exists ps xs ro, cs = sym "{" :: ps /\ Den_pat_start ps xs ro.
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsl & ts1 & -> & Hl & H1). text_leaf Hl.
  split_seq H1 as (tsa & tsr & -> & Ha & Hr). text_leaf Hr.
  split_seq Ha as (tsb & tsc & -> & Hb & Hc).
  assert (Hfin : tsc = [] \/ tsc = [sym ","]).
  { destruct (gen_opt_inv Hc) as [Hcomma | ->].
    - text_inv Hcomma. subst. right. reflexivity.
    - left. reflexivity. }
  destruct (gen_alt_inv Hb) as [Hnamed | Hrest].
  - split_seq Hnamed as (tsx & ts3 & -> & Hx & H3).
    destruct (gen_ident _ Hx) as (x & ->).
    split_seq H3 as (tstar & topt & -> & Hstar & Hopt).
    assert (Hopt' : topt = [] \/ exists r, topt = [sym ","; rest_node r]).
    { destruct (gen_opt_inv Hopt) as [Hs | ->].
      - split_seq Hs as (tscomma & tsrest & -> & Hcomma & Hrest).
        text_inv Hcomma. subst.
        destruct (shape_rest_binding _ Hrest) as (r & ->).
        right. exists r. reflexivity.
      - left. reflexivity. }
    destruct (pat_more _ Hstar topt tsc Hopt' Hfin) as (xs & ro & Hmore).
    exists (ident x :: tstar ++ topt ++ tsc ++ [sym "}"]), (x :: xs), ro.
    split; [ simpl; rewrite <- ?app_assoc; reflexivity | ].
    apply DPS_name. exact Hmore.
  - destruct (shape_rest_binding _ Hrest) as (r & ->).
    exists (rest_node r :: tsc ++ [sym "}"]), [], (Some r).
    split; [ reflexivity | apply DPS_rest; exact Hfin ].
Qed.

Lemma shape_destructure : forall cs,
  gen (body R_destructure) cs ->
  exists ps xs ro vs semi bs,
    cs = [Node R_record_pattern (sym "{" :: ps); sym "="; Node R_value vs]
           ++ semi ++ bs
    /\ (semi = [] \/ semi = [sym ";"])
    /\ Den_pat_start ps xs ro
    /\ loop_body_shape bs.
Proof.
  intros cs H. simpl in H.
  split_seq H as (tspat & ts1 & -> & Hpat & H1).
  split_seq H1 as (tseq & ts2 & -> & Heq & H2). text_leaf Heq.
  split_seq H2 as (tsv & ts3 & -> & Hv & H3).
  split_seq H3 as (tssemi & tsb & -> & Hsemi & Hb).
  apply gen_expect_inv in Hv.
  destruct (gen_node_of Hv eq_refl) as (vs & -> & _).
  destruct (gen_alt_inv Hpat) as [Hrec | Hlist]; [ | exfalso; exact (gen_outside Hlist eq_refl eq_refl) ].
  destruct (gen_node_of Hrec eq_refl) as (cp & -> & Hbodyp).
  destruct (shape_record_pattern cp Hbodyp) as (ps & xs & ro & -> & Hps).
  destruct (gen_opt_inv Hsemi) as [Hs | ->].
  - text_inv Hs. subst.
    exists ps, xs, ro, vs, [sym ";"], tsb.
    split; [ reflexivity | split; [ right; reflexivity | split; [ exact Hps | exact (gen_loop_body tsb Hb) ] ] ].
  - exists ps, xs, ro, vs, [], tsb.
    split; [ reflexivity | split; [ left; reflexivity | split; [ exact Hps | exact (gen_loop_body tsb Hb) ] ] ].
Qed.

Lemma shape_string : forall cs, gen (body R_string) cs -> cs = [Leaf TStr].
Proof. intros cs H. simpl in H. inversion H. reflexivity. Qed.

Lemma shape_conditional : forall cs,
  gen (body R_conditional) cs ->
  (exists a b c,
     cs = [sym "if"; Node R_expr a; sym "then"; Node R_expr b; sym "else"; Node R_expr c;
           sym "done"])
  \/ (exists a b,
        cs = [sym "if"; Node R_expr a; sym "then"; Node R_expr b; sym "done"]).
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsif & ts1 & -> & Hif & H1). text_leaf Hif.
  split_seq H1 as (tsa & ts2 & -> & Ha & H2).
  destruct (gen_node_of Ha eq_refl) as (a & -> & _).
  split_seq H2 as (tsthen & ts3 & -> & Hthen & H3).
  apply gen_expect_inv in Hthen. text_leaf Hthen.
  split_seq H3 as (tsb & ts4 & -> & Hb & H4).
  apply gen_expect_inv in Hb.
  destruct (gen_node_of Hb eq_refl) as (b & -> & _).
  split_seq H4 as (tsel & tsdone & -> & Hel & Hdone).
  apply gen_expect_inv in Hdone. text_leaf Hdone.
  destruct (gen_opt_inv Hel) as [Helse | ->].
  - pose proof (gen_splice_inv Helse eq_refl) as Hbody. simpl in Hbody.
    split_seq Hbody as (tse & ts5 & -> & He & Hc). text_leaf He.
    apply gen_expect_inv in Hc.
    destruct (gen_node_of Hc eq_refl) as (c & -> & _).
    left. exists a, b, c. reflexivity.
  - right. exists a, b. reflexivity.
Qed.

(* A rule that is one spelled word: the keyword token, or for the contextual
   words the name token. *)
Lemma gen_word_inv : forall {w ts},
  gen (E_term (T_text w)) ts -> exists k, ts = [Leaf k] /\ word_tok w k.
Proof.
  intros w ts H. inversion H; subst.
  - exists (TSym w). split; [ reflexivity | right; reflexivity ].
  - exists (TName w). split; [ reflexivity | left; reflexivity ].
Qed.

Lemma shape_word : forall r w ts,
  silent r = false -> body r = E_term (T_text w) -> gen (E_rule r) ts ->
  exists k, ts = [Node r [Leaf k]] /\ word_tok w k.
Proof.
  intros r w ts Hs Hb H.
  destruct (gen_node_of H Hs) as (cs & -> & Hbody). rewrite Hb in Hbody.
  destruct (gen_word_inv Hbody) as (k & -> & Hk). exists k. split; [ reflexivity | exact Hk ].
Qed.

Lemma shape_for_kw : forall ts,
  gen (E_rule R_for_kw) ts -> ts = [Node R_for_kw [sym "for"]].
Proof.
  intros ts H.
  destruct (gen_node_of H eq_refl) as (cs & -> & Hbody). simpl in Hbody. text_leaf Hbody.
  reflexivity.
Qed.

Lemma shape_repeat : forall cs,
  gen (body R_repeat_loop) cs ->
  exists cn bs,
    cs = [sym "repeat"; Node R_expr cn; sym "times"; sym "do"] ++ bs ++ [sym "done"]
    /\ loop_body_shape bs.
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsr & ts1 & -> & Hr & H1). text_leaf Hr.
  split_seq H1 as (tse & ts2 & -> & He & H2). apply gen_expect_inv in He.
  destruct (gen_node_of He eq_refl) as (cn & -> & _).
  split_seq H2 as (tst & ts3 & -> & Ht & H3). apply gen_expect_inv in Ht. text_leaf Ht.
  split_seq H3 as (tsdo & ts4 & -> & Hdo & H4). apply gen_expect_inv in Hdo. text_leaf Hdo.
  split_seq H4 as (tsb & tsdone & -> & Hb & Hdone). apply gen_expect_inv in Hdone. text_leaf Hdone.
  exists cn, tsb. split; [ reflexivity | exact (gen_loop_body tsb Hb) ].
Qed.

Lemma shape_count : forall cs,
  gen (body R_count_loop) cs ->
  exists x kf kt ca cz bs,
    cs = [Node R_for_kw [sym "for"]; ident x; Node R_from_kw [Leaf kf]; Node R_expr ca;
          Node R_to_kw [Leaf kt]; Node R_expr cz; sym "do"] ++ bs ++ [sym "done"]
    /\ word_tok "from" kf /\ word_tok "to" kt /\ loop_body_shape bs.
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsf & ts1 & -> & Hf & H1). rewrite (shape_for_kw tsf Hf). clear Hf.
  split_seq H1 as (tsn & ts2 & -> & Hn & H2).
  destruct (gen_ident _ Hn) as (x & ->).
  split_seq H2 as (tsfrom & ts3 & -> & Hfrom & H3).
  destruct (shape_word R_from_kw "from" tsfrom eq_refl eq_refl Hfrom) as (kf & -> & Hkf).
  split_seq H3 as (tsa & ts4 & -> & Ha & H4). apply gen_expect_inv in Ha.
  destruct (gen_node_of Ha eq_refl) as (ca & -> & _).
  split_seq H4 as (tsto & ts5 & -> & Hto & H5). apply gen_expect_inv in Hto.
  destruct (shape_word R_to_kw "to" tsto eq_refl eq_refl Hto) as (kt & -> & Hkt).
  split_seq H5 as (tsz & ts6 & -> & Hz & H6). apply gen_expect_inv in Hz.
  destruct (gen_node_of Hz eq_refl) as (cz & -> & _).
  split_seq H6 as (tsdo & ts7 & -> & Hdo & H7). apply gen_expect_inv in Hdo. text_leaf Hdo.
  split_seq H7 as (tsb & tsdone & -> & Hb & Hdone). apply gen_expect_inv in Hdone. text_leaf Hdone.
  exists x, kf, kt, ca, cz, tsb.
  split; [ reflexivity | exact (conj Hkf (conj Hkt (gen_loop_body tsb Hb))) ].
Qed.

Lemma shape_each : forall cs,
  gen (body R_each_loop) cs ->
  exists x ki cl bs,
    cs = [Node R_for_kw [sym "for"]; ident x; Node R_in_kw [Leaf ki]; Node R_expr cl; sym "do"]
           ++ bs ++ [sym "done"]
    /\ word_tok "in" ki /\ loop_body_shape bs.
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsf & ts1 & -> & Hf & H1). rewrite (shape_for_kw tsf Hf). clear Hf.
  split_seq H1 as (tsn & ts2 & -> & Hn & H2).
  destruct (gen_ident _ Hn) as (x & ->).
  split_seq H2 as (tsin & ts3 & -> & Hin & H3).
  destruct (shape_word R_in_kw "in" tsin eq_refl eq_refl Hin) as (ki & -> & Hki).
  split_seq H3 as (tsl & ts4 & -> & Hl & H4). apply gen_expect_inv in Hl.
  destruct (gen_node_of Hl eq_refl) as (cl & -> & _).
  split_seq H4 as (tsdo & ts5 & -> & Hdo & H5). apply gen_expect_inv in Hdo. text_leaf Hdo.
  split_seq H5 as (tsb & tsdone & -> & Hb & Hdone). apply gen_expect_inv in Hdone. text_leaf Hdone.
  exists x, ki, cl, tsb.
  split; [ reflexivity | exact (conj Hki (gen_loop_body tsb Hb)) ].
Qed.

Lemma tag_decl_nodes : forall ds,
  gen (E_star (E_rule R_tag_decl)) ds ->
  Forall (fun t => exists c, t = Node R_tag_decl c) ds.
Proof.
  intros ds H.
  apply (gen_star_ind (E_rule R_tag_decl)); [ | | exact H ].
  - apply Forall_nil.
  - intros ts1 ts2 H1 IH.
    destruct (gen_node_of H1 eq_refl) as (c & -> & _).
    apply Forall_cons; [ eauto | exact IH ].
Qed.

Lemma shape_goat : forall cs,
  gen (body R_goat) cs ->
  exists decls bs,
    cs = decls ++ bs
    /\ Forall (fun t => exists c, t = Node R_tag_decl c) decls
    /\ loop_body_shape bs.
Proof.
  intros cs H. simpl in H.
  split_seq H as (tstags & ts1 & -> & Htags & H1).
  split_seq H1 as (tse & tseoi & -> & He & Heoi).
  inversion Heoi; subst.
  rewrite app_nil_r.
  exists tstags, tse. split; [ reflexivity | split; [ exact (tag_decl_nodes tstags Htags) | exact (gen_loop_body tse He) ] ].
Qed.

Lemma arm_nodes : forall ds,
  gen (E_star (E_rule R_arm)) ds ->
  Forall (fun t => exists c, t = Node R_arm c) ds.
Proof.
  intros ds H.
  apply (gen_star_ind (E_rule R_arm)); [ | | exact H ].
  - apply Forall_nil.
  - intros ts1 ts2 H1 IH.
    destruct (gen_node_of H1 eq_refl) as (c & -> & _).
    apply Forall_cons; [ eauto | exact IH ].
Qed.

Lemma shape_list : forall cs,
  gen (body R_list) cs ->
  cs = [sym "["; sym "]"] \/ exists args, cs = [sym "["; Node R_arguments args; sym "]"].
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsl & ts1 & -> & Hl & H1). text_leaf Hl.
  split_seq H1 as (tsa & tsr & -> & Ha & Hr).
  apply gen_expect_inv in Hr. text_leaf Hr.
  destruct (gen_opt_inv Ha) as [Hargs | ->].
  - destruct (gen_node_of Hargs eq_refl) as (args & -> & _).
    right. exists args. reflexivity.
  - left. reflexivity.
Qed.

Lemma labels_den : forall tail,
  gen (E_star (E_seq (E_term (T_text ",")) (E_rule R_name))) tail ->
  forall x, exists xs, Den_labels (ident x :: tail) (x :: xs).
Proof.
  intros tail H.
  apply (gen_star_ind (E_seq (E_term (T_text ",")) (E_rule R_name))
           (fun tail => forall x, exists xs, Den_labels (ident x :: tail) (x :: xs)));
    [ | | exact H ].
  - intros x. exists []. apply DLb_one.
  - intros ts1 ts2 Hstep IH x.
    split_seq Hstep as (tscomma & tsname & -> & Hcomma & Hname).
    text_inv Hcomma. subst.
    destruct (gen_ident _ Hname) as (y & ->).
    destruct (IH y) as (ys & Hys).
    exists (y :: ys). simpl. apply DLb_more. exact Hys.
Qed.

Lemma shape_labels : forall cs,
  gen (body R_labels) cs -> exists xs, Den_labels cs xs.
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsx & tail & -> & Hx & Htail).
  destruct (gen_ident _ Hx) as (x & ->).
  destruct (labels_den tail Htail x) as (xs & Hxs).
  exists (x :: xs). exact Hxs.
Qed.

Lemma shape_pattern : forall cs,
  gen (body R_pattern) cs -> exists t xs, Den_tpat cs t xs.
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsn & ts1 & -> & Hn & H1).
  destruct (gen_ident _ Hn) as (t & ->).
  destruct (gen_opt_inv H1) as [Hs | ->].
  - split_seq Hs as (tsl & ts2 & -> & Hl & H2). text_leaf Hl.
    split_seq H2 as (tsb & tsr & -> & Hb & Hr). text_leaf Hr.
    destruct (gen_opt_inv Hb) as [Hlab | ->].
    + destruct (gen_node_of Hlab eq_refl) as (ls & -> & Hbody).
      destruct (shape_labels ls Hbody) as (xs & Hxs).
      exists t, xs. exact (DTP_labels t ls xs Hxs).
    + exists t, []. exact (DTP_empty t).
  - exists t, []. exact (DTP_bare t).
Qed.

Lemma shape_literal_pattern : forall cs,
  gen (body R_literal_pattern) cs ->
  exists c x, cs = [c] /\ (c = Node R_number x \/ c = Node R_string x \/ c = Node R_boolean x).
Proof.
  intros cs H. simpl in H.
  destruct (gen_alt_inv H) as [Hn | H1].
  - destruct (gen_node_of Hn eq_refl) as (x & -> & _). exists (Node R_number x), x. auto.
  - destruct (gen_alt_inv H1) as [Hs | Hb].
    + destruct (gen_node_of Hs eq_refl) as (x & -> & _). exists (Node R_string x), x. auto.
    + destruct (gen_node_of Hb eq_refl) as (x & -> & _). exists (Node R_boolean x), x. auto.
Qed.

Lemma shape_arm : forall cs,
  gen (body R_arm) cs ->
  (exists p b, cs = [Node R_pattern p; sym "then"; Node R_expr b])
  \/ (exists p b, cs = [Node R_literal_pattern p; sym "then"; Node R_expr b]).
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsp & ts1 & -> & Hp & H1).
  split_seq H1 as (tsthen & tsb & -> & Hthen & Hb).
  apply gen_expect_inv in Hthen. text_leaf Hthen.
  apply gen_expect_inv in Hb.
  destruct (gen_node_of Hb eq_refl) as (b & -> & _).
  destruct (gen_alt_inv Hp) as [Hlist | Hp1]; [ exfalso; exact (gen_outside Hlist eq_refl eq_refl) | ].
  destruct (gen_alt_inv Hp1) as [Hlit | Hpat].
  - destruct (gen_node_of Hlit eq_refl) as (p & -> & _). right. exists p, b. reflexivity.
  - destruct (gen_node_of Hpat eq_refl) as (p & -> & _). left. exists p, b. reflexivity.
Qed.

Lemma shape_match : forall cs,
  gen (body R_match_expr) cs ->
  exists c arms els,
    cs = [sym "match"; Node R_expr c; sym "do"] ++ arms ++ els ++ [sym "done"]
    /\ gen (E_star (E_rule R_arm)) arms
    /\ (els = [] \/ exists c2, els = [sym "else"; Node R_expr c2]).
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsm & ts1 & -> & Hm & H1). text_leaf Hm.
  split_seq H1 as (tse & ts2 & -> & He & H2).
  apply gen_expect_inv in He.
  destruct (gen_node_of He eq_refl) as (c & -> & _).
  split_seq H2 as (tsdo & ts3 & -> & Hdo & H3).
  apply gen_expect_inv in Hdo. text_leaf Hdo.
  split_seq H3 as (tsarms & ts4 & -> & Harms & H4).
  split_seq H4 as (tsels & tsdone & -> & Hels & Hdone).
  apply gen_expect_inv in Hdone. text_leaf Hdone.
  exists c, tsarms, tsels. split; [ reflexivity | split; [ exact Harms | ] ].
  destruct (gen_opt_inv Hels) as [Helse | ->].
  - right.
    pose proof (gen_splice_inv Helse eq_refl) as Hbody. simpl in Hbody.
    split_seq Hbody as (tse2 & ts5 & -> & He2 & Hc). text_leaf He2.
    apply gen_expect_inv in Hc.
    destruct (gen_node_of Hc eq_refl) as (c2 & -> & _).
    exists c2. reflexivity.
  - left. reflexivity.
Qed.

(* ---- expressions: a block is declarations and then a chain ---- *)

Ltac dead :=
  match goal with
  | H : gen (E_rule _) _ |- False => exact (gen_outside H eq_refl eq_refl)
  end.

Ltac op_case H o :=
  destruct (gen_node_of H eq_refl) as (? & -> & Hc);
  simpl in Hc; text_inv Hc; subst; exists o; split; [ reflexivity | discriminate ].

Ltac infix_step Halt o :=
  destruct (gen_alt_inv Halt) as [Hh | Halt']; [ op_case Hh o | clear Halt; rename Halt' into Halt ].

Lemma infix_shape : forall ts,
  gen (E_rule R__infix) ts -> exists o, ts = [lop_tree o] /\ o <> L_not.
Proof.
  intros ts H.
  pose proof (gen_splice_inv H eq_refl) as Halt. simpl in Halt.
  infix_step Halt L_and.
  infix_step Halt L_or.
  infix_step Halt (L_bin bop_add).
  infix_step Halt (L_bin bop_sub).
  infix_step Halt (L_bin bop_mul).
  infix_step Halt (L_bin bop_fdiv).
  infix_step Halt (L_bin bop_div).
  infix_step Halt (L_bin bop_rem).
  infix_step Halt (L_bin bop_eq).
  infix_step Halt (L_bin bop_ne).
  infix_step Halt (L_bin bop_lte).
  infix_step Halt (L_bin bop_lt).
  infix_step Halt (L_bin bop_gte).
  op_case Halt (L_bin bop_gt).
Qed.

Lemma more_math_shape : forall ts,
  gen (E_rule R__more_math) ts ->
  exists o c2, ts = lop_tree o :: c2 /\ o <> L_not /\ gen (E_rule R__operand) c2.
Proof.
  intros ts H.
  pose proof (gen_splice_inv H eq_refl) as Hseq. simpl in Hseq.
  split_seq Hseq as (tsi & ts1 & -> & Hinfix & Hop).
  destruct (infix_shape _ Hinfix) as (o & -> & Hne).
  apply gen_expect_inv in Hop.
  exists o, ts1. split; [ reflexivity | split; [ exact Hne | exact Hop ] ].
Qed.

Lemma operand_shape : forall cs,
  gen (E_rule R__operand) cs ->
  exists nots t,
    cs = nots ++ t
    /\ gen (E_star (E_rule R_not_op)) nots
    /\ gen (E_rule R__term) t.
Proof.
  intros cs H.
  pose proof (gen_splice_inv H eq_refl) as Hseq. simpl in Hseq.
  split_seq Hseq as (nots & t & -> & Hnots & Hterm).
  exists nots, t. split; [ reflexivity | split; assumption ].
Qed.

Lemma term_shape : forall cs,
  gen (E_rule R__term) cs ->
  (exists c, cs = [Node R_negation c])
  \/ (exists prim posts,
        cs = prim ++ posts
        /\ gen (E_rule R__primary) prim
        /\ gen (E_star (E_rule R__postfix)) posts).
Proof.
  intros cs H.
  pose proof (gen_splice_inv H eq_refl) as Halt. simpl in Halt.
  destruct (gen_alt_inv Halt) as [Hneg | Hseq].
  - left. destruct (gen_node_of Hneg eq_refl) as (c & -> & _). eauto.
  - right. split_seq Hseq as (prim & posts & -> & Hprim & Hposts).
    exists prim, posts. split; [ reflexivity | split; assumption ].
Qed.

(* A negation takes a nested negation, or a primary and its postfixes. *)
Lemma negation_shape : forall cs,
  gen (body R_negation) cs ->
  (exists c, cs = [op_tree bop_sub; Node R_negation c])
  \/ (exists chain,
        cs = op_tree bop_sub :: chain
        /\ gen (E_seq (E_rule R__primary) (E_star (E_rule R__postfix))) chain).
Proof.
  intros cs H. simpl in H.
  split_seq H as (tsm & ts1 & -> & Hminus & Hrest).
  destruct (gen_node_of Hminus eq_refl) as (c & -> & Hc). simpl in Hc. text_inv Hc. subst.
  destruct (gen_alt_inv Hrest) as [Hneg | Hchain].
  - left. destruct (gen_node_of Hneg eq_refl) as (c & -> & _). exists c. reflexivity.
  - right. eexists. split; [ reflexivity | exact Hchain ].
Qed.

Lemma primary_shape : forall prim,
  gen (E_rule R__primary) prim ->
  (exists c, prim = [Node R_number c])
  \/ (exists c, prim = [Node R_string c])
  \/ (exists c, prim = [Node R_boolean c])
  \/ (exists c, prim = [Node R_conditional c])
  \/ (exists c, prim = [Node R_local c])
  \/ (exists c, prim = [Node R_function c])
  \/ (exists c, prim = [Node R_record c])
  \/ (exists c, prim = [Node R_name c])
  \/ (exists c, prim = [sym "("; Node R_expr c; sym ")"])
  \/ (exists c, prim = [Node R_destructure c])
  \/ (exists c, prim = [Node R_list c])
  \/ (exists c, prim = [Node R_match_expr c])
  \/ (exists c, prim = [Node R_repeat_loop c])
  \/ (exists c, prim = [Node R_count_loop c])
  \/ (exists c, prim = [Node R_each_loop c]).
Proof.
  intros prim H.
  pose proof (gen_splice_inv H eq_refl) as Halt. simpl in Halt.
  destruct (gen_alt_inv Halt) as [Hnumber | Halt1].
  { destruct (gen_node_of Hnumber eq_refl) as (c & -> & _). left. eauto. }
  destruct (gen_alt_inv Halt1) as [Hstring | Halt2].
  { destruct (gen_node_of Hstring eq_refl) as (c & -> & _). right; left. eauto. }
  destruct (gen_alt_inv Halt2) as [Hboolean | Halt3].
  { destruct (gen_node_of Hboolean eq_refl) as (c & -> & _). right; right; left. eauto. }
  destruct (gen_alt_inv Halt3) as [Hdestructure | Halt4].
  { destruct (gen_node_of Hdestructure eq_refl) as (c & -> & _).
    right; right; right; right; right; right; right; right; right. left. eauto. }
  destruct (gen_alt_inv Halt4) as [Hlocal | Halt5].
  { destruct (gen_node_of Hlocal eq_refl) as (c & -> & _). right; right; right; right; left. eauto. }
  destruct (gen_alt_inv Halt5) as [Hfunction | Halt6].
  { destruct (gen_node_of Hfunction eq_refl) as (c & -> & _).
    right; right; right; right; right; left. eauto. }
  destruct (gen_alt_inv Halt6) as [Hconditional | Halt7].
  { destruct (gen_node_of Hconditional eq_refl) as (c & -> & _).
    right; right; right; left. eauto. }
  destruct (gen_alt_inv Halt7) as [Hmatch | Halt8].
  { destruct (gen_node_of Hmatch eq_refl) as (c & -> & _).
    right; right; right; right; right; right; right; right; right; right; right. left. eauto. }
  destruct (gen_alt_inv Halt8) as [Hrepeat | Halt9].
  { destruct (gen_node_of Hrepeat eq_refl) as (c & -> & _).
    right; right; right; right; right; right; right; right; right; right; right.
    right; left. eauto. }
  destruct (gen_alt_inv Halt9) as [Hcount | Halt10].
  { destruct (gen_node_of Hcount eq_refl) as (c & -> & _).
    right; right; right; right; right; right; right; right; right; right; right.
    right; right; left. eauto. }
  destruct (gen_alt_inv Halt10) as [Heach | Halt11].
  { destruct (gen_node_of Heach eq_refl) as (c & -> & _).
    right; right; right; right; right; right; right; right; right; right; right.
    right; right; right. eauto. }
  destruct (gen_alt_inv Halt11) as [Hrecord | Halt12].
  { destruct (gen_node_of Hrecord eq_refl) as (c & -> & _).
    right; right; right; right; right; right; left. eauto. }
  destruct (gen_alt_inv Halt12) as [Hlist | Hrest].
  { destruct (gen_node_of Hlist eq_refl) as (c & -> & _).
    right; right; right; right; right; right; right; right; right; right. left. eauto. }
  destruct (gen_alt_inv Hrest) as [Hname | Hparen].
  - destruct (gen_node_of Hname eq_refl) as (c & -> & _).
    right; right; right; right; right; right; right; left. eauto.
  - split_seq Hparen as (tsl & ts1 & -> & Hl & H1). text_leaf Hl.
    split_seq H1 as (tse & tsr & -> & He & Hr).
    apply gen_expect_inv in Hr. text_leaf Hr.
    destruct (gen_node_of He eq_refl) as (c & -> & _).
    right; right; right; right; right; right; right; right; left. exists c. reflexivity.
Qed.

Lemma part_shape : forall cs,
  gen (E_rule R__part) cs ->
  (exists ds ss,
     cs = ds ++ ss
     /\ gen (E_plus (E_rule R_declaration)) ds
     /\ (gen (E_rule R__statement) ss \/ ss = []))
  \/ gen (E_rule R__statement) cs.
Proof.
  intros cs H.
  pose proof (gen_splice_inv H eq_refl) as Halt. simpl in Halt.
  destruct (gen_alt_inv Halt) as [Hdecls | Hstatement].
  - left. split_seq Hdecls as (ds & ss & -> & Hds & Hss).
    exists ds, ss. split; [ reflexivity | split; [ exact Hds | ] ].
    destruct (gen_opt_inv Hss) as [Hs | Hnil]; [ left | right ]; assumption.
  - right. exact Hstatement.
Qed.

Lemma declaration_nodes : forall ds,
  gen (E_star (E_rule R_declaration)) ds ->
  Forall (fun t => exists c, t = Node R_declaration c) ds.
Proof.
  intros ds H.
  apply (gen_star_ind (E_rule R_declaration)); [ | | exact H ].
  - apply Forall_nil.
  - intros ts1 ts2 H1 IH.
    destruct (gen_node_of H1 eq_refl) as (c & -> & _).
    apply Forall_cons; [ eauto | exact IH ].
Qed.

Lemma statement_math_value : forall cs,
  gen (body R_value) cs ->
  gen (E_seq (E_rule R__operand) (E_star (E_rule R__more_math))) cs.
Proof. intros cs H. exact H. Qed.

Lemma statement_math : forall cs,
  gen (E_rule R__statement) cs ->
  gen (E_seq (E_rule R__operand) (E_star (E_rule R__more_math))) cs.
Proof.
  intros cs H.
  pose proof (gen_splice_inv H eq_refl) as Hseq. simpl in Hseq.
  exact Hseq.
Qed.

(* ---- what the fragment excludes beyond its rules, and when a tree is valid ---- *)

Definition not_spread (t : tree) : Prop := forall c, t <> Node R_spread c.

(* A spread comes first in a record, and at most once (the lowering reports the
   others). *)
Definition spread_first (cs : list tree) : Prop :=
  match cs with
  | Leaf _ :: Node R_spread _ :: rest => Forall not_spread rest
  | _ => Forall not_spread cs
  end.

(* A payload type of a declaration is a name the table can encode: the group,
   or Number, Int, Bool, Unit, String. *)
Definition type_ok (g : option string) (t : tree) : Prop :=
  match t with
  | Node R_type_name [Leaf (TName n)] =>
      (match g with Some m => String.eqb m n | None => false end = true)
      \/ In n ["Number"; "Int"; "Bool"; "Unit"; "String"]
  | _ => True
  end.

Definition case_ok (g : option string) (t : tree) : Prop :=
  match t with Node R_tag_case c => Forall (type_ok g) c | _ => True end.

Definition is_arm_node (t : tree) : bool :=
  match t with Node R_arm _ => true | _ => false end.

Definition is_tag_arm (t : tree) : bool :=
  match t with Node R_arm (Node R_pattern _ :: _) => true | _ => false end.

Definition is_lit_arm (t : tree) : bool :=
  match t with Node R_arm (Node R_literal_pattern _ :: _) => true | _ => false end.

(* A match has an arm, and its arms are all tag patterns, or all literals with
   an else (the fragment has no bool match that omits it). *)
Definition match_ok (cs : list tree) : Prop :=
  has R_arm cs /\
  (Forall (fun t => is_arm_node t = true -> is_tag_arm t = true) cs
   \/ (Forall (fun t => is_arm_node t = true -> is_lit_arm t = true) cs
       /\ In (sym "else") cs)).

Definition complete_node (r : rule) (cs : list tree) : Prop :=
  match r with
  | R_params => Forall not_pattern cs
  | R_tag_decl => Forall (case_ok (decl_group cs)) cs
  | R_match_expr => match_ok cs
  | _ => True
  end.

Inductive Complete : tree -> Prop :=
  | Cp_leaf : forall k, Complete (Leaf k)
  | Cp_node : forall r cs,
      complete_node r cs -> Forall Complete cs -> Complete (Node r cs).

(* The shapes of a parse tree that lowering reports as a diagnostic, so that
   no term is denoted: a record whose spread is not first, or has a second. *)
Inductive Reject : tree -> Prop :=
  | Rj_spread : forall cs, ~ spread_first cs -> Reject (Node R_record cs)
  | Rj_child : forall r cs c, In c cs -> Reject c -> Reject (Node r cs).

Definition accepted_node (r : rule) (cs : list tree) : Prop :=
  match r with
  | R_record => spread_first cs
  | _ => True
  end.

Inductive Accepted : tree -> Prop :=
  | Ac_leaf : forall k, Accepted (Leaf k)
  | Ac_node : forall r cs,
      accepted_node r cs -> Forall Accepted cs -> Accepted (Node r cs).

Inductive core_tree : tree -> Prop :=
  | Core_leaf : forall k, core_tree (Leaf k)
  | Core_node : forall r cs,
      core_rule r = true -> Forall core_tree cs -> core_tree (Node r cs).

(* The names the program resolves exist in the table: the tag of a pattern, and
   the list tags a list literal builds. *)
Definition known_node (tt : tagtab) (r : rule) (cs : list tree) : Prop :=
  match r with
  | R_arm =>
      match cs with
      | Node R_pattern (Node R_name [Leaf (TName t)] :: _) :: _ => tag_lookup tt t <> None
      | _ => True
      end
  | R_list => tag_lookup tt "Empty" <> None /\ tag_lookup tt "Link" <> None
  | R_each_loop =>
      exists w tge tgl, tag_lookup tt "Empty" = Some (w, tge) /\ tag_lookup tt "Link" = Some (w, tgl)
  | _ => True
  end.

Inductive Known (tt : tagtab) : tree -> Prop :=
  | Kn_leaf : forall k, Known tt (Leaf k)
  | Kn_node : forall r cs,
      known_node tt r cs -> Forall (Known tt) cs -> Known tt (Node r cs).

Ltac prove_known :=
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Kn_leaf
    | (apply Kn_node; [ exact I | ]) ].

Definition valid (t : tree) : Prop :=
  match t with
  | Leaf _ => True
  | Node r _ => gen (E_rule r) [t]
  end.

Lemma gen_valid : forall e ts, gen e ts -> Forall valid ts.
Proof.
  intros e ts H. induction H.
  - apply Forall_cons; [ exact I | apply Forall_nil ].
  - apply Forall_cons; [ exact I | apply Forall_nil ].
  - apply Forall_cons; [ exact I | apply Forall_nil ].
  - apply Forall_cons; [ exact I | apply Forall_nil ].
  - apply Forall_cons; [ exact I | apply Forall_nil ].
  - apply Forall_cons; [ exact I | apply Forall_nil ].
  - apply Forall_nil.
  - (* node *)
    apply Forall_cons; [ | apply Forall_nil ].
    simpl. apply G_node; assumption.
  - (* splice *) assumption.
  - (* seq *) apply Forall_app. split; assumption.
  - assumption.
  - assumption.
  - apply Forall_nil.
  - apply Forall_app. split; assumption.
  - assumption.
  - assumption.
  - apply Forall_nil.
  - assumption.
Qed.

(* ---- from the PEG relation to the forests it can produce ---- *)

Lemma term_step_gen : forall t s ts s',
  term_step t s = Ok ts s' -> gen (E_term t) ts.
Proof.
  intros t s ts s' H. destruct s as [| k s0].
  - (* no tokens left: only the end of input matches *)
    destruct t; simpl in H; try discriminate H.
    injection H as <- _. apply G_eoi.
  - destruct t as [txt | | | | ]; destruct k as [x | n | d | | y]; simpl in H;
      try discriminate H.
    + (* spelled name *)
      destruct (contextual txt) eqn:Hc; [ | discriminate H ].
      destruct (String.eqb txt x) eqn:Hmatch; [ | discriminate H ].
      injection H as <- _. apply String.eqb_eq in Hmatch. subst.
      apply G_word; exact Hc.
    + (* text *)
      destruct (String.eqb txt y) eqn:Hmatch; [ | discriminate H ].
      injection H as <- _. apply String.eqb_eq in Hmatch. subst.
      apply G_text.
    + (* name *) injection H as <- _. apply G_name.
    + (* number *) injection H as <- _. apply G_number.
    + (* decimal *) injection H as <- _. apply G_decimal.
    + (* string *) injection H as <- _. apply G_string.
Qed.

Lemma peg_gen : forall e s res,
  peg e s res ->
  forall ts s', res = Ok ts s' -> Forall core_tree ts -> gen e ts.
Proof.
  intros e s res D.
  induction D as
    [ t s
    | r s res Hbody IH
    | a b s ts s1 res Ha IHa Hb IHb
    | a b s Ha IHa
    | a b s ts s' Ha IHa
    | a b s res Ha IHa Hb IHb
    | a s Ha IHa
    | a s ts s1 ts' s2 Ha IHa Hstar IHstar
    | a s res Hseq IH
    | a s ts s' Ha IHa
    | a s Ha IHa
    | a s res Ha IH ];
    intros out s_out Hres Hcore.
  - (* term *) exact (term_step_gen t s out s_out Hres).
  - (* rule *)
    destruct res as [| ts0 s0]; [ discriminate Hres | ].
    simpl in Hres. destruct (silent r) eqn:Hsilent.
    + injection Hres as <- <-.
      apply G_splice; [ exact Hsilent | ]. apply (IH ts0 s0); [ reflexivity | exact Hcore ].
    + injection Hres as <- <-.
      inversion Hcore as [| ? ? Hnode _]; subst.
      inversion Hnode as [? | ? cs' Hrule Hkids]; subst.
      apply G_node; [ exact Hsilent | exact Hrule | ].
      apply (IH ts0 s0); [ reflexivity | exact Hkids ].
  - (* seq *)
    destruct res as [| ts2 s2]; [ discriminate Hres | ].
    simpl in Hres. injection Hres as <- <-.
    apply Forall_app in Hcore as [Hcore1 Hcore2].
    apply G_seq.
    + apply (IHa ts s1); [ reflexivity | exact Hcore1 ].
    + apply (IHb ts2 s2); [ reflexivity | exact Hcore2 ].
  - (* seq, first part fails *) discriminate Hres.
  - (* alt, left *)
    injection Hres as <- <-. apply G_alt_left. apply (IHa ts s'); [ reflexivity | exact Hcore ].
  - (* alt, right *)
    apply G_alt_right. apply (IHb out s_out); assumption.
  - (* star, stops *)
    injection Hres as <- <-. apply G_star_nil.
  - (* star, steps *)
    injection Hres as <- <-.
    apply Forall_app in Hcore as [Hcore1 Hcore2].
    apply G_star_cons.
    + apply (IHa ts s1); [ reflexivity | exact Hcore1 ].
    + apply (IHstar ts' s2); [ reflexivity | exact Hcore2 ].
  - (* plus *)
    apply G_plus. apply (IH out s_out); assumption.
  - (* opt, present *)
    injection Hres as <- <-. apply G_opt_some. apply (IHa ts s'); [ reflexivity | exact Hcore ].
  - (* opt, absent *)
    injection Hres as <- <-. apply G_opt_none.
  - (* expect *)
    apply G_expect. apply (IH out s_out); assumption.
Qed.

(* ---- totality: every valid, complete core tree has a denotation ---- *)

Fixpoint used_vars (var_of : string -> termvar) (names : list string) : atoms :=
  match names with
  | [] => empty
  | n :: rest => singleton (var_of n) `union` used_vars var_of rest
  end.

Lemma in_used_vars : forall var_of names x,
  List.In x names -> AtomSetImpl.In (var_of x) (used_vars var_of names).
Proof.
  intros var_of names x. induction names as [| n names IH]; intros Hx.
  - destruct Hx.
  - simpl. destruct Hx as [<- | Hx].
    + fsetdec.
    + specialize (IH Hx). fsetdec.
Qed.

Section Totality.

  Context {TT : TagTable}.
  Variable var_of : string -> termvar.
  Variable tbl : list string.

  (* What a node of each core kind must yield, given its children do. *)
  Definition TotKind (t : tree) : Prop :=
    match t with
    | Leaf _ => True
    | Node r cs =>
        match r with
        | R_number | R_boolean | R_function | R_record | R_local
        | R_expr | R_value | R_string | R_conditional | R_destructure | R_negation
        | R_list | R_match_expr | R_repeat_loop | R_count_loop | R_each_loop =>
            exists e, Den var_of tbl t e
        | R_name => exists x, cs = [Leaf (TName x)]
        | R_arm =>
            match cs with
            | Node R_pattern _ :: _ => exists w tg b, Den_arm var_of tbl t w tg b
            | Node R_literal_pattern _ :: _ => exists l b, Den_lit_arm var_of tbl t l b
            | _ => True
            end
        | R_pattern => exists t' xs, Den_tpat cs t' xs
        | R_labels => exists xs, Den_labels cs xs
        | R_literal_pattern => exists c e, cs = [c] /\ Den var_of tbl c e
        | R_spread =>
            exists c e, cs = [sym "..."; Node R_expr c] /\ Den var_of tbl (Node R_expr c) e
        | R_declaration => exists x v, Den_decl var_of tbl t x v
        | R_field => exists l e, Den_field var_of tbl t l e
        | R_access => exists l, cs = [sym "."; ident l]
        | R_take => exists l, cs = [sym "::"; ident l]
        | R_call =>
            cs = [sym "("; sym ")"]
            \/ exists args es,
                 cs = [sym "("; Node R_arguments args; sym ")"]
                 /\ Den_args var_of tbl args es
        | R_arguments => exists es, Den_args var_of tbl cs es
        | R_params => exists xs, Den_params var_of tbl cs xs
        | _ => True
        end
    end.

  Lemma fresh_for_args : forall es,
    exists s, Forall (fun a => ~ AtomSetImpl.In s (fv_exp a)) es.
  Proof.
    intros es.
    destruct (atom_fresh (fold_right (fun a acc => fv_exp a `union` acc)
                                     AtomSetImpl.empty es)) as [s Hs].
    exists s. revert Hs. induction es as [| a es IH]; intros Hs.
    - apply Forall_nil.
    - simpl in Hs. apply Forall_cons.
      + intros Hin. apply Hs. fsetdec.
      + apply IH. intros Hin. apply Hs. fsetdec.
  Qed.

  Lemma dot_den : forall acc l args es rest,
    Den_args var_of tbl args es ->
    (forall acc', exists e'', Den_posts var_of tbl acc' rest e'') ->
    exists e'', Den_posts var_of tbl acc
      (Node R_access [sym "."; ident l]
         :: Node R_call [sym "("; Node R_arguments args; sym ")"] :: rest) e''.
  Proof.
    intros acc l args es rest Hargs Hrest.
    destruct (is_path acc) eqn:Hpath.
    - destruct (Hrest (apps (e_proj acc (lab tbl l)) (acc :: es))) as (e'' & Hposts).
      exists e''. apply DP_dot_path with (es := es); assumption.
    - destruct (fresh_for_args es) as (s & Hfresh).
      destruct (Hrest (e_let acc (close_exp s (apps (e_proj (e_fvar_f s) (lab tbl l))
                                                     (e_fvar_f s :: es)))))
        as (e'' & Hposts).
      exists e''. apply DP_dot_bind with (s := s) (es := es); assumption.
  Qed.

  Lemma dot_den_unit : forall acc l rest,
    (forall acc', exists e'', Den_posts var_of tbl acc' rest e'') ->
    exists e'', Den_posts var_of tbl acc
      (Node R_access [sym "."; ident l]
         :: Node R_call [sym "("; sym ")"] :: rest) e''.
  Proof.
    intros acc l rest Hrest.
    destruct (is_path acc) eqn:Hpath.
    - destruct (Hrest (apps (e_proj acc (lab tbl l)) [acc])) as (e'' & Hposts).
      exists e''. apply DP_dot_path_unit; assumption.
    - destruct (atom_fresh (fv_exp acc)) as [s _].
      destruct (Hrest (e_let acc (close_exp s (apps (e_proj (e_fvar_f s) (lab tbl l))
                                                     [e_fvar_f s]))))
        as (e'' & Hposts).
      exists e''. apply DP_dot_bind_unit with (s := s); assumption.
  Qed.

  Lemma posts_den : forall n ps,
    length ps <= n ->
    gen (E_star (E_rule R__postfix)) ps -> Forall TotKind ps ->
    forall acc, exists e', Den_posts var_of tbl acc ps e'.
  Proof.
    induction n as [| n IH]; intros ps Hlen H Hkids acc.
    - destruct ps as [| t ps]; [ | simpl in Hlen; lia ].
      exists acc. apply DP_nil.
    - destruct (gen_star_inv H) as [-> | (ts1 & ts2 & -> & Hpost & Hrest)].
      { exists acc. apply DP_nil. }
      apply Forall_app in Hkids as [Hkids1 Hkids2].
      pose proof (gen_splice_inv Hpost eq_refl) as Halt. simpl in Halt.
      destruct (gen_alt_inv Halt) as [Haccess | Htake_call].
      + (* .label, then perhaps a call *)
        destruct (gen_node_of Haccess eq_refl) as (c & -> & _).
        inversion Hkids1 as [| ? ? Hkid _]; subst. simpl in Hkid.
        destruct Hkid as (l & ->).
        simpl in Hlen.
        destruct (gen_star_inv Hrest) as [-> | (ts3 & ts4 & -> & Hpost3 & Hrest4)].
        * destruct (IH [] (le_0_n _) Hrest Hkids2 (e_proj acc (lab tbl l))) as (e' & Hposts).
          exists e'. apply DP_access; [ intros [] | exact Hposts ].
        * pose proof (gen_splice_inv Hpost3 eq_refl) as Halt3. simpl in Halt3.
          apply Forall_app in Hkids2 as [Hkids3 Hkids4].
          destruct (gen_alt_inv Halt3) as [Haccess3 | Htake_call3].
          -- destruct (gen_node_of Haccess3 eq_refl) as (c3 & -> & _).
             assert (Hk : Forall TotKind ([Node R_access c3] ++ ts4))
               by (apply Forall_app; split; assumption).
             destruct (IH ([Node R_access c3] ++ ts4) ltac:(simpl; simpl in Hlen; lia) Hrest Hk
                         (e_proj acc (lab tbl l))) as (e' & Hposts).
             exists e'. apply DP_access; [ intros [] | exact Hposts ].
          -- destruct (gen_alt_inv Htake_call3) as [Htake3 | Hcall3].
             ++ destruct (gen_node_of Htake3 eq_refl) as (c3 & -> & _).
                assert (Hk : Forall TotKind ([Node R_take c3] ++ ts4))
                  by (apply Forall_app; split; assumption).
                destruct (IH ([Node R_take c3] ++ ts4) ltac:(simpl; simpl in Hlen; lia) Hrest Hk
                            (e_proj acc (lab tbl l))) as (e' & Hposts).
                exists e'. apply DP_access; [ intros [] | exact Hposts ].
             ++ (* a call straight after the access: a dot call *)
                destruct (gen_node_of Hcall3 eq_refl) as (c3 & -> & _).
                inversion Hkids3 as [| ? ? Hkid3 _]; subst. simpl in Hkid3.
                destruct Hkid3 as [-> | (args & es & -> & Hargs)].
                ** apply (dot_den_unit acc l ts4).
                   intros acc'. apply (IH ts4 ltac:(simpl in Hlen; simpl; lia) Hrest4 Hkids4 acc').
                ** apply (dot_den acc l args es ts4 Hargs).
                   intros acc'. apply (IH ts4 ltac:(simpl in Hlen; simpl; lia) Hrest4 Hkids4 acc').
      + destruct (gen_alt_inv Htake_call) as [Htake | Hcall].
        * (* ::label *)
          destruct (gen_node_of Htake eq_refl) as (c & -> & _).
          inversion Hkids1 as [| ? ? Hkid _]; subst. simpl in Hkid.
          destruct Hkid as (l & ->).
          destruct (IH ts2 ltac:(simpl in Hlen; lia) Hrest Hkids2 (e_proj acc (lab tbl l)))
            as (e' & Hposts).
          exists e'. apply DP_take. exact Hposts.
        * (* (arguments) *)
          destruct (gen_node_of Hcall eq_refl) as (c & -> & _).
          inversion Hkids1 as [| ? ? Hkid _]; subst. simpl in Hkid.
          destruct Hkid as [-> | (args & es & -> & Hargs)].
          -- destruct (IH ts2 ltac:(simpl in Hlen; lia) Hrest Hkids2 (e_app acc e_unit))
               as (e' & Hposts).
             exists e'. apply DP_call_unit. exact Hposts.
          -- destruct (IH ts2 ltac:(simpl in Hlen; lia) Hrest Hkids2 (apps acc es))
               as (e' & Hposts).
             exists e'. apply DP_call with (es := es); assumption.
  Qed.

  Lemma chain_head : forall t posts e0,
    Den var_of tbl t e0 ->
    gen (E_star (E_rule R__postfix)) posts -> Forall TotKind posts ->
    exists e, Den_chain var_of tbl (t :: posts) e.
  Proof.
    intros t posts e0 Hden Hposts Hkids.
    destruct (posts_den (length posts) posts (le_n _) Hposts Hkids e0) as (e & Hchain).
    exists e. apply DC_head with (e0 := e0); assumption.
  Qed.

  (* A tag at the head of a chain: bare, or with the arguments of the call that
     follows it. *)
  Lemma tag_chain : forall x w tg posts,
    tag_lookup tags x = Some (w, tg) ->
    gen (E_star (E_rule R__postfix)) posts -> Forall TotKind posts ->
    exists e, Den_chain var_of tbl (ident x :: posts) e.
  Proof.
    intros x w tg posts Hlook H Hkids.
    destruct (gen_star_inv H) as [Hnil | (ts1 & ts2 & Hposts & Hpost & Hrest)].
    - subst posts. exists (e_con w tg e_unit).
      apply (DC_tag var_of tbl x w tg [] _ Hlook); [ intros [] | apply DP_nil ].
    - pose proof (gen_splice_inv Hpost eq_refl) as Halt. simpl in Halt.
      destruct (gen_alt_inv Halt) as [Haccess | Htake_call].
      + destruct (gen_node_of Haccess eq_refl) as (c & Hts1 & _).
        destruct (posts_den (length posts) posts (le_n _) H Hkids (e_con w tg e_unit))
          as (e & Hden).
        exists e. apply (DC_tag var_of tbl x w tg posts e Hlook); [ | exact Hden ].
        subst posts ts1. intros [].
      + destruct (gen_alt_inv Htake_call) as [Htake | Hcall].
        * destruct (gen_node_of Htake eq_refl) as (c & Hts1 & _).
          destruct (posts_den (length posts) posts (le_n _) H Hkids (e_con w tg e_unit))
            as (e & Hden).
          exists e. apply (DC_tag var_of tbl x w tg posts e Hlook); [ | exact Hden ].
          subst posts ts1. intros [].
        * destruct (gen_node_of Hcall eq_refl) as (c & Hts1 & _).
          subst posts ts1.
          apply Forall_app in Hkids as [Hk1 Hk2].
          inversion Hk1 as [| ? ? Hk _]; subst. simpl in Hk.
          destruct Hk as [-> | (args & es & -> & Hargs)].
          ++ destruct (posts_den (length ts2) ts2 (le_n _) Hrest Hk2 (e_con w tg e_unit))
               as (e & Hden).
             exists e. exact (DC_tag_unit var_of tbl x w tg ts2 e Hlook Hden).
          ++ destruct (posts_den (length ts2) ts2 (le_n _) Hrest Hk2 (e_con w tg (payload es)))
               as (e & Hden).
             exists e. exact (DC_tag_call var_of tbl x w tg args es ts2 e Hlook Hargs Hden).
  Qed.

  Lemma chain_den : forall cs,
    gen (E_rule R__term) cs -> Forall TotKind cs ->
    exists e, Den_chain var_of tbl cs e.
  Proof.
    intros cs H Hkids.
    destruct (term_shape cs H) as [(c & ->) | (prim & posts & -> & Hprim & Hposts)].
    - (* a negation is a whole term *)
      inversion Hkids as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (e0 & Hden).
      exact (chain_head _ [] e0 Hden (G_star_nil _) (Forall_nil _)).
    - apply Forall_app in Hkids as [Hkprim Hkposts].
      destruct (primary_shape prim Hprim) as
        [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | [(c & ->) | (c & ->)]]]]]]]]]]]]]];
        try (inversion Hkprim as [| ? ? Hk _]; subst; simpl in Hk;
             destruct Hk as (e0 & Hden);
             exact (chain_head _ _ e0 Hden Hposts Hkposts)).
      + (* a name: a variable, or a tag *)
        inversion Hkprim as [| ? ? Hk _]; subst. simpl in Hk.
        destruct Hk as (x & ->).
        destruct (tag_lookup tags x) as [[w tg] | ] eqn:Hlook.
        * exact (tag_chain x w tg posts Hlook Hposts Hkposts).
        * exact (chain_head _ _ _ (D_name var_of tbl x Hlook) Hposts Hkposts).
      + (* parenthesised expression *)
        inversion Hkprim as [| ? ? _ Hrest]; subst.
        inversion Hrest as [| ? ? Hk _]; subst. simpl in Hk.
        destruct Hk as (e0 & Hden).
        destruct (posts_den (length posts) posts (le_n _) Hposts Hkposts e0) as (e & Hchain).
        exists e. apply DC_paren with (e0 := e0); assumption.
  Qed.

  (* An operand: prefix [not]s, then a term. *)
  Lemma operand_den : forall cs,
    gen (E_rule R__operand) cs -> Forall TotKind cs ->
    exists is, Den_opd var_of tbl cs is /\ Opd is.
  Proof.
    intros cs H Hkids.
    destruct (operand_shape cs H) as (nots & t & -> & Hnots & Hterm).
    revert Hkids.
    apply (gen_star_ind (E_rule R_not_op)
             (fun nots => Forall TotKind (nots ++ t) ->
                          exists is, Den_opd var_of tbl (nots ++ t) is /\ Opd is));
      [ | | exact Hnots ].
    - intros Hk. simpl.
      destruct (chain_den t Hterm Hk) as (e & Hchain).
      exists [I_val e]. split; [ apply DO_val; exact Hchain | apply Opd_val ].
    - intros ts1 ts2 Hnot IH Hk.
      destruct (gen_node_of Hnot eq_refl) as (c & -> & Hc). simpl in Hc. text_inv Hc. subst.
      simpl in Hk. inversion Hk as [| ? ? _ Hk']; subst.
      destruct (IH Hk') as (is & Hden & Hopd).
      exists (I_not :: is). simpl. split.
      + apply (DO_not var_of tbl). exact Hden.
      + apply Opd_not. exact Hopd.
  Qed.

  (* The operators and operands after the first operand. *)
  Lemma run_den : forall tsm,
    gen (E_star (E_rule R__more_math)) tsm ->
    forall first,
      gen (E_rule R__operand) first -> Forall TotKind (first ++ tsm) ->
      exists is, Den_run var_of tbl (first ++ tsm) is /\ Run is.
  Proof.
    intros tsm H.
    apply (gen_star_ind (E_rule R__more_math)
             (fun tsm => forall first,
                gen (E_rule R__operand) first -> Forall TotKind (first ++ tsm) ->
                exists is, Den_run var_of tbl (first ++ tsm) is /\ Run is));
      [ | | exact H ].
    - intros first Hfirst Hk. rewrite app_nil_r in *.
      destruct (operand_den first Hfirst Hk) as (is & Hden & Hopd).
      exists is. split; [ apply DR_one; exact Hden | apply Run_one; exact Hopd ].
    - intros m1 m2 Hm1 IH first Hfirst Hk.
      destruct (more_math_shape _ Hm1) as (o & c2 & -> & Hne & Hc2).
      change (first ++ (lop_tree o :: c2) ++ m2) with (first ++ lop_tree o :: (c2 ++ m2)) in Hk.
      rename Hk into Hk'.
      apply Forall_app in Hk' as [Hk1 Hk2].
      inversion Hk2 as [| ? ? _ Hk3]; subst.
      destruct (operand_den first Hfirst Hk1) as (is1 & Hden1 & Hopd1).
      destruct (IH c2 Hc2 Hk3) as (is2 & Hden2 & Hrun2).
      exists (is1 ++ I_op o :: is2). split.
      + change (first ++ (lop_tree o :: c2) ++ m2) with (first ++ lop_tree o :: (c2 ++ m2)).
        apply DR_more; assumption.
      + apply Run_more; assumption.
  Qed.

  Lemma math_den : forall cs,
    gen (E_seq (E_rule R__operand) (E_star (E_rule R__more_math))) cs ->
    Forall TotKind cs ->
    exists e, Den_math var_of tbl cs e.
  Proof.
    intros cs H Hkids.
    split_seq H as (tso & tsm & -> & Hop & Hmore).
    destruct (run_den tsm Hmore tso Hop Hkids) as (is & Hden & Hrun).
    destruct (resolve_total is Hrun) as (e & Hres).
    exists e. apply (DM_run var_of tbl _ is e); assumption.
  Qed.

  Definition sequel_tree : tree := Node R_sequel [sym ";"].

  Definition BlkTot (k : list tree) : Prop :=
    forall ctx fin, exists xs gs b, Den_blk var_of tbl ctx fin k xs gs b.

  (* What may follow a part of a block: nothing, or a [;] and a block. *)
  Definition Cont (k : list tree) : Prop :=
    k = [] \/ exists k', k = sequel_tree :: k' /\ BlkTot k'.

  Lemma blk_end : BlkTot [].
  Proof. intros ctx fin. exists [], [], fin. apply DK_end. Qed.

  Lemma cont_blk : forall k, Cont k -> BlkTot k.
  Proof.
    intros k [-> | (k' & -> & Hk')]; [ exact blk_end | ].
    intros ctx fin. destruct (Hk' ctx fin) as (xs & gs & b & H).
    exists xs, gs, b. apply DK_skip. exact H.
  Qed.

  Lemma decls_blk : forall ds,
    Forall (fun t => exists c, t = Node R_declaration c) ds ->
    Forall TotKind ds ->
    forall k, BlkTot k -> BlkTot (ds ++ k).
  Proof.
    intros ds Hds. induction Hds as [| d ds [c ->] _ IH]; intros Hkids k Hk; [ exact Hk | ].
    inversion Hkids as [| ? ? Hd Hkids']; subst. simpl in Hd.
    destruct Hd as (x & v & Hdecl).
    specialize (IH Hkids' k Hk).
    intros ctx fin. rewrite <- app_comm_cons.
    destruct (is_fn_decl (Node R_declaration c)) eqn:Hfn.
    - destruct (mentions_any ctx v) eqn:Hm.
      + destruct (IH (var_of x :: ctx) (e_fvar_f (var_of x))) as (xs & gs & b & H).
        exists xs, gs, (fn_place (var_of x) v b).
        eapply DK_late; eassumption.
      + destruct (IH ctx (e_fvar_f (var_of x))) as (xs & gs & b & H).
        exists (x :: xs), (v :: gs), b.
        eapply DK_hoist; eassumption.
    - destruct (IH (var_of x :: ctx) (e_fvar_f (var_of x))) as (xs & gs & b & H).
      exists xs, gs, (e_let v (close_exp (var_of x) b)).
      eapply DK_value; eassumption.
  Qed.

  Lemma stmt_blk : forall ss,
    gen (E_rule R__statement) ss -> Forall TotKind ss ->
    forall k, Cont k -> BlkTot (ss ++ k).
  Proof.
    intros ss H Hkids k Hk.
    destruct (math_den ss (statement_math _ H) Hkids) as (e & Hmath).
    destruct Hk as [-> | (k' & -> & Hk')].
    - intros ctx fin. rewrite app_nil_r. exists [], [], e. apply DK_chain. exact Hmath.
    - intros ctx fin. destruct (Hk' ctx e_unit) as (xs & gs & b & Hb).
      exists xs, gs, (e_let e b). apply DK_seq; assumption.
  Qed.

  Lemma part_blk : forall part,
    gen (E_rule R__part) part -> Forall TotKind part ->
    forall k, Cont k -> BlkTot (part ++ k).
  Proof.
    intros part H Hkids k Hk.
    destruct (part_shape part H) as [(ds & ss & -> & Hds & Hss) | Hstatement].
    - apply Forall_app in Hkids as [Hkds Hkss].
      destruct (gen_seq_inv (gen_plus_inv Hds)) as (d1 & drest & Hsplit & Hd1 & Hrest).
      assert (Hstar : gen (E_star (E_rule R_declaration)) ds)
        by (rewrite Hsplit; apply G_star_cons; assumption).
      rewrite app_assoc.
      apply decls_blk; [ exact (declaration_nodes ds Hstar) | exact Hkds | ].
      destruct Hss as [Hst | ->].
      + exact (stmt_blk ss Hst Hkss k Hk).
      + simpl. exact (cont_blk k Hk).
    - exact (stmt_blk part Hstatement Hkids k Hk).
  Qed.

  Lemma tail_cont : forall ts,
    gen (E_star (E_seq (E_rule R_sequel) (E_rule R__part))) ts ->
    Forall TotKind ts ->
    forall opt, (opt = [] \/ opt = [sequel_tree]) -> Cont (ts ++ opt).
  Proof.
    intros ts H.
    apply (gen_star_ind (E_seq (E_rule R_sequel) (E_rule R__part))
             (fun ts => Forall TotKind ts ->
                        forall opt, (opt = [] \/ opt = [sequel_tree]) -> Cont (ts ++ opt)));
      [ | | exact H ].
    - intros _ opt [-> | ->]; simpl.
      + left. reflexivity.
      + right. exists []. split; [ reflexivity | exact blk_end ].
    - intros ts1 ts2 Hstep IH Hkids opt Hopt.
      apply Forall_app in Hkids as [Hk1 Hk2].
      split_seq Hstep as (tss & tsp & -> & Hsq & Hpart).
      destruct (gen_node_of Hsq eq_refl) as (c & -> & Hc). simpl in Hc. text_inv Hc. subst c.
      inversion Hk1 as [| ? ? _ Hkp]; subst.
      right. exists (tsp ++ ts2 ++ opt). split.
      + unfold sequel_tree. simpl. rewrite <- app_assoc. reflexivity.
      + apply part_blk; [ exact Hpart | exact Hkp | exact (IH Hk2 opt Hopt) ].
  Qed.

  Lemma block_den : forall cs,
    gen (body R_expr) cs -> Forall TotKind cs ->
    exists e, Den_block var_of tbl cs e.
  Proof.
    intros cs H Hkids. simpl in H.
    split_seq H as (tsp & ts1 & -> & Hpart & H1).
    split_seq H1 as (tsstar & tsopt & -> & Hstar & Hopt).
    apply Forall_app in Hkids as [Hkp Hk1]. apply Forall_app in Hk1 as [Hks Hko].
    assert (Hopt' : tsopt = [] \/ tsopt = [sequel_tree]).
    { destruct (gen_opt_inv Hopt) as [Hs | ->]; [ | left; reflexivity ].
      destruct (gen_node_of Hs eq_refl) as (c & -> & Hc). simpl in Hc. text_inv Hc. subst c.
      right. reflexivity. }
    pose proof (tail_cont tsstar Hstar Hks tsopt Hopt') as Hcont.
    destruct (part_blk tsp Hpart Hkp _ Hcont [] e_unit) as (xs & gs & b & Hb).
    exists (wrap_group (List.map var_of xs) gs b). apply DB_top. exact Hb.
  Qed.

  Lemma args_den : forall fin tail,
    (fin = [] \/ fin = [sym ","]) ->
    gen (E_star (E_seq (E_term (T_text ",")) (E_rule R_expr))) tail ->
    Forall TotKind tail ->
    forall t e, Den var_of tbl t e ->
    exists es, Den_args var_of tbl (t :: tail ++ fin) es.
  Proof.
    intros fin tail Hfin H.
    apply (gen_star_ind (E_seq (E_term (T_text ",")) (E_rule R_expr))
             (fun tail => Forall TotKind tail ->
                          forall t e, Den var_of tbl t e ->
                          exists es, Den_args var_of tbl (t :: tail ++ fin) es));
      [ | | exact H ].
    - (* last argument *)
      intros _ t e Hden. simpl.
      destruct Hfin as [-> | ->].
      + exists [e]. apply DA_last. exact Hden.
      + exists [e]. apply DA_trailing. exact Hden.
    - intros ts1 ts2 Hstep IH Hkids t e Hden.
      apply Forall_app in Hkids as [Hkids1 Hkids2].
      split_seq Hstep as (tscomma & tsarg & -> & Hcomma & Harg).
      text_inv Hcomma. subst.
      destruct (gen_node_of Harg eq_refl) as (c & -> & _).
      inversion Hkids1 as [| ? ? _ Hrest]; subst.
      inversion Hrest as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (e2 & Hden2).
      destruct (IH Hkids2 (Node R_expr c) e2 Hden2) as (es & Hargs).
      exists (e :: es). simpl. apply DA_more; assumption.
  Qed.

  Lemma arguments_den : forall cs,
    gen (body R_arguments) cs -> Forall TotKind cs ->
    exists es, Den_args var_of tbl cs es.
  Proof.
    intros cs H Hkids.
    destruct (shape_arguments cs H) as (c & tail & fin & -> & Htail & Hfin).
    inversion Hkids as [| ? ? Hk Hktail]; subst. simpl in Hk.
    destruct Hk as (e & Hden).
    apply Forall_app in Hktail as [Hktail _].
    exact (args_den fin tail Hfin Htail Hktail _ _ Hden).
  Qed.

  Lemma params_den : forall tail,
    gen (E_star (E_seq (E_term (T_text ",")) (E_rule R__param))) tail ->
    Forall not_pattern tail ->
    forall x, exists xs, Den_params var_of tbl (ident x :: tail) (x :: xs).
  Proof.
    intros tail H.
    apply (gen_star_ind (E_seq (E_term (T_text ",")) (E_rule R__param))
             (fun tail => Forall not_pattern tail -> forall x,
                exists xs, Den_params var_of tbl (ident x :: tail) (x :: xs)));
      [ | | exact H ].
    - intros _ x. exists []. apply DPa_one.
    - intros ts1 ts2 Hstep IH Hplain x.
      apply Forall_app in Hplain as [Hplain1 Hplain2].
      split_seq Hstep as (tscomma & tsparam & -> & Hcomma & Hparam).
      text_inv Hcomma. subst.
      inversion Hplain1 as [| ? ? _ Hplainp]; subst.
      destruct (shape_param _ Hparam Hplainp) as (y & ->).
      destruct (IH Hplain2 y) as (ys & Hys).
      exists (y :: ys). simpl. apply DPa_more. exact Hys.
  Qed.

  Lemma sep_den : forall fin tail,
    (fin = [] \/ fin = [sym ","]) ->
    gen (E_star (E_seq (E_term (T_text ",")) (E_rule R__record_item))) tail ->
    Forall TotKind tail -> Forall not_spread tail ->
    exists fs, Den_sep var_of tbl (tail ++ fin ++ [sym "}"]) fs.
  Proof.
    intros fin tail Hfin H.
    apply (gen_star_ind (E_seq (E_term (T_text ",")) (E_rule R__record_item))
             (fun tail => Forall TotKind tail -> Forall not_spread tail ->
                exists fs, Den_sep var_of tbl (tail ++ fin ++ [sym "}"]) fs));
      [ | | exact H ].
    - (* the closing brace *)
      intros _ _. simpl.
      destruct Hfin as [-> | ->].
      + exists fs_nil. apply DS_end.
      + exists fs_nil. apply DS_more. apply DI_end.
    - intros ts1 ts2 Hstep IH Hkids Hplain.
      apply Forall_app in Hkids as [Hkids1 Hkids2].
      apply Forall_app in Hplain as [Hplain1 Hplain2].
      split_seq Hstep as (tscomma & tsitem & -> & Hcomma & Hitem).
      text_inv Hcomma. subst.
      destruct (shape_record_item _ Hitem) as [(c & ->) | (c & ->)].
      2: { exfalso. inversion Hplain1 as [| ? ? _ Hrest]; subst.
           inversion Hrest as [| ? ? Hc _]; subst. exact (Hc c eq_refl). }
      inversion Hkids1 as [| ? ? _ Hrest]; subst.
      inversion Hrest as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (l & e & Hfield).
      destruct (IH Hkids2 Hplain2) as (fs & Hsep).
      exists (fs_cons (lab tbl l) e fs). simpl.
      apply DS_more. apply DI_field with (l := l) (e := e); assumption.
  Qed.

  Lemma fresh_source : forall body names,
    exists s, ~ AtomSetImpl.In s (fv_exp body) /\
              forall x, List.In x names -> s <> var_of x.
  Proof.
    intros body names.
    destruct (atom_fresh (fv_exp body `union` used_vars var_of names)) as [s Hs].
    exists s. split.
    - intros Hin. apply Hs. fsetdec.
    - intros x Hx Heq. apply Hs. rewrite Heq. apply AtomSetImpl.union_3.
      exact (in_used_vars var_of names x Hx).
  Qed.

End Totality.

Section TreeInduction.

  Variable P : tree -> Prop.
  Hypothesis Hleaf : forall k, P (Leaf k).
  Hypothesis Hnode : forall r cs, Forall P cs -> P (Node r cs).

  Fixpoint tree_ind' (t : tree) : P t :=
    match t with
    | Leaf k => Hleaf k
    | Node r cs =>
        Hnode r cs
          ((fix go (l : list tree) : Forall P l :=
              match l with
              | [] => Forall_nil P
              | c :: l' => Forall_cons c (tree_ind' c) (go l')
              end) cs)
    end.

End TreeInduction.

Lemma not_spread_dec : forall t, {not_spread t} + {~ not_spread t}.
Proof.
  intros t. destruct t as [k | r c].
  - left. intros c H. discriminate H.
  - destruct r; try (left; intros c' H; discriminate H).
    right. intros H. exact (H c eq_refl).
Qed.

Lemma spread_first_dec : forall cs, {spread_first cs} + {~ spread_first cs}.
Proof.
  intros cs. unfold spread_first.
  assert (Fdec : forall l, {Forall not_spread l} + {~ Forall not_spread l})
    by (intros l; apply Forall_dec; exact not_spread_dec).
  destruct cs as [| t [| t2 rest]]; [ exact (Fdec _) | destruct t; exact (Fdec _) | ].
  destruct t as [k | r c]; [ | exact (Fdec _) ].
  destruct t2 as [k2 | r2 c2]; [ exact (Fdec _) | ].
  destruct r2; exact (Fdec _).
Qed.

(* Every parse tree is one lowering reports, or one it accepts. *)
Lemma reject_or_accepted : forall t, Reject t \/ Accepted t.
Proof.
  apply (tree_ind' (fun t => Reject t \/ Accepted t)).
  - intros k. right. apply Ac_leaf.
  - intros r cs IH.
    assert (Hkids : (exists c, In c cs /\ Reject c) \/ Forall Accepted cs).
    { induction IH as [| c cs' Hc _ IHcs].
      - right. apply Forall_nil.
      - destruct Hc as [Hr | Ha].
        + left. exists c. split; [ left; reflexivity | exact Hr ].
        + destruct IHcs as [(c' & Hin & Hr) | Hall].
          * left. exists c'. split; [ right; exact Hin | exact Hr ].
          * right. apply Forall_cons; assumption. }
    destruct Hkids as [(c & Hin & Hr) | Hall].
    + left. exact (Rj_child r cs c Hin Hr).
    + destruct r; try (right; apply Ac_node; [ exact I | exact Hall ]).
      destruct (spread_first_dec cs) as [Hs | Hns].
      * right. apply Ac_node; [ exact Hs | exact Hall ].
      * left. apply Rj_spread. exact Hns.
Qed.

Ltac acc_all :=
  cbv;
  repeat first
    [ apply Forall_nil | apply Forall_cons | apply Ac_leaf | apply Ac_node ];
  simpl; try exact I.

Ltac in_list := simpl; repeat first [ left; reflexivity | right ].

Section Steps.

  Context {TT : TagTable}.
  Variable var_of : string -> termvar.
  Variable tbl : list string.

  Definition StepO (r : rule) : Prop :=
    forall cs,
      gen (body r) cs -> complete_node r cs ->
      Forall (TotKind var_of tbl) cs -> TotKind var_of tbl (Node r cs).

  Definition Step (r : rule) : Prop :=
    forall cs,
      gen (body r) cs -> complete_node r cs -> known_node tags r cs ->
      accepted_node r cs ->
      Forall (TotKind var_of tbl) cs -> TotKind var_of tbl (Node r cs).

  Lemma lift : forall r, StepO r -> Step r.
  Proof. intros r H cs Hgen Hcomplete _ _ Hkids. exact (H cs Hgen Hcomplete Hkids). Qed.

  Lemma step_number : StepO R_number.
  Proof.
    intros cs H _ _. destruct (shape_number cs H) as [(n & ->) | (d & ->)].
    - simpl. exists (e_num (z_of_nat n)). apply D_num.
    - simpl. exists (e_dec d). apply D_dec.
  Qed.

  Lemma step_name : StepO R_name.
  Proof.
    intros cs H _ _. destruct (shape_name cs H) as (x & ->).
    simpl. exists x. reflexivity.
  Qed.

  Lemma step_boolean : StepO R_boolean.
  Proof.
    intros cs H _ _. destruct (shape_boolean cs H) as [-> | ->]; simpl.
    - exists e_true. apply D_true.
    - exists e_false. apply D_false.
  Qed.

  Lemma step_expr : StepO R_expr.
  Proof.
    intros cs H _ Hkids.
    destruct (block_den var_of tbl cs H Hkids) as (e & Hblock).
    simpl. exists e. apply D_expr. exact Hblock.
  Qed.

  Lemma step_value : StepO R_value.
  Proof.
    intros cs H _ Hkids.
    destruct (math_den var_of tbl cs (statement_math_value cs H) Hkids)
      as (e & Hmath).
    simpl. exists e. apply D_value. exact Hmath.
  Qed.

  Lemma bare_number_dec : forall cs, {bare_number cs} + {~ bare_number cs}.
  Proof.
    intros cs. destruct cs as [| t [| t2 rest]].
    - right. intros [c H]. discriminate H.
    - destruct t as [k | r c].
      + right. intros [c H]. discriminate H.
      + destruct r; try (right; intros [c' H]; inversion H; fail).
        left. exists c. reflexivity.
    - right. intros [c H]. discriminate H.
  Qed.

  Lemma step_negation : StepO R_negation.
  Proof.
    intros cs H _ Hkids.
    destruct (negation_shape cs H) as [(c & ->) | (chain & -> & Hchain)].
    - (* a negation of a negation *)
      inversion Hkids as [| ? ? _ Hrest]; subst.
      inversion Hrest as [| ? ? Hk _]; subst. simpl in Hk.
      destruct Hk as (e & Hden).
      simpl. exists (e_bin (e_num 0) bop_sub e). apply D_neg_neg. exact Hden.
    - inversion Hkids as [| ? ? _ Hk]; subst.
      assert (Hterm : gen (E_rule R__term) chain).
      { apply G_splice; [ reflexivity | ]. simpl. apply G_alt_right. exact Hchain. }
      destruct (bare_number_dec chain) as [(c & ->) | Hnot].
      + assert (Hvalid : Forall valid [Node R_number c]) by exact (gen_valid _ _ Hchain).
        inversion Hvalid as [| ? ? Hnode _]; subst.
        destruct (gen_node_inv Hnode eq_refl) as (c' & Hc' & _ & Hbody).
        injection Hc' as <-.
        destruct (shape_number c Hbody) as [(n & ->) | (d & ->)]; simpl.
        * exists (e_num (Stdlib.ZArith.BinInt.Z.opp (z_of_nat n))). apply D_neg_int.
        * exists (e_dec d). apply D_neg_dec.
      + destruct (chain_den var_of tbl chain Hterm Hk) as (e & Hden).
        simpl. exists (e_bin (e_num 0) bop_sub e). apply D_neg_chain; assumption.
  Qed.

  Lemma step_string : StepO R_string.
  Proof.
    intros cs H _ _. pose proof (shape_string cs H) as ->.
    simpl. exists (e_str []). apply D_str.
  Qed.

  Lemma step_conditional : StepO R_conditional.
  Proof.
    intros cs H _ Hkids.
    rewrite Forall_forall in Hkids.
    destruct (shape_conditional cs H) as [(a & b & c & ->) | (a & b & ->)].
    - assert (Ha : TotKind var_of tbl (Node R_expr a)) by (apply Hkids; in_list).
      assert (Hb : TotKind var_of tbl (Node R_expr b)) by (apply Hkids; in_list).
      assert (Hc : TotKind var_of tbl (Node R_expr c)) by (apply Hkids; in_list).
      simpl in Ha, Hb, Hc.
      destruct Ha as (ea & Hda). destruct Hb as (eb & Hdb). destruct Hc as (ec & Hdc).
      simpl. exists (e_ite ea eb ec). apply D_cond; assumption.
    - assert (Ha : TotKind var_of tbl (Node R_expr a)) by (apply Hkids; in_list).
      assert (Hb : TotKind var_of tbl (Node R_expr b)) by (apply Hkids; in_list).
      simpl in Ha, Hb.
      destruct Ha as (ea & Hda). destruct Hb as (eb & Hdb).
      simpl. exists (e_ite ea eb e_unit). apply D_cond_noelse; assumption.
  Qed.

  Lemma loop_body_den : forall bs,
    loop_body_shape bs -> Forall (TotKind var_of tbl) bs ->
    exists b, Den_body var_of tbl bs b.
  Proof.
    intros bs [-> | (cb & ->)] Hk.
    - exists e_unit. apply DBo_none.
    - inversion Hk as [| ? ? Hk1 _]; subst. simpl in Hk1.
      destruct Hk1 as (b & Hb). exists b. apply DBo_some. exact Hb.
  Qed.

  Lemma step_function : StepO R_function.
  Proof.
    intros cs H _ Hkids.
    destruct (shape_function cs H) as (kw & pso & bs & -> & Hpso & Hbs).
    apply Forall_app in Hkids as [_ Hk1]. apply Forall_app in Hk1 as [Hkps Hk2].
    apply Forall_app in Hk2 as [_ Hk3]. apply Forall_app in Hk3 as [Hkbs _].
    destruct (loop_body_den bs Hbs Hkbs) as (body & Hbody).
    destruct Hpso as [-> | (ps & ->)].
    - destruct (atom_fresh (fv_exp body)) as [s Hs].
      simpl. exists (unit_arg s body).
      exact (D_function_unit var_of tbl kw bs body s Hbody Hs).
    - inversion Hkps as [| ? ? Hps _]; subst. simpl in Hps. destruct Hps as (xs & Hxs).
      destruct Hbs as [-> | (cb & ->)].
      + simpl. exists (curry (List.map var_of xs) e_unit).
        exact (D_function_empty var_of tbl kw ps xs Hxs).
      + inversion Hbody; subst. simpl. exists (curry (List.map var_of xs) body).
        apply D_function; assumption.
  Qed.

  Lemma step_record : Step R_record.
  Proof.
    intros cs H _ _ Hcomplete Hkids. simpl in Hcomplete.
    destruct (shape_record cs H) as
      (rest & -> & [-> | [(c & tail & fin & -> & Htail & Hfin)
                         | (c & tail & fin & -> & Htail & Hfin)]]).
    - (* no fields *)
      simpl. exists (e_rec fs_nil). apply D_record. apply DI_end.
    - (* a first field and the rest *)
      inversion Hkids as [| ? ? _ Hrest]; subst.
      inversion Hrest as [| ? ? Hfield Hmore]; subst. simpl in Hfield.
      destruct Hfield as (l & e & Hf).
      apply Forall_app in Hmore as [Hktail Hkfin].
      assert (Hplain : Forall not_spread tail).
      { simpl in Hcomplete. inversion Hcomplete as [| ? ? _ Hc0]; subst.
        inversion Hc0 as [| ? ? _ Hc]; subst.
        apply Forall_app in Hc as [Hc _]. exact Hc. }
      destruct (sep_den var_of tbl fin tail Hfin Htail Hktail Hplain) as (fs & Hsep).
      simpl. exists (e_rec (fs_cons (lab tbl l) e fs)).
      apply D_record. apply DI_field with (l := l) (e := e); assumption.
    - (* a spread, then fields *)
      inversion Hkids as [| ? ? _ Hrest]; subst.
      inversion Hrest as [| ? ? Hspread Hmore]; subst. simpl in Hspread.
      destruct Hspread as (cx & base & -> & Hbase).
      apply Forall_app in Hmore as [Hktail Hkfin].
      assert (Hplain : Forall not_spread tail).
      { simpl in Hcomplete. apply Forall_app in Hcomplete as [Hc _]. exact Hc. }
      destruct (sep_den var_of tbl fin tail Hfin Htail Hktail Hplain) as (fs & Hsep).
      simpl. exists (spread_nest base fs).
      apply D_spread_record; assumption.
  Qed.

  Lemma step_spread : StepO R_spread.
  Proof.
    intros cs H _ Hkids.
    destruct (shape_spread cs H) as (c & ->).
    rewrite Forall_forall in Hkids.
    assert (Hv : TotKind var_of tbl (Node R_expr c)) by (apply Hkids; in_list).
    simpl in Hv. destruct Hv as (e & Hden).
    simpl. exists c, e. split; [ reflexivity | exact Hden ].
  Qed.

  Lemma step_destructure : StepO R_destructure.
  Proof.
    intros cs H _ Hkids.
    destruct (shape_destructure cs H) as (ps & xs & ro & vs & semi & bs & -> & Hsemi & Hpat & Hbs).
    assert (Hv : TotKind var_of tbl (Node R_value vs)).
    { rewrite Forall_forall in Hkids. apply Hkids. apply in_or_app. left. in_list. }
    apply Forall_app in Hkids as [_ Hk1]. apply Forall_app in Hk1 as [_ Hkbs].
    simpl in Hv. destruct Hv as (v & Hdv).
    destruct Hbs as [-> | (cb & ->)].
    - destruct (fresh_source var_of e_unit (xs ++ match ro with Some r => [r] | None => [] end))
        as (s & _ & Hdistinct).
      simpl. exists (e_let v (close_exp s (unpack var_of tbl s xs ro
                                             (e_fvar_f (var_of (last_name xs ro)))))).
      rewrite app_nil_r.
      eapply D_destructure_end; eassumption.
    - inversion Hkbs as [| ? ? Hb _]; subst. simpl in Hb. destruct Hb as (body & Hdb).
      destruct (fresh_source var_of body (xs ++ match ro with Some r => [r] | None => [] end))
        as (s & Hfresh & Hdistinct).
      simpl. exists (e_let v (close_exp s (unpack var_of tbl s xs ro body))).
      eapply D_destructure; eassumption.
  Qed.

  Lemma step_local : StepO R_local.
  Proof.
    intros cs H _ Hkids.
    destruct (shape_local cs H) as (d & bs & -> & Hbs).
    inversion Hkids as [| ? ? Hd Hkbs]; subst. simpl in Hd.
    destruct Hd as (x & v & Hdecl).
    destruct (is_fn_decl (Node R_declaration d)) eqn:Hfn.
    - destruct Hbs as [-> | (cb & ->)].
      + simpl. exists (fn_place (var_of x) v (e_fvar_f (var_of x))).
        exact (D_local_fn_end var_of tbl _ x v Hdecl Hfn).
      + inversion Hkbs as [| ? ? Hb _]; subst. simpl in Hb. destruct Hb as (body & Hbody).
        simpl. exists (fn_place (var_of x) v body).
        exact (D_local_fn var_of tbl _ x v cb body Hdecl Hfn Hbody).
    - destruct Hbs as [-> | (cb & ->)].
      + simpl. exists (e_let v (close_exp (var_of x) (e_fvar_f (var_of x)))).
        exact (D_local_end var_of tbl _ x v Hdecl Hfn).
      + inversion Hkbs as [| ? ? Hb _]; subst. simpl in Hb. destruct Hb as (body & Hbody).
        simpl. exists (e_let v (close_exp (var_of x) body)).
        apply D_local with (x := x); assumption.
  Qed.

  Lemma step_declaration : StepO R_declaration.
  Proof.
    intros cs H _ Hkids.
    destruct (shape_declaration cs H) as (x & c & [-> | ->]);
      rewrite Forall_forall in Hkids;
      assert (Hv : TotKind var_of tbl (Node R_value c)) by (apply Hkids; in_list);
      simpl in Hv; destruct Hv as (v & Hden); simpl; exists x, v.
    - apply DD_plain. exact Hden.
    - apply DD_semi. exact Hden.
  Qed.

  Lemma step_field : StepO R_field.
  Proof.
    intros cs H _ Hkids.
    destruct (shape_field cs H) as (l & c & ->).
    rewrite Forall_forall in Hkids.
    assert (Hv : TotKind var_of tbl (Node R_expr c)) by (apply Hkids; in_list).
    simpl in Hv. destruct Hv as (e & Hden).
    simpl. exists l, e. apply DF. exact Hden.
  Qed.

  Lemma step_access : StepO R_access.
  Proof.
    intros cs H _ _. destruct (shape_access cs H) as (l & ->).
    simpl. exists l. reflexivity.
  Qed.

  Lemma step_take : StepO R_take.
  Proof.
    intros cs H _ _. destruct (shape_take cs H) as (l & ->).
    simpl. exists l. reflexivity.
  Qed.

  Lemma step_call : StepO R_call.
  Proof.
    intros cs H _ Hkids.
    destruct (shape_call cs H) as [-> | (args & ->)].
    - simpl. left. reflexivity.
    - rewrite Forall_forall in Hkids.
      assert (Ha : TotKind var_of tbl (Node R_arguments args)) by (apply Hkids; in_list).
      simpl in Ha. destruct Ha as (es & Hargs).
      simpl. right. exists args, es. split; [ reflexivity | exact Hargs ].
  Qed.

  Lemma step_arguments : StepO R_arguments.
  Proof.
    intros cs H _ Hkids. simpl.
    exact (arguments_den var_of tbl cs H Hkids).
  Qed.

  Lemma step_params : StepO R_params.
  Proof.
    intros cs H Hplain _.
    destruct (shape_params cs H Hplain) as (x & tail & -> & Htail & Hplaint).
    destruct (params_den var_of tbl tail Htail Hplaint x) as (xs & Hxs).
    simpl. exists (x :: xs). exact Hxs.
  Qed.

  Lemma var_or_not : forall e : exp,
    (exists x, e = e_fvar_f x) \/ (forall x, e <> e_fvar_f x).
  Proof.
    intros e. destruct e;
      first [ (left; eexists; reflexivity) | (right; intros x H; discriminate H) ].
  Qed.

  Lemma Den_tpat_head : forall p t xs, Den_tpat p t xs -> exists rest, p = ident t :: rest.
  Proof. intros p t xs H. inversion H; eexists; reflexivity. Qed.

  Lemma step_list : Step R_list.
  Proof.
    intros cs H _ Hknown _ Hkids. destruct Hknown as [HE HL].
    destruct (tag_lookup tags "Empty") as [[we tge] | ] eqn:Hempty; [ | exfalso; exact (HE eq_refl) ].
    destruct (tag_lookup tags "Link") as [[wl tgl] | ] eqn:Hlink; [ | exfalso; exact (HL eq_refl) ].
    destruct (shape_list cs H) as [-> | (args & ->)].
    - simpl. exists (e_con we tge e_unit). apply D_list_nil. exact Hempty.
    - rewrite Forall_forall in Hkids.
      assert (Ha : TotKind var_of tbl (Node R_arguments args)) by (apply Hkids; in_list).
      simpl in Ha. destruct Ha as (es & Hargs).
      simpl. exists (list_of we tge wl tgl es).
      apply D_list with (es := es); assumption.
  Qed.

  Lemma step_labels : StepO R_labels.
  Proof. intros cs H _ _. simpl. exact (shape_labels cs H). Qed.

  Lemma step_pattern : StepO R_pattern.
  Proof. intros cs H _ _. simpl. exact (shape_pattern cs H). Qed.

  Lemma step_literal_pattern : StepO R_literal_pattern.
  Proof.
    intros cs H _ Hkids.
    destruct (shape_literal_pattern cs H) as (c & x & -> & Hc).
    inversion Hkids as [| ? ? Hk _]; subst.
    assert (Hc' : exists e, Den var_of tbl c e).
    { destruct Hc as [-> | [-> | ->]]; exact Hk. }
    destruct Hc' as (e & Hden). simpl. exists c, e. split; [ reflexivity | exact Hden ].
  Qed.

  Lemma step_arm : Step R_arm.
  Proof.
    intros cs H Hcomplete Hknown _ Hkids.
    destruct (shape_arm cs H) as [(p & b & ->) | (p & b & ->)].
    - rewrite Forall_forall in Hkids.
      assert (Hp : TotKind var_of tbl (Node R_pattern p)) by (apply Hkids; in_list).
      assert (Hb : TotKind var_of tbl (Node R_expr b)) by (apply Hkids; in_list).
      simpl in Hp, Hb. destruct Hp as (t & xs & Hpat). destruct Hb as (body & Hbody).
      destruct (Den_tpat_head _ _ _ Hpat) as (rest & ->).
      simpl in Hknown.
      destruct (tag_lookup tags t) as [[w tg] | ] eqn:Hlook; [ | exfalso; exact (Hknown eq_refl) ].
      destruct (fresh_source var_of body xs) as (s & Hfresh & Hdistinct).
      simpl. exists w, tg, (close_exp s (slot_lets var_of s 0 xs body)).
      apply DArm with (t := t) (xs := xs) (cs := b) (body := body) (s := s); assumption.
    - rewrite Forall_forall in Hkids.
      assert (Hp : TotKind var_of tbl (Node R_literal_pattern p)) by (apply Hkids; in_list).
      assert (Hb : TotKind var_of tbl (Node R_expr b)) by (apply Hkids; in_list).
      simpl in Hp, Hb. destruct Hp as (c & l & Hc & Hl). destruct Hb as (body & Hbody).
      subst p. simpl. exists l, body. apply DLA; assumption.
  Qed.

  Lemma tag_arms_den : forall arms,
    gen (E_star (E_rule R_arm)) arms ->
    Forall (TotKind var_of tbl) arms -> Forall (fun t => is_tag_arm t = true) arms ->
    forall els ars_end, Den_arms var_of tbl els ars_end ->
    exists ars, Den_arms var_of tbl (arms ++ els) ars.
  Proof.
    intros arms H.
    apply (gen_star_ind (E_rule R_arm)
             (fun arms => Forall (TotKind var_of tbl) arms -> Forall (fun t => is_tag_arm t = true) arms ->
                forall els ars_end, Den_arms var_of tbl els ars_end ->
                exists ars, Den_arms var_of tbl (arms ++ els) ars));
      [ | | exact H ].
    - intros _ _ els ars_end Hels. exists ars_end. exact Hels.
    - intros ts1 ts2 H1 IH Hk Htag els ars_end Hels.
      apply Forall_app in Hk as [Hk1 Hk2]. apply Forall_app in Htag as [Ht1 Ht2].
      destruct (IH Hk2 Ht2 els ars_end Hels) as (ars & Hars).
      destruct (gen_node_of H1 eq_refl) as (c & -> & _).
      inversion Hk1 as [| ? ? Hk _]; subst.
      inversion Ht1 as [| ? ? Ht _]; subst.
      destruct c as [| [kp | rp cp] crest]; [ discriminate Ht | discriminate Ht | ].
      destruct rp; try discriminate Ht. simpl in Hk.
      destruct Hk as (w & tg & b & Harm).
      exists (arms_cons tg b ars). simpl.
      apply DAr_cons with (w := w); assumption.
  Qed.

  Lemma lit_arms_den : forall arms,
    gen (E_star (E_rule R_arm)) arms ->
    Forall (TotKind var_of tbl) arms -> Forall (fun t => is_lit_arm t = true) arms ->
    forall els rows e, Den_lit_arms var_of tbl els rows e ->
    exists rows', Den_lit_arms var_of tbl (arms ++ els) rows' e.
  Proof.
    intros arms H.
    apply (gen_star_ind (E_rule R_arm)
             (fun arms => Forall (TotKind var_of tbl) arms -> Forall (fun t => is_lit_arm t = true) arms ->
                forall els rows e, Den_lit_arms var_of tbl els rows e ->
                exists rows', Den_lit_arms var_of tbl (arms ++ els) rows' e));
      [ | | exact H ].
    - intros _ _ els rows e Hels. exists rows. exact Hels.
    - intros ts1 ts2 H1 IH Hk Hlit els rows e Hels.
      apply Forall_app in Hk as [Hk1 Hk2]. apply Forall_app in Hlit as [Hl1 Hl2].
      destruct (IH Hk2 Hl2 els rows e Hels) as (rows' & Hrows).
      destruct (gen_node_of H1 eq_refl) as (c & -> & _).
      inversion Hk1 as [| ? ? Hk _]; subst.
      inversion Hl1 as [| ? ? Hl _]; subst.
      destruct c as [| [kp | rp cp] crest]; [ discriminate Hl | discriminate Hl | ].
      destruct rp; try discriminate Hl. simpl in Hk.
      destruct Hk as (l & b & Harm).
      exists ((l, b) :: rows'). simpl.
      apply DLs_cons with (a := Node R_arm (Node R_literal_pattern cp :: crest)); assumption.
  Qed.

  Lemma app_shape : forall (l : list tree) a rest els d,
    l ++ (a :: rest) ++ els ++ d = l ++ a :: (rest ++ els) ++ d.
  Proof. intros l a rest els d. simpl. rewrite app_assoc. reflexivity. Qed.

  Lemma else_absent : forall c arms,
    Forall (fun t => exists cc, t = Node R_arm cc) arms ->
    ~ In (sym "else") ([sym "match"; Node R_expr c; sym "do"] ++ arms ++ [] ++ [sym "done"]).
  Proof.
    intros c arms Hnodes Hin. rewrite Forall_forall in Hnodes.
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    - simpl in Hin. repeat (destruct Hin as [Hin | Hin]; [ discriminate Hin | ]). contradiction.
    - apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      + destruct (Hnodes _ Hin) as (cc & Hcc). discriminate Hcc.
      + simpl in Hin. destruct Hin as [Hin | Hin]; [ discriminate Hin | contradiction ].
  Qed.

  Lemma step_match : Step R_match_expr.
  Proof.
    intros cs H Hcomplete Hknown _ Hkids. simpl in Hcomplete.
    destruct Hcomplete as [Harm_in Hkind].
    destruct (shape_match cs H) as (c & arms & els & Hcs & Harms & Hels).
    subst cs.
    pose proof (arm_nodes arms Harms) as Hnodes0.
    rewrite Forall_forall in Hkids.
    assert (Hscrut : TotKind var_of tbl (Node R_expr c)) by (apply Hkids; in_list).
    simpl in Hscrut. destruct Hscrut as (e & Hden).
    assert (Harmsk : Forall (TotKind var_of tbl) arms).
    { rewrite Forall_forall. intros t Ht. apply Hkids.
      apply in_or_app. right. apply in_or_app. left. exact Ht. }
    assert (Hend : exists ars_end, Den_arms var_of tbl els ars_end).
    { destruct Hels as [-> | (c2 & ->)].
      - exists arms_nil. apply DAr_nil.
      - assert (Hc2 : TotKind var_of tbl (Node R_expr c2)).
        { apply Hkids. apply in_or_app. right. apply in_or_app. right.
          apply in_or_app. left. in_list. }
        simpl in Hc2. destruct Hc2 as (e2 & Hden2).
        exists (arms_else e2). apply DAr_else. exact Hden2. }
    destruct arms as [| a rest].
    { exfalso. destruct Hels as [-> | (c2 & ->)]; absurd_has Harm_in. }
    pose proof Hnodes0 as Hnodes. rewrite Forall_forall in Hnodes.
    destruct (Hnodes a (or_introl eq_refl)) as (cc & Ha). subst a.
    destruct Hkind as [Htag | [Hlit Helse]].
    - assert (Htagarms : Forall (fun t => is_tag_arm t = true) (Node R_arm cc :: rest)).
      { rewrite Forall_forall. intros t Ht. destruct (Hnodes t Ht) as (cc' & ->).
        rewrite Forall_forall in Htag. apply Htag.
        - apply in_or_app. right. apply in_or_app. left. exact Ht.
        - reflexivity. }
      destruct Hend as (ars_end & Hend).
      destruct (tag_arms_den _ Harms Harmsk Htagarms els ars_end Hend) as (ars & Hars).
      simpl in Hars. inversion Hars; subst.
      rewrite app_shape. simpl.
      eexists. eapply D_match_tags; eassumption.
    - destruct Hels as [-> | (c2 & ->)].
      + exfalso. exact (else_absent c _ Hnodes0 Helse).
      + assert (Hc2 : TotKind var_of tbl (Node R_expr c2)).
        { apply Hkids. apply in_or_app. right. apply in_or_app. right.
          apply in_or_app. left. in_list. }
        simpl in Hc2. destruct Hc2 as (e2 & Hden2).
        assert (Hend' : Den_lit_arms var_of tbl [sym "else"; Node R_expr c2] [] e2)
          by (apply DLs_else; exact Hden2).
        assert (Hlitarms : Forall (fun t => is_lit_arm t = true) (Node R_arm cc :: rest)).
        { rewrite Forall_forall. intros t Ht. destruct (Hnodes t Ht) as (cc' & ->).
          rewrite Forall_forall in Hlit. apply Hlit.
          - apply in_or_app. right. apply in_or_app. left. exact Ht.
          - reflexivity. }
        destruct (lit_arms_den _ Harms Harmsk Hlitarms _ _ _ Hend') as (rows & Hrows).
        simpl in Hrows. rewrite app_shape. simpl.
        destruct (var_or_not e) as [(x & ->) | Hnot].
        * eexists. eapply D_match_lit_var; eassumption.
        * destruct (atom_fresh (fv_rows rows `union` fv_exp e2)) as (s & Hs).
          eexists. eapply D_match_lit_let; eassumption.
  Qed.

  Lemma step_repeat : StepO R_repeat_loop.
  Proof.
    intros cs H _ Hkids.
    destruct (shape_repeat cs H) as (cn & bs & -> & Hbs).
    assert (Hn : TotKind var_of tbl (Node R_expr cn))
      by (rewrite Forall_forall in Hkids; apply Hkids; in_list).
    apply Forall_app in Hkids as [_ Hk2]. apply Forall_app in Hk2 as [Hkbs _].
    simpl in Hn. destruct Hn as (n & Hdn).
    destruct (loop_body_den bs Hbs Hkbs) as (b & Hb).
    destruct (atom_fresh (loop_atoms (e_num 0) n b)) as [c Hc].
    destruct (exists_apart3 (loop_atoms (e_num 0) n b) c) as (s & t & g & Happ).
    simpl. exists (counted s t g c (e_num 0) n bop_lt b).
    apply (D_repeat var_of tbl cn n bs b s t g c Hdn Hb Hc Happ).
  Qed.

  Lemma step_count : StepO R_count_loop.
  Proof.
    intros cs H _ Hkids.
    destruct (shape_count cs H) as (x & kf & kt & ca & cz & bs & -> & Hf & Ht & Hbs).
    assert (Ha : TotKind var_of tbl (Node R_expr ca))
      by (rewrite Forall_forall in Hkids; apply Hkids; in_list).
    assert (Hz : TotKind var_of tbl (Node R_expr cz))
      by (rewrite Forall_forall in Hkids; apply Hkids; in_list).
    apply Forall_app in Hkids as [_ Hk2]. apply Forall_app in Hk2 as [Hkbs _].
    simpl in Ha, Hz. destruct Ha as (a & Hda). destruct Hz as (z & Hdz).
    destruct (loop_body_den bs Hbs Hkbs) as (b & Hb).
    destruct (exists_apart3 (loop_atoms a z b) (var_of x)) as (s & t & g & Happ).
    simpl. exists (counted s t g (var_of x) a z bop_lte b).
    apply (D_count var_of tbl x kf kt ca cz a z bs b s t g Hf Ht Hda Hdz Hb Happ).
  Qed.

  Lemma step_each : Step R_each_loop.
  Proof.
    intros cs H _ Hknown _ Hkids. destruct Hknown as (w & tge & tgl & HE & HL).
    destruct (shape_each cs H) as (x & ki & cl & bs & -> & Hi & Hbs).
    assert (Hl : TotKind var_of tbl (Node R_expr cl))
      by (rewrite Forall_forall in Hkids; apply Hkids; in_list).
    apply Forall_app in Hkids as [_ Hk2]. apply Forall_app in Hk2 as [Hkbs _].
    simpl in Hl. destruct Hl as (xs & Hdl).
    destruct (loop_body_den bs Hbs Hkbs) as (b & Hb).
    destruct (exists_apart4 (fv_exp xs `union` fv_exp b) (var_of x)) as (g & r & sp & tp & Happ).
    simpl. exists (each_term w tge tgl g r sp tp (var_of x) xs b).
    apply (D_each var_of tbl x ki cl xs bs b w tge tgl g r sp tp Hi HE HL Hdl Hb Happ).
  Qed.

  Lemma step_all : forall r, Step r.
  Proof.
    intros r. destruct r;
      first
        [ exact (lift _ step_number) | exact (lift _ step_name) | exact (lift _ step_boolean)
        | exact (lift _ step_expr) | exact (lift _ step_value) | exact (lift _ step_function)
        | exact (lift _ step_string) | exact (lift _ step_conditional) | exact (lift _ step_negation)
        | exact step_record | exact (lift _ step_local) | exact (lift _ step_declaration)
        | exact (lift _ step_spread) | exact (lift _ step_destructure)
        | exact (lift _ step_field) | exact (lift _ step_access) | exact (lift _ step_take) | exact (lift _ step_call)
        | exact (lift _ step_arguments) | exact (lift _ step_params)
        | exact (lift _ step_pattern) | exact (lift _ step_labels)
        | exact (lift _ step_literal_pattern)
        | exact step_list | exact step_arm | exact step_match
        | exact (lift _ step_repeat) | exact (lift _ step_count) | exact step_each
        | (intros cs _ _ _ _ _; exact I) ].
  Qed.

  Theorem tot : forall t,
    valid t -> Complete t -> Known tags t -> Accepted t -> TotKind var_of tbl t.
  Proof.
    apply (tree_ind' (fun t => valid t -> Complete t -> Known tags t -> Accepted t -> TotKind var_of tbl t)).
    - intros k _ _ _ _. exact I.
    - intros r cs IH Hvalid Hcomplete Hknown Haccepted.
      destruct (silent r) eqn:Hsilent.
      + (* a silent rule never labels a node *)
        destruct r; first [ exact I | discriminate Hsilent ].
      + destruct (gen_node_inv Hvalid Hsilent) as (cs' & Hcs & _ & Hbody).
        injection Hcs as <-.
        inversion Hcomplete as [| ? ? Hnode Hcomplete_kids]; subst.
        inversion Hknown as [| ? ? Hknode Hknown_kids]; subst.
        inversion Haccepted as [| ? ? Hanode Haccepted_kids]; subst.
        assert (Hvalid_kids : Forall valid cs) by exact (gen_valid _ _ Hbody).
        assert (Hkids : Forall (TotKind var_of tbl) cs).
        { rewrite Forall_forall in *. intros c Hc.
          exact (IH c Hc (Hvalid_kids c Hc) (Hcomplete_kids c Hc) (Hknown_kids c Hc)
                   (Haccepted_kids c Hc)). }
        exact (step_all r cs Hbody Hnode Hknode Hanode Hkids).
  Qed.

End Steps.
