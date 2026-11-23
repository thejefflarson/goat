(* The printed block of every closed term parses as an expression, with every
   ordered choice committing to the right alternative. *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatPegTac.
Require Import Goat.GoatDen.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintChain.
Require Import Goat.GoatPrintPrim.
Require Import Goat.GoatPrintBlock.
Open Scope string_scope.
Open Scope list_scope.

Lemma chain_prim : forall H, PrimOK H -> Chain H.
Proof.
  intros H Hprim. exists H, []. split; [ symmetry; apply app_nil_r | ].
  split; [ exact Hprim | constructor ].
Qed.

Lemma plus_of_star : forall a s t ts s',
  peg (E_star a) s (Ok (t :: ts) s') -> peg (E_plus a) s (Ok (t :: ts) s').
Proof.
  intros a s t ts s' H.
  destruct (inv_star H) as [(_ & Hr) | (ts1 & s1 & ts' & s2 & Ha & Hs & Hr)];
    [ discriminate Hr | ].
  apply P_plus. rewrite Hr.
  exact (P_seq a (E_star a) s ts1 s1 (Ok ts' s2) Ha Hs).
Qed.

(* A binding: [name = value ;]. *)
Lemma decl_named_parses : forall x kv rest,
  Fin kv ->
  peg (E_rule R_declaration) (flat (decl_named x kv) ++ rest)
      (Ok [decl_named x kv] rest).
Proof.
  intros x kv rest Hc. unfold decl_named. flat_simp.
  pok ltac:(first
    [ exact (fin_value _ _ Hc (Stop_semi _))
    | (eapply plain_foreign; exact (fin_plain _ _ Hc (Stop_semi _))) ]).
Qed.

Lemma decl_parses : forall P kv rest,
  Fin kv ->
  peg (E_rule R_declaration) (flat (decl_tree P kv) ++ rest)
      (Ok [decl_tree P kv] rest).
Proof. intros P kv rest Hc. exact (decl_named_parses (nm P) kv rest Hc). Qed.

(* ---- the bindings and the final statement of a block ---- *)

(* A group's members are the bindings that open its block, then the bindings
   of the body. *)
Fixpoint decls (G : Grp) (P : nat) (e : exp) {struct e} : list tree :=
  match e with
  | e_let v b => decl_tree P (as_value v (block G P v)) :: decls G (S P) b
  | e_letrec fs b =>
      member_trees ((P, flen fs) :: G) P 0 fs ++ decls ((P, flen fs) :: G) (S P) b
  | _ => []
  end.

Fixpoint fin (G : Grp) (P : nat) (e : exp) {struct e} : list tree :=
  match e with
  | e_let _ b => fin G (S P) b
  | e_letrec fs b => fin ((P, flen fs) :: G) (S P) b
  | _ => block G P e
  end.

Definition NonLet (e : exp) : Prop :=
  match e with e_let _ _ | e_letrec _ _ => False | _ => True end.

(* Whether the block's last statement is an operation. *)
Fixpoint bin_end (e : exp) : bool :=
  match e with
  | e_bin _ _ _ => true
  | e_let _ b => bin_end b
  | e_letrec _ b => bin_end b
  | _ => false
  end.

Lemma block_split : forall e G P, block G P e = decls G P e ++ fin G P e.
Proof.
  fix IH 1. intros e G P. destruct e; try reflexivity.
  - cbn [block decls fin]. rewrite (IH _ G (S P)). reflexivity.
  - cbn [block decls fin]. rewrite (IH _ ((P, flen _) :: G) (S P)), app_assoc. reflexivity.
Qed.

Lemma decls_nonlet : forall G P e, NonLet e -> decls G P e = [].
Proof. intros G P e H. destruct e; first [ contradiction | reflexivity ]. Qed.

Lemma fin_nonlet : forall G P e, NonLet e -> fin G P e = block G P e.
Proof. intros G P e H. destruct e; first [ contradiction | reflexivity ]. Qed.

(* The block's last statement is a chain, and its bindings are read one after
   another until the statement, which is not a binding, ends them. *)
Definition BlkAt (G : Grp) (P : nat) (e : exp) : Prop :=
  Fin (fin G P e) /\ (bin_end e = false -> Chain (fin G P e)) /\
  forall r, StopE r ->
    peg (E_star (E_rule R_declaration))
        (flats (decls G P e) ++ flats (fin G P e) ++ r)
        (Ok (decls G P e) (flats (fin G P e) ++ r)).

Lemma blk_nonlet : forall G P e, NonLet e -> Fin (block G P e) ->
  (bin_end e = false -> Chain (block G P e)) -> BlkAt G P e.
Proof.
  intros G P e Hn Hf Hc. rewrite <- (fin_nonlet G P e Hn) in Hf, Hc.
  split; [ exact Hf | split; [ exact Hc | ] ].
  intros r Hr. rewrite (decls_nonlet G P e Hn).
  eapply P_star_stop. apply notdecl_fail.
  apply fin_notdecl; [ exact Hf | apply stop_of_stopE; exact Hr ].
Qed.

Lemma blk_chain : forall G P e, NonLet e -> Chain (block G P e) -> BlkAt G P e.
Proof.
  intros G P e Hn Hc. apply blk_nonlet; [ exact Hn | left; exact Hc | intros _; exact Hc ].
Qed.

Lemma expr_parses : forall G P e, BlkAt G P e -> ExprParses (block G P e).
Proof.
  intros G P e [Hfin [_ Hstar]] r Hr.
  rewrite (block_split e G P), flats_app, <- app_assoc.
  specialize (Hstar r Hr).
  assert (Hstop : Stop r) by (apply stop_of_stopE; exact Hr).
  destruct (decls G P e) as [| d ds].
  - inversion Hr; subst; cbn [flats flat_map app] in *;
      pok ltac:(first
        [ exact (fin_statement _ _ Hfin Hstop)
        | (eapply notdecl_fail; exact (fin_notdecl _ _ Hfin Hstop)) ]).
  - inversion Hr; subst;
      pok ltac:(first
        [ exact (fin_statement _ _ Hfin Hstop)
        | exact (plus_of_star _ _ _ _ _ Hstar) ]).
Qed.

Lemma operand_chain : forall G P f, BlkAt G P f -> Chain (as_operand f (block G P f)).
Proof.
  intros G P f HB. destruct f; cbn [as_operand];
    first
    [ exact (chain_prim _ (prim_paren _ (expr_parses G P _ HB)))
    | exact (proj1 (proj2 HB) eq_refl) ].
Qed.

Lemma callee_chain : forall G P f, BlkAt G P f -> Chain (as_callee f (block G P f)).
Proof.
  intros G P f HB. destruct f; cbn [as_callee as_operand];
    first
    [ exact (chain_prim _ (prim_paren _ (expr_parses G P _ HB)))
    | exact (proj1 (proj2 HB) eq_refl) ].
Qed.

Lemma value_fin : forall G P v, BlkAt G P v -> Fin (as_value v (block G P v)).
Proof.
  intros G P v HB. destruct v; cbn [as_value];
    first
    [ exact (or_introl (chain_prim _ (prim_paren _ (expr_parses G P _ HB))))
    | exact (proj1 HB) ].
Qed.

Lemma binop_chain : forall G P f, BlkAt G P f -> Chain (as_binop f (block G P f)).
Proof.
  intros G P f HB. destruct f; cbn [as_binop];
    first
    [ exact (chain_prim _ (prim_paren _ (expr_parses G P _ HB)))
    | exact (proj1 (proj2 HB) eq_refl) ].
Qed.

(* Every member of a group is a binding whose value is one chain: the
   function. *)
Fixpoint MemFin (G : Grp) (P : nat) (fs : Goat_ott.fields) {struct fs} : Prop :=
  match fs with
  | fs_nil => True
  | fs_cons _ v rest => Fin (block G P v) /\ MemFin G P rest
  | fs_meth _ v rest => Fin (block G P v) /\ MemFin G P rest
  end.

Lemma star_members : forall G P fs i ds r,
  MemFin G (S P) fs ->
  peg (E_star (E_rule R_declaration)) (flats ds ++ r) (Ok ds r) ->
  peg (E_star (E_rule R_declaration)) (flats (member_trees G P i fs ++ ds) ++ r)
      (Ok (member_trees G P i fs ++ ds) r).
Proof.
  intros G P fs. induction fs as [| l v rest IH | l v rest IH]; intros i ds r Hm Hstar.
  - exact Hstar.
  - destruct Hm as [Hv Hrest]. cbn [member_trees app]. rewrite flats_cons, <- app_assoc.
    eapply peg_star_cons;
      [ apply decl_named_parses; exact Hv
      | exact (IH _ _ _ Hrest Hstar) | reflexivity ].
  - destruct Hm as [Hv Hrest]. cbn [member_trees app]. rewrite flats_cons, <- app_assoc.
    eapply peg_star_cons;
      [ apply decl_named_parses; exact Hv
      | exact (IH _ _ _ Hrest Hstar) | reflexivity ].
Qed.

Lemma blk_letrec : forall G P fs b,
  MemFin ((P, flen fs) :: G) (S P) fs ->
  BlkAt ((P, flen fs) :: G) (S P) b ->
  BlkAt G P (e_letrec fs b).
Proof.
  intros G P fs b Hm [Hfin [Hch Hstar]].
  assert (Hd : decls G P (e_letrec fs b)
               = member_trees ((P, flen fs) :: G) P 0 fs ++ decls ((P, flen fs) :: G) (S P) b)
    by reflexivity.
  assert (Hf : fin G P (e_letrec fs b) = fin ((P, flen fs) :: G) (S P) b) by reflexivity.
  assert (Hbe : bin_end (e_letrec fs b) = bin_end b) by reflexivity.
  unfold BlkAt. rewrite Hd, Hf, Hbe.
  split; [ exact Hfin | split; [ exact Hch | ] ].
  intros r Hr. exact (star_members _ _ _ _ _ _ Hm (Hstar r Hr)).
Qed.

Definition Blk (e : exp) : Prop := forall G n, scoped G n e -> BlkAt G n e.
Definition FieldsOK (fs : Goat_ott.fields) : Prop :=
  (forall G n, scoped_fields G n fs -> AllExpr G n fs) /\
  (forall G n i, scoped_group G n i fs -> MemFin G n fs).

Lemma proj_plain : forall G n f l,
  scoped G n (e_proj f l) -> proj_level G n f = None -> scoped G n f.
Proof.
  intros G n f l Hs Hl. destruct f; try exact Hs.
  match goal with Hl : proj_level _ _ (e_fvar_b ?i) = None |- _ =>
    unfold proj_level in Hl; destruct (grp_size G (n - 1 - i)) eqn:E; [ discriminate Hl | ];
    split; [ exact (proj1 Hs) | exact E ] end.
Qed.

Lemma fin_abs : forall G P v, is_abs v -> fin G P v = block G P v.
Proof. intros G P v H. destruct v; first [ contradiction | reflexivity ]. Qed.

Lemma blk_all : (forall e, Blk e) /\ (forall fs, FieldsOK fs) /\ (forall ars : arms, True).
Proof.
  apply exp_fields_mutind.
  - (* bound variable *)
    intros i G n Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ (prim_name _ (nm_not_foreign _))).
  - (* free variable: not in a closed term *)
    intros y G n Hs. destruct Hs.
  - intros k G n Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ (prim_number _)).
  - intros d G n Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ (prim_decimal _)).
  - intros G n Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ prim_true).
  - intros G n Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ prim_false).
  - (* program *)
    intros b IHb G n Hs. apply blk_chain; [ exact I | ].
    destruct (block_abs_cases G n b) as [(-> & E) | (Hne & E)]; rewrite E.
    + exact (chain_prim _ (prim_function_empty _)).
    + destruct Hs as [Hs | Hs]; [ exfalso; exact (Hne Hs) | ].
      exact (chain_prim _ (prim_function _ _ (expr_parses _ _ _ (IHb G (S n) Hs)))).
  - (* call *)
    intros f IHf a IHa G n [Hf Ha]. apply blk_chain; [ exact I | ].
    destruct (block_app_cases G n f a) as [(-> & E) | (Hne & E)]; rewrite E.
    + exact (chain_snoc _ _ (callee_chain _ _ _ (IHf G n Hf)) post_call_unit).
    + destruct Ha as [Ha | Ha]; [ exfalso; exact (Hne Ha) | ].
      exact (chain_snoc _ _ (callee_chain _ _ _ (IHf G n Hf))
               (post_call _ (expr_parses _ _ _ (IHa G n Ha)))).
  - (* binding *)
    intros v IHv b IHb G n [Hv [Hb Hnr]].
    destruct (IHb G (S n) Hb) as [Hfin [Hch Hstar]].
    split; [ exact Hfin | split; [ exact Hch | ] ].
    intros r Hr. cbn [decls fin]. rewrite flats_cons, <- app_assoc.
    eapply peg_star_cons;
      [ apply decl_parses; exact (value_fin _ _ _ (IHv G n Hv))
      | exact (Hstar r Hr) | reflexivity ].
  - (* recursive group *)
    intros fs [IHfs IHgrp] b IHb G n [Hlen [Hgrp [Hb Hnr]]].
    apply blk_letrec; [ exact (IHgrp _ _ 0 Hgrp) | exact (IHb _ _ Hb) ].
  - (* record *)
    intros fs [IHfs _] G n Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ (prim_record _ _ _ (IHfs G n Hs))).
  - (* projection *)
    intros f IHf l G n Hs. apply blk_chain; [ exact I | ].
    destruct (proj_level G n f) eqn:EL.
    + rewrite (block_proj_group G n f l n0 EL).
      exact (chain_prim _ (prim_name _ (gm_not_foreign _ _))).
    + rewrite (block_proj_plain G n f l EL).
      exact (chain_snoc _ _ (operand_chain _ _ _ (IHf G n (proj_plain _ _ _ _ Hs EL)))
               (post_access _)).
  - (* unit: not a term of the printed fragment *)
    intros G n Hs. destruct Hs.
  - (* string *)
    intros q G n Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ prim_string).
  - (* conditional *)
    intros c IHc a IHa b IHb G n [Hc [Ha Hb]]. apply blk_chain; [ exact I | ].
    destruct (block_ite_cases G n c a b) as [(-> & E) | (Hne & E)]; rewrite E.
    + exact (chain_prim _ (prim_conditional_noelse _ _
               (expr_parses _ _ _ (IHc G n Hc)) (expr_parses _ _ _ (IHa G n Ha)))).
    + destruct Hb as [Hb | Hb]; [ exfalso; exact (Hne Hb) | ].
      exact (chain_prim _ (prim_conditional _ _ _
               (expr_parses _ _ _ (IHc G n Hc)) (expr_parses _ _ _ (IHa G n Ha))
               (expr_parses _ _ _ (IHb G n Hb)))).
  - (* operation *)
    intros a IHa o b IHb G n [Ha Hb].
    apply blk_nonlet; [ exact I | | intros Hx; discriminate Hx ].
    right. exists (as_binop a (block G n a)), o, (as_binop b (block G n b)).
    split; [ reflexivity | ].
    split; [ exact (binop_chain _ _ _ (IHa G n Ha)) | exact (binop_chain _ _ _ (IHb G n Hb)) ].
  - (* coercion: not a term of the printed fragment *)
    intros a IH G n Hs. destruct Hs.
  - (* tag construction: not a term of the printed fragment *)
    intros w tg a IH G n Hs. destruct Hs.
  - (* match: not a term of the printed fragment *)
    intros w a IHa ars IHars G n Hs. destruct Hs.
  - (* spread *)
    intros a IHa l b IHb G n [Ha Hb]. apply blk_chain; [ exact I | ].
    exact (chain_prim _ (prim_spread _ _ _ (expr_parses _ _ _ (IHa G n Ha))
                           (expr_parses _ _ _ (IHb G n Hb)))).
  - (* restrict: not a term of the printed fragment *)
    intros a IH l G n Hs. destruct Hs.
  - (* fold: not a term of the printed fragment *)
    intros a IH G n Hs. destruct Hs.
  - (* unfold: not a term of the printed fragment *)
    intros a IH G n Hs. destruct Hs.
  - split; [ intros G n Hs; exact I | intros G n i Hs; exact I ].
  - intros l e IHe rest [IHr IHg]. split.
    + intros G n [He Hrest].
      split; [ exact (expr_parses _ _ _ (IHe G n He)) | exact (IHr G n Hrest) ].
    + intros G n i (Hl & Hab & Hv & Hrest).
      split; [ | exact (IHg G n (S i) Hrest) ].
      rewrite <- (fin_abs G n e Hab). exact (proj1 (IHe G n Hv)).
  - (* a method field is not a term of the printed fragment *)
    intros l e IHe rest IHrest. split; intros G n; [ intros Hs | intros i Hs ]; destruct Hs.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
Qed.
