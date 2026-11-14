(* The printed block of every closed term parses as an expression, with every
   ordered choice committing to the right alternative. *)

From Coq Require Import String List.
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
Lemma decl_parses : forall P kv rest,
  Fin kv ->
  peg (E_rule R_declaration) (flat (decl_tree P kv) ++ rest)
      (Ok [decl_tree P kv] rest).
Proof.
  intros P kv rest Hc. unfold decl_tree. flat_simp.
  pok ltac:(first
    [ exact (fin_value _ _ Hc (Stop_semi _))
    | (eapply plain_foreign; exact (fin_plain _ _ Hc (Stop_semi _))) ]).
Qed.

(* ---- the bindings and the final statement of a block ---- *)

Fixpoint decls (P : nat) (e : exp) {struct e} : list tree :=
  match e with
  | e_let v b => decl_tree P (as_value v (block P v)) :: decls (S P) b
  | _ => []
  end.

Fixpoint fin (P : nat) (e : exp) {struct e} : list tree :=
  match e with
  | e_let _ b => fin (S P) b
  | _ => block P e
  end.

Definition NonLet (e : exp) : Prop :=
  match e with e_let _ _ => False | _ => True end.

(* Whether the block's last statement is an operation. *)
Fixpoint bin_end (e : exp) : bool :=
  match e with
  | e_bin _ _ _ => true
  | e_let _ b => bin_end b
  | _ => false
  end.

Lemma block_split : forall e P, block P e = decls P e ++ fin P e.
Proof.
  fix IH 1. intros e P. destruct e; try reflexivity.
  cbn [block decls fin]. rewrite (IH e2 (S P)). reflexivity.
Qed.

Lemma decls_nonlet : forall P e, NonLet e -> decls P e = [].
Proof. intros P e H. destruct e; first [ contradiction | reflexivity ]. Qed.

Lemma fin_nonlet : forall P e, NonLet e -> fin P e = block P e.
Proof. intros P e H. destruct e; first [ contradiction | reflexivity ]. Qed.

(* The block's last statement is a chain, and its bindings are read one after
   another until the statement, which is not a binding, ends them. *)
Definition BlkAt (P : nat) (e : exp) : Prop :=
  Fin (fin P e) /\ (bin_end e = false -> Chain (fin P e)) /\
  forall r, StopE r ->
    peg (E_star (E_rule R_declaration))
        (flats (decls P e) ++ flats (fin P e) ++ r)
        (Ok (decls P e) (flats (fin P e) ++ r)).

Lemma blk_nonlet : forall P e, NonLet e -> Fin (block P e) ->
  (bin_end e = false -> Chain (block P e)) -> BlkAt P e.
Proof.
  intros P e Hn Hf Hc. rewrite <- (fin_nonlet P e Hn) in Hf, Hc.
  split; [ exact Hf | split; [ exact Hc | ] ].
  intros r Hr. rewrite (decls_nonlet P e Hn).
  eapply P_star_stop. apply notdecl_fail.
  apply fin_notdecl; [ exact Hf | apply stop_of_stopE; exact Hr ].
Qed.

Lemma blk_chain : forall P e, NonLet e -> Chain (block P e) -> BlkAt P e.
Proof.
  intros P e Hn Hc. apply blk_nonlet; [ exact Hn | left; exact Hc | intros _; exact Hc ].
Qed.

Lemma expr_parses : forall P e, BlkAt P e -> ExprParses (block P e).
Proof.
  intros P e [Hfin [_ Hstar]] r Hr.
  rewrite (block_split e P), flats_app, <- app_assoc.
  specialize (Hstar r Hr).
  assert (Hstop : Stop r) by (apply stop_of_stopE; exact Hr).
  destruct (decls P e) as [| d ds].
  - inversion Hr; subst; cbn [flats flat_map app] in *;
      pok ltac:(first
        [ exact (fin_statement _ _ Hfin Hstop)
        | (eapply notdecl_fail; exact (fin_notdecl _ _ Hfin Hstop)) ]).
  - inversion Hr; subst;
      pok ltac:(first
        [ exact (fin_statement _ _ Hfin Hstop)
        | exact (plus_of_star _ _ _ _ _ Hstar) ]).
Qed.

Lemma operand_chain : forall P f, BlkAt P f -> Chain (as_operand f (block P f)).
Proof.
  intros P f HB. destruct f; cbn [as_operand];
    first
    [ exact (chain_prim _ (prim_paren _ (expr_parses P _ HB)))
    | exact (proj1 (proj2 HB) eq_refl) ].
Qed.

Lemma callee_chain : forall P f, BlkAt P f -> Chain (as_callee f (block P f)).
Proof.
  intros P f HB. destruct f; cbn [as_callee as_operand];
    first
    [ exact (chain_prim _ (prim_paren _ (expr_parses P _ HB)))
    | exact (proj1 (proj2 HB) eq_refl) ].
Qed.

Lemma value_fin : forall P v, BlkAt P v -> Fin (as_value v (block P v)).
Proof.
  intros P v HB. destruct v; cbn [as_value];
    first
    [ exact (or_introl (chain_prim _ (prim_paren _ (expr_parses P _ HB))))
    | exact (proj1 HB) ].
Qed.

Lemma binop_chain : forall P f, BlkAt P f -> Chain (as_binop f (block P f)).
Proof.
  intros P f HB. destruct f; cbn [as_binop];
    first
    [ exact (chain_prim _ (prim_paren _ (expr_parses P _ HB)))
    | exact (proj1 (proj2 HB) eq_refl) ].
Qed.

Definition Blk (e : exp) : Prop := forall n P, scoped n e -> BlkAt P e.
Definition FieldsOK (fs : Goat_ott.fields) : Prop :=
  forall n P, scoped_fields n fs -> AllExpr P fs.

Lemma blk_all : (forall e, Blk e) /\ (forall fs, FieldsOK fs).
Proof.
  apply exp_fields_mutind.
  - (* bound variable *)
    intros i n P Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ (prim_name _)).
  - (* free variable: not in a closed term *)
    intros y n P Hs. destruct Hs.
  - intros k n P Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ (prim_number _)).
  - (* decimal literal: not in the printable fragment *)
    intros d n P Hs. destruct Hs.
  - intros n P Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ prim_true).
  - intros n P Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ prim_false).
  - (* program *)
    intros b IHb n P Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ (prim_function _ _ (expr_parses _ _ (IHb (S n) (S P) Hs)))).
  - (* call *)
    intros f IHf a IHa n P [Hf Ha]. apply blk_chain; [ exact I | ].
    exact (chain_snoc _ _ (callee_chain _ _ (IHf n P Hf))
             (post_call _ (expr_parses _ _ (IHa n P Ha)))).
  - (* binding *)
    intros v IHv b IHb n P [Hv Hb].
    destruct (IHb (S n) (S P) Hb) as [Hfin [Hch Hstar]].
    split; [ exact Hfin | split; [ exact Hch | ] ].
    intros r Hr. cbn [decls fin]. rewrite flats_cons, <- app_assoc.
    eapply peg_star_cons;
      [ apply decl_parses; exact (value_fin _ _ (IHv n P Hv))
      | exact (Hstar r Hr) | reflexivity ].
  - (* record *)
    intros fs IHfs n P Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ (prim_record _ _ (IHfs n P Hs))).
  - (* projection *)
    intros f IHf l n P Hf. apply blk_chain; [ exact I | ].
    exact (chain_snoc _ _ (operand_chain _ _ (IHf n P Hf)) (post_access _)).
  - (* unit: not a term of the printed fragment *)
    intros n P Hs. destruct Hs.
  - (* string *)
    intros q n P Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ prim_string).
  - (* conditional *)
    intros c IHc a IHa b IHb n P [Hc [Ha Hb]]. apply blk_chain; [ exact I | ].
    exact (chain_prim _ (prim_conditional _ _ _
             (expr_parses _ _ (IHc n P Hc)) (expr_parses _ _ (IHa n P Ha))
             (expr_parses _ _ (IHb n P Hb)))).
  - (* operation *)
    intros a IHa o b IHb n P [Ha Hb].
    apply blk_nonlet; [ exact I | | intros Hx; discriminate Hx ].
    right. exists (as_binop a (block P a)), o, (as_binop b (block P b)).
    split; [ reflexivity | ].
    split; [ exact (binop_chain _ _ (IHa n P Ha)) | exact (binop_chain _ _ (IHb n P Hb)) ].
  - intros n P Hs. exact I.
  - intros l e IHe rest IHrest n P [He Hrest].
    split; [ exact (expr_parses _ _ (IHe n P He)) | exact (IHrest n P Hrest) ].
Qed.
