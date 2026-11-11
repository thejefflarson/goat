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
  Chain kv ->
  peg (E_rule R_declaration) (flat (decl_tree P kv) ++ rest)
      (Ok [decl_tree P kv] rest).
Proof.
  intros P kv rest Hc. unfold decl_tree. flat_simp.
  pok ltac:(first
    [ exact (chain_value _ _ Hc (Stop_semi _))
    | (eapply plain_foreign; exact (chain_plain _ _ Hc (Stop_semi _))) ]).
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
  Chain (fin P e) /\
  forall r, StopE r ->
    peg (E_star (E_rule R_declaration))
        (flats (decls P e) ++ flats (fin P e) ++ r)
        (Ok (decls P e) (flats (fin P e) ++ r)).

Lemma blk_chain : forall P e, NonLet e -> Chain (block P e) -> BlkAt P e.
Proof.
  intros P e Hn Hc. rewrite <- (fin_nonlet P e Hn) in Hc.
  split; [ exact Hc | ].
  intros r Hr. rewrite (decls_nonlet P e Hn).
  eapply P_star_stop. apply notdecl_fail.
  apply chain_notdecl; [ exact Hc | apply stop_of_stopE; exact Hr ].
Qed.

Lemma expr_parses : forall P e, BlkAt P e -> ExprParses (block P e).
Proof.
  intros P e [Hchain Hstar] r Hr.
  rewrite (block_split e P), flats_app, <- app_assoc.
  specialize (Hstar r Hr).
  assert (Hstop : Stop r) by (apply stop_of_stopE; exact Hr).
  destruct (decls P e) as [| d ds].
  - inversion Hr; subst; cbn [flats flat_map app] in *;
      pok ltac:(first
        [ exact (chain_statement _ _ Hchain Hstop)
        | (eapply notdecl_fail; exact (chain_notdecl _ _ Hchain Hstop)) ]).
  - inversion Hr; subst;
      pok ltac:(first
        [ exact (chain_statement _ _ Hchain Hstop)
        | exact (plus_of_star _ _ _ _ _ Hstar) ]).
Qed.

Lemma operand_chain : forall P f, BlkAt P f -> Chain (as_operand f (block P f)).
Proof.
  intros P f HB. destruct f; cbn [as_operand];
    first
    [ exact (chain_prim _ (prim_paren _ (expr_parses P _ HB)))
    | exact (proj1 HB) ].
Qed.

Lemma value_chain : forall P v, BlkAt P v -> Chain (as_value v (block P v)).
Proof.
  intros P v HB. destruct v; cbn [as_value];
    first
    [ exact (chain_prim _ (prim_paren _ (expr_parses P _ HB)))
    | exact (proj1 HB) ].
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
  - intros n P Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ prim_true).
  - intros n P Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ prim_false).
  - (* program *)
    intros b IHb n P Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ (prim_function _ _ (expr_parses _ _ (IHb (S n) (S P) Hs)))).
  - (* call *)
    intros f IHf a IHa n P [Hf Ha]. apply blk_chain; [ exact I | ].
    exact (chain_snoc _ _ (operand_chain _ _ (IHf n P Hf))
             (post_call _ (expr_parses _ _ (IHa n P Ha)))).
  - (* binding *)
    intros v IHv b IHb n P [Hv Hb].
    destruct (IHb (S n) (S P) Hb) as [Hchain Hstar].
    split; [ exact Hchain | ].
    intros r Hr. cbn [decls fin]. rewrite flats_cons, <- app_assoc.
    eapply peg_star_cons;
      [ apply decl_parses; exact (value_chain _ _ (IHv n P Hv))
      | exact (Hstar r Hr) | reflexivity ].
  - (* record *)
    intros fs IHfs n P Hs. apply blk_chain; [ exact I | ].
    exact (chain_prim _ (prim_record _ _ (IHfs n P Hs))).
  - (* projection *)
    intros f IHf l n P Hf. apply blk_chain; [ exact I | ].
    exact (chain_snoc _ _ (operand_chain _ _ (IHf n P Hf)) (post_access _)).
  - intros n P Hs. exact I.
  - intros l e IHe rest IHrest n P [He Hrest].
    split; [ exact (expr_parses _ _ (IHe n P He)) | exact (IHrest n P Hrest) ].
Qed.
