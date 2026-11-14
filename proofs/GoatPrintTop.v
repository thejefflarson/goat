(* The top rule parses a printed program, and reading the bound indices back is
   the identity on a closed term. *)

From Stdlib Require Import String List Arith Lia.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatPegTac.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintChain.
Require Import Goat.GoatPrintPrim.
Require Import Goat.GoatPrintBlock.
Require Import Goat.GoatPrintParse.
Require Import Goat.GoatPrintDen.
Open Scope string_scope.
Open Scope list_scope.

(* The program's first token starts neither a tag declaration nor anything
   else the top rule tries first. *)
Lemma block_plain : forall P e r,
  BlkAt P e -> Stop r -> Plain (flats (block P e) ++ r).
Proof.
  intros P e r HB Hr. destruct e;
    first
    [ (cbn [block]; unfold decl_tree; flat_simp; exact I)
    | exact (fin_plain _ _ (proj1 HB) Hr) ].
Qed.

Lemma goat_parses : forall e,
  scoped 0 e ->
  peg (E_rule R_goat) (print e) (Ok [print_tree e] []).
Proof.
  intros e Hs.
  assert (HB : BlkAt 0 e) by exact (proj1 blk_all e 0 0 Hs).
  assert (Hexpr : ExprParses (block 0 e)) by exact (expr_parses 0 e HB).
  assert (Hplain : Plain (flats (block 0 e) ++ [])) by exact (block_plain 0 e [] HB Stop_nil).
  unfold print, print_tree. rewrite <- (app_nil_r (flats (block 0 e))).
  pok ltac:(first
    [ (eapply plain_tag; exact Hplain)
    | (eapply Hexpr; constructor) ]).
Qed.

Lemma inst_closed : forall var_of,
  (forall e k, scoped k e -> inst_rec var_of k 0 e = e) /\
  (forall fs k, scoped_fields k fs -> inst_fields var_of k 0 fs = fs).
Proof.
  intros var_of. apply exp_fields_mutind.
  - intros i k Hs. simpl in Hs. cbn [inst_rec].
    destruct (Nat.ltb i k) eqn:Hik; [ reflexivity | ].
    apply Nat.ltb_ge in Hik. lia.
  - intros y k Hs. destruct Hs.
  - intros n k Hs. reflexivity.
  - intros d k Hs. destruct Hs.
  - intros k Hs. reflexivity.
  - intros k Hs. reflexivity.
  - intros b IH k Hs. simpl in Hs. cbn [inst_rec]. rewrite (IH (S k) Hs). reflexivity.
  - intros a IHa b IHb k [Ha Hb]. cbn [inst_rec]. rewrite (IHa k Ha), (IHb k Hb). reflexivity.
  - intros a IHa b IHb k [Ha Hb]. cbn [inst_rec]. rewrite (IHa k Ha), (IHb (S k) Hb). reflexivity.
  - intros fs IH k Hs. simpl in Hs. cbn [inst_rec]. rewrite (IH k Hs). reflexivity.
  - intros a IH l k Hs. simpl in Hs. cbn [inst_rec]. rewrite (IH k Hs). reflexivity.
  - intros k Hs. destruct Hs.
  - intros q k Hs. reflexivity.
  - intros a IHa b IHb c IHc k [Ha [Hb Hc]]. cbn [inst_rec].
    rewrite (IHa k Ha), (IHb k Hb), (IHc k Hc). reflexivity.
  - intros a IHa o b IHb k [Ha Hb]. cbn [inst_rec]. rewrite (IHa k Ha), (IHb k Hb). reflexivity.
  - intros k Hs. reflexivity.
  - intros l e IHe fs IHfs k [He Hfs]. cbn [inst_fields].
    rewrite (IHe k He), (IHfs k Hfs). reflexivity.
Qed.
