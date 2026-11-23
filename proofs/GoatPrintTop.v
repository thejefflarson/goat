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
Require Import Goat.GoatPrintInst.
Require Import Goat.GoatPrintDen.
Open Scope string_scope.
Open Scope list_scope.

(* The program's first token starts neither a tag declaration nor anything
   else the top rule tries first. *)
Lemma members_head : forall G P i fs rest d ds,
  0 < flen fs -> member_trees G P i fs ++ rest = d :: ds ->
  exists x v, d = decl_named x v /\ x <> "foreign".
Proof.
  intros G P i fs rest d ds Hlen H. destruct fs as [| l v rs | l v rs]; cbn [flen] in Hlen.
  - lia.
  - cbn [member_trees app] in H. injection H as <- _.
    exists (gm P i). eexists. split; [ reflexivity | exact (gm_not_foreign _ _) ].
  - cbn [member_trees app] in H. injection H as <- _.
    exists (gm P i). eexists. split; [ reflexivity | exact (gm_not_foreign _ _) ].
Qed.

Lemma decls_head : forall G P e d ds,
  scoped G P e -> decls G P e = d :: ds -> exists x v, d = decl_named x v /\ x <> "foreign".
Proof.
  intros G P e d ds Hs H. destruct e; try discriminate H.
  - cbn [decls] in H. injection H as <- _.
    exists (nm P). eexists. split; [ reflexivity | exact (nm_not_foreign _) ].
  - cbn [decls] in H. destruct Hs as [Hlen _]. exact (members_head _ _ _ _ _ d ds Hlen H).
Qed.

Lemma block_plain : forall G P e r,
  scoped G P e -> BlkAt G P e -> Stop r -> Plain (flats (block G P e) ++ r).
Proof.
  intros G P e r Hs HB Hr. rewrite (block_split e G P). rewrite flats_app, <- app_assoc.
  destruct (decls G P e) as [| d ds] eqn:Hd.
  - cbn [flats flat_map app]. exact (fin_plain _ _ (proj1 HB) Hr).
  - destruct (decls_head G P e d ds Hs Hd) as (x & v & -> & Hx).
    rewrite flats_cons. unfold decl_named. flat_simp. exact Hx.
Qed.

Lemma goat_parses : forall e,
  scoped [] 0 e ->
  peg (E_rule R_goat) (print e) (Ok [print_tree e] []).
Proof.
  intros e Hs.
  assert (HB : BlkAt [] 0 e) by exact (proj1 blk_all e [] 0 Hs).
  assert (Hexpr : ExprParses (block [] 0 e)) by exact (expr_parses [] 0 e HB).
  assert (Hplain : Plain (flats (block [] 0 e) ++ [])) by exact (block_plain [] 0 e [] Hs HB Stop_nil).
  unfold print, print_tree. rewrite <- (app_nil_r (flats (block [] 0 e))).
  pok ltac:(first
    [ (eapply plain_tag; exact Hplain)
    | (eapply Hexpr; constructor) ]).
Qed.

Lemma inst_closed : forall var_of,
  (forall e G k, scoped G k e -> inst_rec var_of G k 0 e = e) /\
  (forall fs G k, scoped_fields G k fs -> inst_fields var_of G k 0 fs = fs) /\
  (forall ars : arms, True).
Proof.
  intros var_of. apply exp_fields_mutind.
  - intros i G k (Hi & _). cbn [inst_rec].
    destruct (Nat.ltb i k) eqn:Hik; [ reflexivity | ].
    apply Nat.ltb_ge in Hik. lia.
  - intros y G k Hs. destruct Hs.
  - intros n G k Hs. reflexivity.
  - intros d G k Hs. reflexivity.
  - intros G k Hs. reflexivity.
  - intros G k Hs. reflexivity.
  - intros b IH G k Hs. simpl in Hs. cbn [inst_rec].
    destruct Hs as [-> | Hs]; [ reflexivity | ].
    rewrite (IH G (S k) Hs). reflexivity.
  - intros a IHa b IHb G k [Ha Hb]. cbn [inst_rec]. rewrite (IHa G k Ha).
    destruct Hb as [-> | Hb]; [ reflexivity | ].
    rewrite (IHb G k Hb). reflexivity.
  - intros a IHa b IHb G k (Ha & Hb & _). cbn [inst_rec].
    rewrite (IHa G k Ha), (IHb G (S k) Hb). reflexivity.
  - intros fs IHfs b IHb G k (Hlen & Hgrp & Hb & _). cbn [inst_rec].
    rewrite Nat.add_0_r.
    rewrite (IHfs _ (S k) (scoped_group_fields _ _ _ _ Hgrp)), (IHb _ (S k) Hb). reflexivity.
  - intros fs IH G k Hs. cbn [inst_rec]. rewrite (IH G k Hs). reflexivity.
  - intros a IH l G k Hs.
    destruct (bvar_or_not a) as [[i ->] | Hnb].
    + destruct Hs as [Hi _]. cbn [inst_rec].
      destruct (Nat.ltb i k) eqn:Hik; [ reflexivity | ].
      apply Nat.ltb_ge in Hik. lia.
    + rewrite (inst_proj_other var_of G k 0 a l Hnb), (IH G k (scoped_proj_other _ _ _ _ Hnb Hs)).
      reflexivity.
  - intros G k Hs. destruct Hs.
  - intros q G k Hs. reflexivity.
  - intros a IHa b IHb c IHc G k (Ha & Hb & Hc). cbn [inst_rec].
    rewrite (IHa G k Ha), (IHb G k Hb).
    destruct Hc as [-> | Hc]; [ reflexivity | rewrite (IHc G k Hc); reflexivity ].
  - intros a IHa o b IHb G k [Ha Hb]. cbn [inst_rec]. rewrite (IHa G k Ha), (IHb G k Hb). reflexivity.
  - intros a IH G k Hs. destruct Hs.
  - intros w tg a IH G k Hs. destruct Hs.
  - intros w a IHa ars IHars G k Hs. destruct Hs.
  - intros a IHa l b IHb G k [Ha Hb]. cbn [inst_rec]. rewrite (IHa G k Ha), (IHb G k Hb). reflexivity.
  - intros a IH l G k Hs. destruct Hs.
  - intros a IH G k Hs. destruct Hs.
  - intros a IH G k Hs. destruct Hs.
  - intros G k Hs. reflexivity.
  - intros l e IHe fs IHfs G k [He Hfs]. cbn [inst_fields].
    rewrite (IHe G k He), (IHfs G k Hfs). reflexivity.
  - intros l e IHe fs IHfs G k Hs. destruct Hs.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
Qed.
