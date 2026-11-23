(* The tag declarations the printer writes parse as declarations, one case after
   another, each stopping where the next token cannot continue it. *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatPegTac.
Require Import Goat.GoatDen.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintArm.
Require Import Goat.GoatPrintChain.
Open Scope string_scope.
Open Scope list_scope.

(* What follows a declaration neither continues its cases nor, after a case
   with no slots, reads as the slots of that case. *)
Definition NotBar (r : list tok) : Prop :=
  match r with TSym x :: _ => x <> "|" | _ => True end.

Definition NotParen (r : list tok) : Prop :=
  match r with TSym x :: _ => x <> "(" | _ => True end.

Lemma notbar_fail : forall r, NotBar r -> peg (E_term (T_text "|")) r Fail.
Proof.
  intros r H. destruct r as [| [x | n | d | | y] r]; try (pfail nope; fail).
  apply text_fail. exact H.
Qed.

Lemma notparen_fail : forall r, NotParen r -> peg (E_term (T_text "(")) r Fail.
Proof.
  intros r H. destruct r as [| [x | n | d | | y] r]; try (pfail nope; fail).
  apply text_fail. exact H.
Qed.

Lemma type_parse : forall w c r,
  peg (E_rule R__type_expr) (flat (slot_tree w c) ++ r) (Ok [slot_tree w c] r).
Proof.
  intros w c r. unfold slot_tree. destruct (slot_name w c) as [n | ]; flat_simp; pok nope.
Qed.

Lemma star_types : forall w cs c r,
  peg (E_star (E_seq (E_term (T_text ",")) (E_rule R__type_expr)))
      (flats (sym "," :: slot_trees w (c :: cs)) ++ TSym ")" :: r)
      (Ok (sym "," :: slot_trees w (c :: cs)) (TSym ")" :: r)).
Proof.
  intros w cs. induction cs as [| c2 cs IH]; intros c r.
  - cbn [slot_trees]. flat_simp. pok ltac:(first [ exact (type_parse _ _ _) ]).
  - rewrite slot_trees_cons2. flat_simp. rewrite <- ?app_assoc.
    pok ltac:(first [ exact (type_parse _ _ _) | exact (IH _ _) ]).
Qed.

Lemma slots_parse : forall w c cs r,
  peg (E_seq (E_rule R__type_expr)
             (E_seq (E_star (E_seq (E_term (T_text ",")) (E_rule R__type_expr)))
                    (E_term (T_text ")"))))
      (flats (slot_trees w (c :: cs)) ++ TSym ")" :: r)
      (Ok (slot_trees w (c :: cs) ++ [sym ")"]) r).
Proof.
  intros w c cs r. destruct cs as [| c2 cs].
  - cbn [slot_trees]. flat_simp. pok ltac:(first [ exact (type_parse _ _ _) ]).
  - rewrite slot_trees_cons2. flat_simp. rewrite <- ?app_assoc.
    pok ltac:(first [ exact (type_parse _ _ _) | exact (star_types _ _ _ _) ]).
Qed.

Lemma case_parse : forall w tg cs r,
  (cs = [] -> NotParen r) ->
  peg (E_rule R_tag_case) (flat (case_tree w tg cs) ++ r) (Ok [case_tree w tg cs] r).
Proof.
  intros w tg cs r Hbare. unfold case_tree, case_kids. destruct cs as [| c cs].
  - flat_simp. pok ltac:(first [ exact (notparen_fail _ (Hbare eq_refl)) ]).
  - flat_simp. rewrite <- ?app_assoc.
    pok ltac:(first [ exact (slots_parse _ _ _ _) ]).
Qed.

Lemma notparen_more : forall w tg css r,
  NotParen r -> NotParen (flats (more_case_trees w tg css) ++ r).
Proof.
  intros w tg css r H. destruct css as [| cs css]; [ exact H | ].
  cbn [more_case_trees]. flat_simp. simpl. discriminate.
Qed.

Lemma more_cases_parse : forall css w tg r,
  NotBar r -> NotParen r ->
  peg (E_star (E_seq (E_term (T_text "|")) (E_expect (E_rule R_tag_case))))
      (flats (more_case_trees w tg css) ++ r) (Ok (more_case_trees w tg css) r).
Proof.
  induction css as [| cs css IH]; intros w tg r Hb Hp.
  - cbn [more_case_trees flats flat_map app]. pok ltac:(first [ exact (notbar_fail _ Hb) ]).
  - cbn [more_case_trees]. flat_simp. rewrite <- ?app_assoc.
    pok ltac:(first
      [ exact (IH _ _ _ Hb Hp)
      | exact (case_parse _ _ _ _ (fun _ => notparen_more _ _ _ _ Hp)) ]).
Qed.

Lemma decl_parse : forall w r,
  WfGroup w -> NotBar r -> NotParen r ->
  peg (E_rule R_tag_decl) (flat (tag_decl_tree w) ++ r) (Ok [tag_decl_tree w] r).
Proof.
  intros w r (_ & _ & Hne & _) Hb Hp. unfold tag_decl_tree.
  destruct (snd w) as [| cs rest]; [ exfalso; exact (Hne eq_refl) | ].
  flat_simp. rewrite <- ?app_assoc.
  pok ltac:(first
    [ exact (more_cases_parse _ _ _ _ Hb Hp)
    | exact (case_parse _ _ _ _ (fun _ => notparen_more _ _ _ _ Hp)) ]).
Qed.

Lemma print_decls_head : forall D r,
  NotBar r -> NotParen r ->
  NotBar (flats (print_decls D) ++ r) /\ NotParen (flats (print_decls D) ++ r).
Proof.
  intros D r Hb Hp. destruct D as [| w D]; [ exact (conj Hb Hp) | ].
  unfold print_decls. cbn [List.map]. rewrite flats_cons. unfold tag_decl_tree.
  flat_simp. split; simpl; discriminate.
Qed.

Lemma decls_parse : forall D r,
  Forall WfGroup D -> NotBar r -> NotParen r -> Plain r ->
  peg (E_star (E_rule R_tag_decl)) (flats (print_decls D) ++ r) (Ok (print_decls D) r).
Proof.
  induction D as [| w D IH]; intros r Hwf Hb Hp Hpl.
  - cbn [print_decls List.map flats flat_map app]. pok ltac:(first [ exact (plain_tag _ Hpl) ]).
  - inversion Hwf as [| ? ? Hw Hrest]; subst.
    destruct (print_decls_head D r Hb Hp) as [Hb' Hp'].
    unfold print_decls in *. cbn [List.map]. rewrite flats_cons, <- app_assoc.
    pok ltac:(first
      [ exact (IH _ Hrest Hb Hp Hpl)
      | exact (decl_parse _ _ Hw Hb' Hp') ]).
Qed.
