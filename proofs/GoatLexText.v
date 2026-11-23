(* T1 over text (phase 8, stage 1): source text, lexed to tokens, parsed by the
   PEG, denotes a locally closed term.  This retires the "the lexer is trusted"
   scope of ADR 0030: [lex] is the lexer's model, tied to [parser::lexer] by the
   differential test ([differential/README.md]), and the text reaches the PEG's
   token type [tok] only through [lex_toks].

   Whitespace and comments are trivia the parser never sees, and a code point no
   token class takes makes the text unparseable (the Rust [parse] reports it
   before it parses), so [lex_toks] is [None] for such a text.

   The Unicode identifier predicates are the only parameters of the model.  The
   theorems are stated for any predicates; [parse_text_denotes_xid] fixes them to
   [xid_start_hi] and [xid_cont_hi], and [GoatAssumptions.v] lists those two as
   what it rests on. *)

From Stdlib Require Import String Ascii List Arith Bool.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatShape.
Require Import Goat.GoatParse.
Require Import Goat.GoatMeta.
Require Import Goat.GoatLex.
Require Import Goat.GoatLexSpec.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

(* The decimal digits of [n], most significant first. *)
Fixpoint dec_digits (fuel n : nat) (acc : list ascii) : list ascii :=
  match fuel with
  | 0 => acc
  | S f =>
      let acc' := ascii_of_nat (48 + n mod 10) :: acc in
      if n / 10 =? 0 then acc' else dec_digits f (n / 10) acc'
  end.

(* ASCII other than a backslash stands for itself; any other code point is a
   backslash, its decimal value and a semicolon, so distinct sources name
   distinct strings. *)
Definition str_of (l : list nat) : string :=
  string_of_list_ascii
    (flat_map (fun c =>
       if (c <? 128) && negb (c =? 92) then [ascii_of_nat c]
       else "\"%char :: dec_digits (S c) c [] ++ [";"%char]) l).

Definition all_digits (l : list nat) : bool := forallb is_digit l.

Fixpoint digits_value (l : list nat) (acc : nat) : nat :=
  match l with
  | [] => acc
  | c :: l' => digits_value l' (acc * 10 + (c - 48))
  end.

(* The token the parser reads for a lexed token; trivia and unknown code points
   are not parser tokens. *)
Definition to_tok (t : token) : tok :=
  match kd t with
  | KName => TName (str_of (tx t))
  | KNumber => if all_digits (tx t) then TNum (digits_value (tx t) 0) else TDec 0
  | KString => TStr
  | _ => TSym (str_of (tx t))
  end.

Fixpoint to_toks (ts : list token) : option (list tok) :=
  match ts with
  | [] => Some []
  | t :: ts' =>
      match to_toks ts' with
      | None => None
      | Some r =>
          match kd t with
          | KUnknown => None
          | KWhitespace | KComment => Some r
          | _ => Some (to_tok t :: r)
          end
      end
  end.

Definition lex_toks (hs hc : nat -> bool) (s : list nat) : option (list tok) :=
  to_toks (lex hs hc s).

Definition nontrivia (ts : list token) : list token :=
  filter (fun t => negb (is_trivia t)) ts.

(* Trivia independence: the parser's tokens are a function of the tokens that are
   not whitespace or comments. *)
Lemma to_toks_nontrivia : forall ts, to_toks ts = to_toks (nontrivia ts).
Proof.
  induction ts as [|t ts IH]; [reflexivity|].
  unfold nontrivia in *. cbn [filter].
  destruct (is_trivia t) eqn:Et; cbn [negb].
  - rewrite <- IH. unfold is_trivia in Et.
    destruct (kd t) eqn:E; simpl in Et; try discriminate;
      cbn [to_toks]; rewrite E; destruct (to_toks ts); reflexivity.
  - cbn [to_toks]. rewrite <- IH. reflexivity.
Qed.

Theorem lex_toks_trivia_independent : forall hs hc s1 s2,
  nontrivia (lex hs hc s1) = nontrivia (lex hs hc s2) ->
  lex_toks hs hc s1 = lex_toks hs hc s2.
Proof.
  intros hs hc s1 s2 H. unfold lex_toks.
  rewrite to_toks_nontrivia, H, <- to_toks_nontrivia. reflexivity.
Qed.

(* The source parses to [ts] when the lexer's tokens do. *)
Definition parse_text (hs hc : nat -> bool) (s : list nat) (ts : list tree) : Prop :=
  exists ks rest, lex_toks hs hc s = Some ks /\ peg (E_rule R_goat) ks (Ok ts rest).

(* T1 over text. *)
Theorem parse_text_denotes : forall hs hc var_of ptbl s ts,
  parse_text hs hc s ts ->
  Forall core_tree ts ->
  Forall Complete ts ->
  Forall (goat_known ptbl) ts ->
  exists t, ts = [t]
    /\ (Reject t \/ exists e, Den_goat var_of ptbl t e /\ lc_exp e /\ lc e).
Proof.
  intros hs hc var_of ptbl s ts (ks & rest & _ & Hparse) Hcore Hcomplete Hknown.
  exact (parse_denotes_lc var_of ptbl ks ts rest Hparse Hcore Hcomplete Hknown).
Qed.

(* A program a text whitespace or comment edit leaves alone parses the same. *)
Corollary parse_text_trivia_independent : forall hs hc s1 s2 ts,
  nontrivia (lex hs hc s1) = nontrivia (lex hs hc s2) ->
  parse_text hs hc s1 ts -> parse_text hs hc s2 ts.
Proof.
  intros hs hc s1 s2 ts Hn (ks & rest & Hl & Hp).
  exists ks, rest. split; [|exact Hp].
  rewrite <- (lex_toks_trivia_independent hs hc s1 s2 Hn). exact Hl.
Qed.

Parameter xid_start_hi : nat -> bool.
Parameter xid_cont_hi : nat -> bool.

Theorem parse_text_denotes_xid : forall var_of ptbl s ts,
  parse_text xid_start_hi xid_cont_hi s ts ->
  Forall core_tree ts ->
  Forall Complete ts ->
  Forall (goat_known ptbl) ts ->
  exists t, ts = [t]
    /\ (Reject t \/ exists e, Den_goat var_of ptbl t e /\ lc_exp e /\ lc e).
Proof.
  intros var_of ptbl s ts.
  exact (parse_text_denotes xid_start_hi xid_cont_hi var_of ptbl s ts).
Qed.
