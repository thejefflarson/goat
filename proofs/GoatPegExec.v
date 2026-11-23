(* An executable parser for the generated grammar (phase 8, stage 8).  [pf] runs
   a PEG expression over a token stream with a fuel bound on the depth of the
   recursion, and [pf_sound] says that whatever it returns is what the relation
   [peg] (the specification, and the subject of T1 and T2) derives.  Running out
   of fuel answers [None]: soundness is a statement about answers, not about
   termination, so there is no completeness theorem and none is needed for T1.

   [parse_fuel] is extracted ([GoatPegExtract.v]) and compared with the Rust
   interpreter [parser::interp] on the repository's programs ([differential/]).
   The two read the same generated grammar, so the comparison ties the Rust
   interpreter's choice, repetition and end-of-input behaviour to the
   relation's. *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatShape.
Require Import Goat.GoatMeta.
Require Import Goat.GoatParse.

Fixpoint pf (fuel : nat) (e : pexpr) (s : list tok) : option result :=
  match fuel with
  | 0 => None
  | S f =>
      match e with
      | E_term t => Some (term_step t s)
      | E_rule r => option_map (wrap r) (pf f (body r) s)
      | E_seq a b =>
          match pf f a s with
          | None => None
          | Some Fail => Some Fail
          | Some (Ok ts s1) => option_map (prepend ts) (pf f b s1)
          end
      | E_alt a b =>
          match pf f a s with
          | None => None
          | Some Fail => pf f b s
          | Some ok => Some ok
          end
      | E_star a =>
          match pf f a s with
          | None => None
          | Some Fail => Some (Ok [] s)
          | Some (Ok ts s1) =>
              match pf f (E_star a) s1 with
              | Some (Ok ts' s2) => Some (Ok (ts ++ ts') s2)
              | _ => None
              end
          end
      | E_plus a => pf f (E_seq a (E_star a)) s
      | E_opt a =>
          match pf f a s with
          | None => None
          | Some Fail => Some (Ok [] s)
          | Some ok => Some ok
          end
      | E_expect a => pf f a s
      end
  end.

Theorem pf_sound : forall fuel e s r, pf fuel e s = Some r -> peg e s r.
Proof.
  induction fuel as [|f IH]; intros e s r H; [ discriminate | ].
  destruct e as [t | x | a b | a b | a | a | a | a]; cbn [pf] in H.
  - injection H as <-. apply P_term.
  - destruct (pf f (body x) s) as [res|] eqn:E; cbn in H; [ | discriminate ].
    injection H as <-. apply P_rule. exact (IH _ _ _ E).
  - destruct (pf f a s) as [[|ts s1]|] eqn:Ea; [ | | discriminate ].
    + injection H as <-. apply P_seq_fail. exact (IH _ _ _ Ea).
    + destruct (pf f b s1) as [res|] eqn:Eb; cbn in H; [ | discriminate ].
      injection H as <-. exact (P_seq _ _ _ _ _ _ (IH _ _ _ Ea) (IH _ _ _ Eb)).
  - destruct (pf f a s) as [[|ts s1]|] eqn:Ea; [ | | discriminate ].
    + exact (P_alt_right _ _ _ _ (IH _ _ _ Ea) (IH _ _ _ H)).
    + injection H as <-. exact (P_alt_left _ _ _ _ _ (IH _ _ _ Ea)).
  - destruct (pf f a s) as [[|ts s1]|] eqn:Ea; [ | | discriminate ].
    + injection H as <-. exact (P_star_stop _ _ (IH _ _ _ Ea)).
    + destruct (pf f (E_star a) s1) as [[|ts' s2]|] eqn:Eb; try discriminate.
      injection H as <-. exact (P_star_step _ _ _ _ _ _ (IH _ _ _ Ea) (IH _ _ _ Eb)).
  - apply P_plus. exact (IH _ _ _ H).
  - destruct (pf f a s) as [[|ts s1]|] eqn:Ea; [ | | discriminate ].
    + injection H as <-. exact (P_opt_none _ _ (IH _ _ _ Ea)).
    + injection H as <-. exact (P_opt_some _ _ _ _ (IH _ _ _ Ea)).
  - apply P_expect. exact (IH _ _ _ H).
Qed.

(* The parse of a token stream: the trees and what is left, when the fuel lasts. *)
Definition parse_fuel (fuel : nat) (s : list tok) : option result :=
  pf fuel (E_rule R_goat) s.

(* T1 for the executable parser: a stream [parse_fuel] accepts is the one the
   relation does, so its tree denotes a locally closed term or is one lowering
   rejects. *)
Corollary parse_fuel_denotes_lc : forall fuel var_of ptbl s ts s',
  parse_fuel fuel s = Some (Ok ts s') ->
  Forall core_tree ts ->
  Forall Complete ts ->
  Forall (goat_known ptbl) ts ->
  exists t, ts = [t]
    /\ (Reject t \/ exists e, Den_goat var_of ptbl t e /\ lc_exp e /\ lc e).
Proof.
  intros fuel var_of ptbl s ts s' H.
  exact (parse_denotes_lc var_of ptbl s ts s' (pf_sound _ _ _ _ H)).
Qed.
