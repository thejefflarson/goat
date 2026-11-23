(* `make check-assumptions` fails unless the theorems below, except the last,
   print "Closed under the global context".  The last, `parse_text_denotes_xid`, is
   the lexer's T1 at the Unicode identifier tables, and rests on exactly two
   declared parameters, `xid_start_hi` and `xid_cont_hi`: whether a code point of
   128 or more may start, or continue, an identifier.  They are what
   `unicode_ident` says, which `make differential` checks by lexing the programs
   the repository holds with those tables and comparing every token with the Rust
   lexer's.  Every other theorem holds for any answer of the two predicates. *)

Require Import Goat.GoatPeg.
Require Import Goat.GoatParse.
Require Import Goat.GoatRoundtrip.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSound.
Require Import Goat.GoatInferSound.
Require Import Goat.GoatElab.
Require Import Goat.GoatInferElab.
Require Import Goat.GoatUnrollEqb.
Require Import Goat.GoatElabConverse.
Require Import Goat.GoatKnot.
Require Import Goat.GoatInferKnot.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatInferGuard.
Require Import Goat.GoatLexSpec.
Require Import Goat.GoatLexText.
Require Import Goat.GoatLexEdit.
Require Import Goat.GoatPegExec.

Print Assumptions peg_deterministic.
Print Assumptions parse_denotes_lc.
Print Assumptions print_parse_roundtrip.
Print Assumptions progress.
Print Assumptions preservation.
Print Assumptions soundness.
Print Assumptions infer_closed_sound.
Print Assumptions erase_step.
Print Assumptions erase_traps.
Print Assumptions coerce_typing.
Print Assumptions infer_elab_sound.
Print Assumptions unroll_eqb_sound.
Print Assumptions erase_converse.
Print Assumptions erase_converse_multistep.
Print Assumptions knot_unrolls.
Print Assumptions unify_k_sound.
Print Assumptions coerce_dec_sound.
Print Assumptions unify_co_sound.
Print Assumptions infer_guarded.
Print Assumptions cmp_total.
Print Assumptions cmp_unerase.
Print Assumptions lex_concat.
Print Assumptions step_longest.
Print Assumptions word_boundary.
Print Assumptions parse_text_denotes.
Print Assumptions edits_preserve_tokens.
Print Assumptions edits_preserve_parse.
Print Assumptions pf_sound.
Print Assumptions parse_fuel_denotes_lc.
Print Assumptions parse_text_denotes_xid.
