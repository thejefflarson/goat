(* `make check-assumptions` fails unless all eighteen theorems below print "Closed
   under the global context". *)

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
