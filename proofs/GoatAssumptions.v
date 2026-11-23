(* `make check-assumptions` fails unless all twelve theorems below print "Closed
   under the global context". *)

Require Import Goat.GoatPeg.
Require Import Goat.GoatParse.
Require Import Goat.GoatRoundtrip.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSound.
Require Import Goat.GoatInferSound.
Require Import Goat.GoatInferMuFree.
Require Import Goat.GoatElab.
Require Import Goat.GoatInferElab.

Print Assumptions peg_deterministic.
Print Assumptions parse_denotes_lc.
Print Assumptions print_parse_roundtrip.
Print Assumptions progress.
Print Assumptions preservation.
Print Assumptions soundness.
Print Assumptions infer_closed_sound.
Print Assumptions infer_mu_free.
Print Assumptions erase_step.
Print Assumptions erase_traps.
Print Assumptions coerce_typing.
Print Assumptions infer_elab_sound.
