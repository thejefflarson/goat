(* `make check-assumptions` fails unless all seven theorems below print "Closed
   under the global context". *)

Require Import Goat.GoatPeg.
Require Import Goat.GoatParse.
Require Import Goat.GoatRoundtrip.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSound.
Require Import Goat.GoatInferSound.

Print Assumptions peg_deterministic.
Print Assumptions parse_denotes_lc.
Print Assumptions print_parse_roundtrip.
Print Assumptions progress.
Print Assumptions preservation.
Print Assumptions soundness.
Print Assumptions infer_closed_sound.
