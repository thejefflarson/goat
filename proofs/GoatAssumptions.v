(* `make check-assumptions` fails unless both theorems below print "Closed under
   the global context". *)

Require Import Goat.GoatPeg.
Require Import Goat.GoatParse.

Print Assumptions peg_deterministic.
Print Assumptions parse_denotes_lc.
