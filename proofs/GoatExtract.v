(* Extract the proven inference algorithm to OCaml (ADR 0037, decision 6).
   The extracted [goat_infer.ml] is what the differential test runs against
   the Rust checker; see [differential/README.md].  [make differential] runs
   this file in its own directory, which is where the output lands.

   The warnings silenced here are about Metalib: its atom supply is proved in
   opaque lemmas whose bodies extraction must read, and the extractor reserves
   a double underscore that the generated syntax uses. *)

Require Import Goat.GoatInfer.
Require Import Stdlib.extraction.ExtrOcamlNatInt.

Set Warnings "-extraction-opaque-accessed,-extraction-default-directory,-extraction-reserved-identifier".
Extraction Language OCaml.
Extraction "goat_infer.ml" infer_closed.
