(* Extract the executable parser to OCaml (phase 8, stage 8).  [parse_driver.ml]
   runs the extracted [parse_fuel] on the token streams of the programs the
   repository holds and compares its trees with [parser::interp]'s; see
   [differential/README.md].  [make differential] runs this file in its own
   directory, which is where the output lands. *)

Require Import Goat.GoatPegExec.
Require Import Goat.GoatGrammar.
Require Import Stdlib.extraction.ExtrOcamlBasic.
Require Import Stdlib.extraction.ExtrOcamlString.
Require Import Stdlib.extraction.ExtrOcamlNatInt.

Set Warnings "-extraction-default-directory -extraction-reserved-identifier".
Extraction Language OCaml.
Extraction "goat_parse.ml" parse_fuel rule_name.
