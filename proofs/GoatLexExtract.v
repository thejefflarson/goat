(* Extract the lexer to OCaml (phase 8, stage 1).  [lex_driver.ml] runs the
   extracted [lex] on the programs the repository holds and compares its tokens
   with [parser::lexer::lex]; see [differential/README.md].  [make differential]
   runs this file in its own directory, which is where the output lands.

   [lex] takes the two Unicode predicates as arguments, and the driver passes
   the tables [lex_dump] writes from [unicode_ident]. *)

Require Import Goat.GoatLex.
Require Import Stdlib.extraction.ExtrOcamlBasic.
Require Import Stdlib.extraction.ExtrOcamlNatInt.

Set Warnings "-extraction-default-directory".
Extraction Language OCaml.
Extraction "goat_lex.ml" lex xs xc.
