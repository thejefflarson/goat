(* A whole-number literal [e_num 3] reads its argument as an integer without
   opening [Z_scope], so a file that never imports ZArith (and the generated
   printer table) can still write one.  Files that mention [e_num] import this
   module. *)

Require Import Goat.Goat_ott.
Require Export Goat.GoatNum.

Arguments e_num n%_znum_scope.
