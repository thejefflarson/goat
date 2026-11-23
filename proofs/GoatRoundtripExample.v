(* The hypotheses of T3 are satisfiable, and the labels one is not vacuous. *)

From Stdlib Require Import String List Lia.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatParse.
Require Import Goat.GoatPrint.
Require Import Goat.GoatRoundtrip.
Open Scope string_scope.
Open Scope list_scope.

(* x = 1; {lab0: x}.lab0 *)
Definition sample : exp :=
  e_let (e_num 1) (e_proj (e_rec (fs_cons 0 (e_fvar_b 0) fs_nil)) 0).

Example sample_scoped : scoped 0 sample.
Proof. simpl. repeat split; first [ lia | (right; exact I) ]. Qed.

Example sample_interned : Interned sample.
Proof.
  intros n Hn. simpl in Hn. destruct Hn as [<- | [<- | []]]; vm_compute; reflexivity.
Qed.

Example sample_roundtrip : forall var_of,
  names_distinct var_of ->
  exists t, peg (E_rule R_goat) (print sample) (Ok [t] []) /\ Den_goat var_of [] t sample.
Proof.
  intros var_of Hdistinct.
  exact (print_parse_roundtrip var_of sample Hdistinct sample_scoped sample_interned).
Qed.

(* A record whose first label is lab1 is numbered 0 when read back. *)
Example not_interned : ~ Interned (e_rec (fs_cons 1 e_true fs_nil)).
Proof.
  intros H. assert (Hin : List.In 1 (lbls (e_rec (fs_cons 1 e_true fs_nil)))) by (left; reflexivity).
  specialize (H 1 Hin). vm_compute in H. discriminate H.
Qed.

(* x = "s"; if 1 < 2 then x else "t" done + ... : a string, a conditional and
   operations, nested one inside another through parentheses. *)
Definition sample_operations : exp :=
  e_let (e_str [])
    (e_ite (e_bin (e_num 1) bop_lt (e_bin (e_num 2) bop_add (e_num 3)))
           (e_fvar_b 0)
           (e_str [])).

Example sample_operations_scoped : scoped 0 sample_operations.
Proof. simpl. repeat split; first [ lia | (right; exact I) ]. Qed.

Example sample_operations_interned : Interned sample_operations.
Proof. intros n Hn. simpl in Hn. destruct Hn. Qed.

Example sample_operations_roundtrip : forall var_of,
  names_distinct var_of ->
  exists t, peg (E_rule R_goat) (print sample_operations) (Ok [t] []) /\
            Den_goat var_of [] t sample_operations.
Proof.
  intros var_of Hdistinct.
  exact (print_parse_roundtrip var_of sample_operations Hdistinct
           sample_operations_scoped sample_operations_interned).
Qed.

(* x = 1.5; if true then x done: a Float literal, and a conditional whose
   missing else the parser reads as the unit value. *)
Definition sample_float_noelse : exp :=
  e_let (e_dec 5) (e_ite e_true (e_fvar_b 0) e_unit).

Example sample_float_noelse_scoped : scoped 0 sample_float_noelse.
Proof. simpl. repeat split; first [ exact I | lia | (left; reflexivity) ]. Qed.

Example sample_float_noelse_interned : Interned sample_float_noelse.
Proof. intros n Hn. simpl in Hn. destruct Hn. Qed.

Example sample_float_noelse_roundtrip : forall var_of,
  names_distinct var_of ->
  exists t, peg (E_rule R_goat) (print sample_float_noelse) (Ok [t] []) /\
            Den_goat var_of [] t sample_float_noelse.
Proof.
  intros var_of Hdistinct.
  exact (print_parse_roundtrip var_of sample_float_noelse Hdistinct
           sample_float_noelse_scoped sample_float_noelse_interned).
Qed.

(* The unit value has no literal in the grammar, so it is not printable on its
   own. *)
Example unit_is_not_printed : ~ scoped 0 e_unit.
Proof. intros H. exact H. Qed.

(* x = 1; {...(x), lab0: x}: a spread, printed with a parenthesised base. *)
Definition sample_spread : exp :=
  e_let (e_num 1) (e_spread (e_fvar_b 0) 0 (e_fvar_b 0)).

Example sample_spread_scoped : scoped 0 sample_spread.
Proof. simpl. repeat split; first [ exact I | lia ]. Qed.

Example sample_spread_interned : Interned sample_spread.
Proof.
  intros n Hn. simpl in Hn. destruct Hn as [<- | []]; vm_compute; reflexivity.
Qed.

Example sample_spread_roundtrip : forall var_of,
  names_distinct var_of ->
  exists t, peg (E_rule R_goat) (print sample_spread) (Ok [t] []) /\
            Den_goat var_of [] t sample_spread.
Proof.
  intros var_of Hdistinct.
  exact (print_parse_roundtrip var_of sample_spread Hdistinct
           sample_spread_scoped sample_spread_interned).
Qed.

(* A restrict is written only inside a rest pattern, which also binds the
   labels it removes, so the printer has no text for a bare restrict. *)
Example restrict_is_not_printed : ~ scoped 0 (e_restrict e_true 0).
Proof. intros H. exact H. Qed.
