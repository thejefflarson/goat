(* The hypotheses of T3 are satisfiable, and the labels one is not vacuous. *)

From Coq Require Import String List Lia.
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
Proof. simpl. repeat split. lia. Qed.

Example sample_interned : Interned sample.
Proof.
  intros n Hn. simpl in Hn. destruct Hn as [<- | [<- | []]]; vm_compute; reflexivity.
Qed.

Example sample_roundtrip : forall var_of,
  names_distinct var_of ->
  exists t, peg (E_rule R_goat) (print sample) (Ok [t] []) /\ Den_goat var_of t sample.
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
