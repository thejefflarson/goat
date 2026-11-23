(* Function groups in a block, worked (phase 8: group placement). Functions
   that name each other later in the block are one group, placed together:
   hoisted when none of them uses an earlier value, and else after the last
   value one of them uses. *)

From Stdlib Require Import String List Lia.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatMeta.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatExample.
Require Import Goat.GoatBlockExample.
Open Scope string_scope.
Open Scope list_scope.

(* `f = program(y) do g(a) done`: a function whose body calls [g] on [a]. *)
Definition call_body (g a : string) : list tree :=
  [ident g; Node R_call [sym "("; Node R_arguments [Node R_expr [ident a]]; sym ")"]].

Definition fn_call_decl (f y g a : string) : tree :=
  Node R_declaration
    [ident f; sym "=";
     value_of (Node R_function
                 [Leaf (TSym "program"); sym "("; Node R_params [ident y]; sym ")"; sym "do";
                  Node R_expr (call_body g a); sym "done"])].

Definition fn_call_term (var_of : string -> termvar) (y g a : string) : exp :=
  curry [var_of y] (e_app (e_fvar_f (var_of g)) (e_fvar_f (var_of a))).

Lemma name_expr_den : forall var_of x,
  Den var_of [] (Node R_expr [ident x]) (e_fvar_f (var_of x)).
Proof.
  intros var_of x. apply D_expr_g. intros ctx fin. apply DK_chain. apply DM_chain.
  eapply DC_head; [ apply D_name; reflexivity | apply DP_nil ].
Qed.

Lemma fn_call_decl_den : forall var_of f y g a,
  Den_decl var_of [] (fn_call_decl f y g a) f (fn_call_term var_of y g a).
Proof.
  intros var_of f y g a. apply DD_plain. apply D_value. apply DM_chain.
  eapply DC_head; [ | apply DP_nil ].
  apply (D_function var_of [] (TSym "program") [ident y] [y] (call_body g a)
           (e_app (e_fvar_f (var_of g)) (e_fvar_f (var_of a))));
    [ apply DPa_one | ].
  apply D_expr_g. intros ctx fin. apply DK_chain. apply DM_chain.
  eapply DC_head; [ apply D_name; reflexivity | ].
  eapply DP_call with (es := [e_fvar_f (var_of a)]); [ | apply DP_nil ].
  apply DA_last. apply name_expr_den.
Qed.

Lemma fn_call_mentions_callee : forall var_of y g a,
  var_of g <> var_of y -> mentions (var_of g) (fn_call_term var_of y g a) = true.
Proof.
  intros var_of y g a Hne. unfold mentions, fn_call_term. apply AtomSetImpl.mem_1.
  unfold curry. simpl. unfold close_exp. simpl.
  destruct (var_of g == var_of y) as [E | _]; [ exfalso; exact (Hne E) | ].
  destruct (var_of a == var_of y); simpl; fsetdec.
Qed.

Lemma fn_call_mentions_arg : forall var_of y g a,
  var_of a <> var_of y -> mentions (var_of a) (fn_call_term var_of y g a) = true.
Proof.
  intros var_of y g a Hne. unfold mentions, fn_call_term. apply AtomSetImpl.mem_1.
  unfold curry. simpl. unfold close_exp. simpl.
  destruct (var_of a == var_of y) as [E | _]; [ exfalso; exact (Hne E) | ].
  destruct (var_of g == var_of y); simpl; fsetdec.
Qed.

Lemma ident_block_den : forall var_of ctx x fin,
  Den_blk var_of [] ctx fin [ident x] [] [] (e_fvar_f (var_of x)).
Proof.
  intros var_of ctx x fin. apply DK_chain. apply DM_chain.
  eapply DC_head; [ apply D_name; reflexivity | apply DP_nil ].
Qed.

Lemma two_members_den : forall var_of f g y z a b,
  Den_fdecls var_of [] [fn_call_decl f y g a; fn_call_decl g z f b] [f; g]
    [fn_call_term var_of y g a; fn_call_term var_of z f b].
Proof.
  intros var_of f g y z a b.
  apply DF_cons; [ apply fn_call_decl_den | reflexivity | ].
  apply DF_cons; [ apply fn_call_decl_den | reflexivity | apply DF_nil ].
Qed.

(* `f = program(y) do g(y) done  g = program(z) do f(z) done  f`: each function
   names the other, so the two are one group, hoisted because neither uses a
   value. *)
Example mutual_pair_is_one_group : forall var_of,
  var_of "g" <> var_of "y" -> var_of "f" <> var_of "z" ->
  Den_blk var_of [] [] e_unit
    [fn_call_decl "f" "y" "g" "y"; fn_call_decl "g" "z" "f" "z"; ident "f"]
    ["f"; "g"] [fn_call_term var_of "y" "g" "y"; fn_call_term var_of "z" "f" "z"]
    (e_fvar_f (var_of "f")).
Proof.
  intros var_of Hgy Hfz.
  apply (DK_group_hoist var_of [] [] e_unit
           [fn_call_decl "f" "y" "g" "y"; fn_call_decl "g" "z" "f" "z"] [ident "f"]
           ["f"; "g"] [fn_call_term var_of "y" "g" "y"; fn_call_term var_of "z" "f" "z"]
           [] [] (e_fvar_f (var_of "f"))).
  - apply two_members_den.
  - simpl. lia.
  - intros j Hj0 Hj. simpl in Hj. assert (j = 1) by lia. subst j.
    unfold cut_linked. simpl.
    rewrite (fn_call_mentions_callee var_of "y" "g" "y" Hgy). reflexivity.
  - reflexivity.
  - reflexivity.
  - apply ident_block_den.
Qed.

(* The same two functions after a value one of them uses: both are placed after
   it, as one group, so [g]'s mention of [f] is bound. *)
Example mutual_pair_after_a_value : forall var_of,
  var_of "x" <> var_of "y" -> var_of "g" <> var_of "y" -> var_of "f" <> var_of "z" ->
  Den_blk var_of [] [] e_unit
    [bind_tree "x" (num_tree 1);
     fn_call_decl "f" "y" "g" "x"; fn_call_decl "g" "z" "f" "z"; ident "f"]
    [] []
    (e_let (e_num (z_of_nat 1))
       (close_exp (var_of "x")
          (wrap_group [var_of "f"; var_of "g"]
             [fn_call_term var_of "y" "g" "x"; fn_call_term var_of "z" "f" "z"]
             (e_fvar_f (var_of "f"))))).
Proof.
  intros var_of Hxy Hgy Hfz.
  eapply DK_value; [ apply DD_plain; apply num_den | reflexivity | ].
  change [fn_call_decl "f" "y" "g" "x"; fn_call_decl "g" "z" "f" "z"; ident "f"]
    with ([fn_call_decl "f" "y" "g" "x"; fn_call_decl "g" "z" "f" "z"] ++ [ident "f"]).
  apply (DK_group_late var_of [] [var_of "x"] (e_fvar_f (var_of "x"))
           [fn_call_decl "f" "y" "g" "x"; fn_call_decl "g" "z" "f" "z"] [ident "f"]
           ["f"; "g"] [fn_call_term var_of "y" "g" "x"; fn_call_term var_of "z" "f" "z"]
           [] [] (e_fvar_f (var_of "f"))).
  - apply two_members_den.
  - simpl. lia.
  - intros j Hj0 Hj. simpl in Hj. assert (j = 1) by lia. subst j.
    unfold cut_linked. simpl.
    rewrite (fn_call_mentions_callee var_of "y" "g" "x" Hgy). reflexivity.
  - reflexivity.
  - unfold mentions_any. simpl.
    rewrite (fn_call_mentions_arg var_of "y" "g" "x" Hxy). reflexivity.
  - apply ident_block_den.
Qed.
