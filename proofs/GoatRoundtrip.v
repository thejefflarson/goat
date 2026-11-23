(* T3 (ADR 0030): the core, with the tags it builds and matches, parses back to
   itself.

   Scope: the core fragment, over a trusted token stream, printed in the curried
   style of checker/tests/core_roundtrip.rs. A program is the declarations of the
   tag groups [D] and then the expression [e]; the printer writes each group as
   [tag G = K0(...) | K1 | ...] with its tags named by position, a tag built from
   its payload as [K(a, b)] and a match as [match e do K(x, y) then ... done].
   The hypotheses:
   - [WfTable D]: each group is one the declaration can spell (its name bytes,
     its slot codes, parameters in the order written), and the names are
     distinct;
   - [tags_in D e]: every tag [e] builds or matches is a group of [D];
   - [scoped [] 0 e]: [e] is closed (no free variable, every bound index has a
     binder), a tag it builds has a payload of slots labelled by position, and
     each arm of a match binds the slots of its payload and does not use the
     payload otherwise;
   - [Interned e]: its labels are numbered as parsing numbers them, by first
     occurrence in the printed text;
   - [StartsApart D e]: after declarations the expression does not open with a
     parenthesis, which a case with no slots would read as its slots;
   - [names_distinct var_of]: the names the printer gives binders stand for
     distinct variables.
   The side conditions of ADR 0030 (recursive function bindings, groups of
   functions, duplicate labels, repeated parameters) are conditions on how the
   Rust front end reads the text. They are not needed here: the printer names
   each binder by its depth, so no name repeats, and the model reads a binding
   as the non-recursive [let] of the Ott source.

   The result: the printed text parses, the tree denotes [e] over the table its
   declarations build, and the groups the declarations declare are [D]. *)

From Stdlib Require Import String List.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatParse.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintLabels.
Require Import Goat.GoatPrintParse.
Require Import Goat.GoatPrintInst.
Require Import Goat.GoatPrintDen.
Require Import Goat.GoatPrintTop.
Require Import Goat.GoatPrintRecover.
Require Import Goat.GoatPrintLookup.
Open Scope string_scope.
Open Scope list_scope.

(* The group a declaration declares. *)
Definition group_of (d : tree) : list gdecl :=
  match decl_entries d with
  | (_, (w, _)) :: _ => [w]
  | [] => []
  end.

Definition declared_groups (t : tree) : list gdecl :=
  match t with
  | Node R_goat cs => List.flat_map group_of cs
  | _ => []
  end.

Lemma group_of_print : forall w, WfGroup w -> group_of (tag_decl_tree w) = [w].
Proof.
  intros w Hw. unfold group_of. rewrite (decl_entries_print w Hw).
  destruct Hw as (_ & _ & Hne & _). destruct (snd w) as [| cs rest]; [ exfalso; exact (Hne eq_refl) | ].
  reflexivity.
Qed.

Lemma declared_print : forall D e,
  Forall WfGroup D -> declared_groups (print_tree D e) = D.
Proof.
  intros D e Hwf. unfold declared_groups, print_tree, print_decls.
  rewrite List.flat_map_app. cbn [List.flat_map group_of decl_entries app]. rewrite List.app_nil_r.
  induction Hwf as [| w D Hw Hrest IH]; [ reflexivity | ].
  cbn [List.map List.flat_map]. rewrite (group_of_print w Hw). cbn [app]. f_equal. exact IH.
Qed.

Lemma clean_tab : forall D,
  Forall WfGroup D -> @CleanTags (mk_tags (tab D)).
Proof.
  intros D Hwf. rewrite (tab_eq D Hwf) in *.
  assert (Hkeys : forall k v, List.In (k, v) (List.flat_map entries_of D) ->
                    exists w tg, k = cn w tg).
  { intros k v Hin. apply List.in_flat_map in Hin. destruct Hin as (w & _ & Hin).
    unfold entries_of in Hin. apply List.in_map_iff in Hin. destruct Hin as (tg & Hv & _).
    injection Hv as <- _. exists w, tg. reflexivity. }
  constructor.
  - intros d. cbn [tags mk_tags]. apply tag_lookup_none. intros k v Hin Heq.
    destruct (Hkeys k v Hin) as (w & tg & ->). unfold cn, nm in Heq. cbn in Heq.
    injection Heq as H1 _. discriminate H1.
  - intros d i. cbn [tags mk_tags]. apply tag_lookup_none. intros k v Hin Heq.
    destruct (Hkeys k v Hin) as (w & tg & ->). unfold cn, gm in Heq. cbn in Heq.
    injection Heq as H1 _. discriminate H1.
Qed.

(* T3 *)
Theorem print_parse_roundtrip : forall var_of D e,
  names_distinct var_of ->
  WfTable D ->
  tags_in D e ->
  StartsApart D e ->
  scoped [] 0 e ->
  Interned e ->
  exists t,
    peg (E_rule R_goat) (print D e) (Ok [t] []) /\
    Den_goat var_of [] t e /\
    declared_groups t = D.
Proof.
  intros var_of D e Hdistinct Hwft Htags Hstart Hscoped Hinterned.
  destruct Hwft as [Hwf Hnd]. assert (Hwft : WfTable D) by exact (conj Hwf Hnd).
  set (t := print_tree D e).
  assert (Hparse : peg (E_rule R_goat) (print D e) (Ok [t] []))
    by exact (goat_parses D e Hwf Hstart Hscoped).
  assert (Htable : labels t = nub_from [] (List.map lname (lbls [] 0 e)))
    by exact (labels_print D e).
  assert (Hlabels : LabelsOK (labels t) (lbls [] 0 e))
    by (rewrite Htable; exact Hinterned).
  pose proof (clean_tab D Hwf) as CL.
  assert (HT : @TableOf (mk_tags (tab D)) D)
    by (intros w tg Hin Htg; exact (lookup_cn D w tg Hwft Hin Htg)).
  assert (Hexpr0 : @Den (mk_tags (tab D)) var_of (labels t)
                     (Node R_expr (block [] 0 e)) (inst var_of [] 0 e))
    by exact (proj1 (proj1 (@print_den (mk_tags (tab D)) CL var_of (labels t) Hdistinct D HT)
                       e [] 0 (fun L m H => ltac:(discriminate H)) Hscoped Htags Hlabels)).
  assert (Hinst : inst var_of [] 0 e = e)
    by exact (proj1 (inst_closed var_of) e [] 0 Hscoped).
  assert (Hexpr : @Den (mk_tags (tab D)) var_of (labels t) (Node R_expr (block [] 0 e)) e)
    by (rewrite <- Hinst at 2; exact Hexpr0).
  assert (Hden : Den_goat var_of [] t e).
  { exists (print_decls D), [Node R_expr (block [] 0 e)].
    split; [ reflexivity | split ].
    - unfold print_decls. apply Forall_forall. intros d Hd. apply List.in_map_iff in Hd.
      destruct Hd as (w & <- & _). exists (match tag_decl_tree w with Node _ c => c | _ => [] end).
      reflexivity.
    - change (@Den_body (mk_tags (tab D)) var_of (labels t) [Node R_expr (block [] 0 e)] e).
      apply DBo_some. exact Hexpr. }
  exists t. split; [ exact Hparse | split; [ exact Hden | exact (declared_print D e Hwf) ] ].
Qed.
