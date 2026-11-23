(* T3 through tags: a program that declares a tag group, builds a tag, and
   matches on it, meets the hypotheses and reads back. *)

From Stdlib Require Import String List Lia.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatParse.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintTop.
Require Import Goat.GoatPrintDecl.
Require Import Goat.GoatRoundtrip.
Open Scope string_scope.
Open Scope list_scope.

(* tag Shape = Circle(Number) | Rect(Number, Number) | Dot
   The tags are named by position: k_Shape, ki_Shape, kii_Shape. *)
Definition shape : gdecl := ([83; 104; 97; 112; 101], [[2]; [2; 2]; []]).

(* match Circle(1) do Circle(r) then r  Rect(w, h) then w + h  else 0 done *)
Definition area : exp :=
  e_match shape
    (e_con shape 0 (e_rec (fs_cons 0 (e_num 1) fs_nil)))
    (arms_cons 0 (e_let (e_proj (e_fvar_b 0) 0) (e_fvar_b 0))
       (arms_cons 1 (e_let (e_proj (e_fvar_b 0) 0)
                       (e_let (e_proj (e_fvar_b 1) 1)
                          (e_bin (e_fvar_b 1) bop_add (e_fvar_b 0))))
          (arms_else (e_num 0)))).

Example area_printed :
  print [shape] area =
    [TSym "tag"; TName "Shape"; TSym "="; TName "k_Shape"; TSym "("; TName "Number"; TSym ")";
     TSym "|"; TName "ki_Shape"; TSym "("; TName "Number"; TSym ","; TName "Number"; TSym ")";
     TSym "|"; TName "kii_Shape";
     TSym "match"; TName "k_Shape"; TSym "("; TNum 1; TSym ")"; TSym "do";
     TName "k_Shape"; TSym "("; TName "v1"; TSym ")"; TSym "then"; TName "v1";
     TName "ki_Shape"; TSym "("; TName "v1"; TSym ","; TName "v2"; TSym ")"; TSym "then";
     TName "v1"; TSym "+"; TName "v2";
     TSym "else"; TNum 0; TSym "done"].
Proof. reflexivity. Qed.

Example shape_wf : WfTable [shape].
Proof.
  split.
  - constructor; [ | constructor ].
    unfold WfGroup, shape. cbn [fst snd]. repeat split.
    + repeat (apply Forall_cons; [ lia | ]). apply Forall_nil.
    + intros H; discriminate H.
  - cbn. constructor; [ intros H; destruct H | constructor ].
Qed.

Example area_tags : tags_in [shape] area.
Proof. simpl. repeat split; left; reflexivity. Qed.

Example area_scoped : scoped [] 0 area.
Proof.
  simpl. repeat (first [ exact I | reflexivity | lia | split
    | (intros m Hm; discriminate Hm) | (intros Hx; discriminate Hx) ]).
Qed.

Example area_interned : Interned area.
Proof. intros n Hn. simpl in Hn. destruct Hn. Qed.

Example area_starts_apart : StartsApart [shape] area.
Proof.
  right. assert (E : exists r, flats (block [] 0 area) = TSym "match" :: r)
    by (eexists; reflexivity).
  destruct E as [r E]. unfold NotParen. rewrite E. intros H. discriminate H.
Qed.

Example area_roundtrip : forall var_of,
  names_distinct var_of ->
  exists t, peg (E_rule R_goat) (print [shape] area) (Ok [t] []) /\
            Den_goat var_of [] t area /\ declared_groups t = [shape].
Proof.
  intros var_of Hdistinct.
  exact (print_parse_roundtrip var_of [shape] area Hdistinct shape_wf area_tags
           area_starts_apart area_scoped area_interned).
Qed.

(* A bare tag is written with an empty call, and a case with no slots is
   declared bare: tag Both = Pair(_, _) | Left(_), and Pair(1, 2). *)
Definition both : gdecl := ([66; 111; 116; 104], [[6; 7]; [8]]).

Example both_printed :
  print [both] (e_con both 0 (e_rec (fs_cons 0 (e_num 1) (fs_cons 1 (e_num 2) fs_nil)))) =
    [TSym "tag"; TName "Both"; TSym "="; TName "k_Both"; TSym "("; TSym "_"; TSym ",";
     TSym "_"; TSym ")"; TSym "|"; TName "ki_Both"; TSym "("; TSym "_"; TSym ")";
     TName "k_Both"; TSym "("; TNum 1; TSym ","; TNum 2; TSym ")"].
Proof. reflexivity. Qed.

(* Two groups cannot share a name, and parameters count from 6 in order. *)
Example repeated_group_name_is_not_a_table :
  ~ WfTable [shape; shape].
Proof.
  intros [_ H]. inversion H as [| ? ? Hn _]; subst. apply Hn. left. reflexivity.
Qed.

Example parameters_out_of_order_are_not_a_group :
  ~ WfGroup ([65], [[7]]).
Proof. intros (_ & _ & _ & H). discriminate H. Qed.
