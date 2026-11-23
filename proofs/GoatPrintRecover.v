(* Reading a printed declaration back: the table the parser builds from the
   declaration of a group has the group's tags, in order, each by its name, and
   the group itself, recovered from the name and the slots written. *)

From Stdlib Require Import String Ascii List Arith Lia Bool.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatDefs.
Require Import Goat.GoatGrammar.
Require Import Goat.GoatPeg.
Require Import Goat.GoatDen.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintArm.
Open Scope string_scope.
Open Scope list_scope.

Lemma is_type_node_slot : forall w c, is_type_node (slot_tree w c) = true.
Proof. intros w c. unfold slot_tree. destruct (slot_name w c); reflexivity. Qed.

Lemma filter_slot_trees : forall w cs,
  List.filter is_type_node (slot_trees w cs) = List.map (slot_tree w) cs.
Proof.
  intros w. induction cs as [| c cs IH]; [ reflexivity | ].
  destruct cs as [| c2 cs].
  - cbn [slot_trees List.filter List.map]. rewrite is_type_node_slot. reflexivity.
  - rewrite slot_trees_cons2. cbn [List.filter List.map]. rewrite is_type_node_slot.
    cbn [List.filter is_type_node sym]. rewrite IH. reflexivity.
Qed.

Lemma filter_case_kids : forall w tg cs,
  List.filter is_type_node (case_kids w tg cs) = List.map (slot_tree w) cs.
Proof.
  intros w tg cs. unfold case_kids. destruct cs as [| c cs]; [ reflexivity | ].
  cbn [List.filter]. cbn [is_type_node ident sym]. rewrite List.filter_app.
  rewrite filter_slot_trees. cbn [List.filter is_type_node sym]. rewrite List.app_nil_r.
  reflexivity.
Qed.

Lemma slot_of_name : forall w c n,
  WfGroup w -> slot_name w c = Some n -> slot_of (Some (gname w)) n = c.
Proof.
  intros w c n (_ & Hres & _) H.
  assert (Hr : forall x, List.In x ["Int"; "Number"; "Bool"; "Unit"; "String"] ->
                         String.eqb (gname w) x = false).
  { intros x Hx. destruct (String.eqb (gname w) x) eqn:E; [ | reflexivity ]. exfalso.
    unfold reserved_name in Hres.
    assert (Hex : existsb (String.eqb (gname w)) ["Int"; "Number"; "Bool"; "Unit"; "String"] = true)
      by (apply existsb_exists; exists x; split; [ exact Hx | exact E ]).
    congruence. }
  unfold slot_name in H. unfold slot_of.
  destruct c as [| [| [| [| [| [| c]]]]]]; try discriminate H;
    injection H as <-.
  - rewrite String.eqb_refl. reflexivity.
  - rewrite (Hr "Int" (or_introl eq_refl)). reflexivity.
  - rewrite (Hr "Number" (or_intror (or_introl eq_refl))). reflexivity.
  - rewrite (Hr "Bool" (or_intror (or_intror (or_introl eq_refl)))). reflexivity.
  - rewrite (Hr "Unit" (or_intror (or_intror (or_intror (or_introl eq_refl))))). reflexivity.
  - rewrite (Hr "String" (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))).
    reflexivity.
Qed.

Lemma app_seq : forall (A B : list nat) s n,
  A ++ B = List.seq s n ->
  A = List.seq s (length A) /\ B = List.seq (s + length A) (length B).
Proof.
  induction A as [| a A IH]; intros B s n H.
  - cbn [app] in H. subst B. rewrite List.length_seq. cbn [length]. rewrite Nat.add_0_r.
    split; reflexivity.
  - destruct n as [| n]; [ discriminate H | ].
    cbn [List.seq app] in H. injection H as Ha Hr. subst a.
    destruct (IH B (S s) n Hr) as [H1 H2].
    cbn [length List.seq]. split.
    + rewrite <- H1. reflexivity.
    + replace (s + S (length A)) with (S s + length A) by lia. exact H2.
Qed.

Lemma type_slots_map : forall w cs j,
  WfGroup w ->
  List.filter (Nat.leb 6) cs = List.seq (6 + j) (length (List.filter (Nat.leb 6) cs)) ->
  type_slots (Some (gname w)) j (List.map (slot_tree w) cs)
  = (cs, j + length (List.filter (Nat.leb 6) cs)).
Proof.
  intros w cs. induction cs as [| c cs IH]; intros j Hw Hp.
  - cbn [List.map type_slots List.filter length]. rewrite Nat.add_0_r. reflexivity.
  - cbn [List.map type_slots]. unfold slot_tree at 1.
    destruct (slot_name w c) as [n | ] eqn:E.
    + assert (Hlt : c < 6).
      { unfold slot_name in E. destruct c as [| [| [| [| [| [| c]]]]]]; try discriminate E; lia. }
      assert (Hleb : Nat.leb 6 c = false) by (apply Nat.leb_gt; exact Hlt).
      cbn [List.filter] in Hp |- *. rewrite Hleb in Hp |- *.
      unfold type_slot. rewrite (slot_of_name w c n Hw E).
      rewrite (IH j Hw Hp). reflexivity.
    + assert (Hge : 6 <= c).
      { unfold slot_name in E. destruct c as [| [| [| [| [| [| c]]]]]]; try discriminate E; lia. }
      assert (Hleb : Nat.leb 6 c = true) by (apply Nat.leb_le; exact Hge).
      cbn [List.filter] in Hp |- *. rewrite Hleb in Hp |- *.
      cbn [length] in Hp |- *. cbn [List.seq] in Hp.
      injection Hp as Hc Hrest. subst c.
      unfold type_slot.
      replace (6 + S j) with (6 + S j) in Hrest by reflexivity.
      assert (Hrest' : List.filter (Nat.leb 6) cs
                       = List.seq (6 + S j) (length (List.filter (Nat.leb 6) cs)))
        by (replace (6 + S j) with (S (6 + j)) by lia; exact Hrest).
      rewrite (IH (S j) Hw Hrest'). cbn [length]. f_equal. lia.
Qed.

Fixpoint case_kids_list (w : gdecl) (tg : nat) (css : list (list nat)) {struct css}
  : list (list tree) :=
  match css with
  | [] => []
  | cs :: rest => case_kids w tg cs :: case_kids_list w (S tg) rest
  end.

Lemma decl_cases_more : forall w css tg,
  decl_cases (more_case_trees w tg css) = case_kids_list w tg css.
Proof.
  intros w. induction css as [| cs css IH]; intros tg; [ reflexivity | ].
  cbn [more_case_trees decl_cases case_kids_list]. unfold case_tree. rewrite IH. reflexivity.
Qed.

Lemma cases_slots_recover : forall css w tg j,
  WfGroup w ->
  params_of css = List.seq (6 + j) (length (params_of css)) ->
  cases_slots (Some (gname w)) j (case_kids_list w tg css)
  = List.map (fun p : nat * list nat => (cn w (fst p), snd p)) (List.combine (List.seq tg (length css)) css).
Proof.
  induction css as [| cs css IH]; intros w tg j Hw Hp; [ reflexivity | ].
  cbn [case_kids_list cases_slots length List.seq List.combine List.map].
  unfold params_of in Hp. cbn [List.concat] in Hp. rewrite List.filter_app in Hp.
  destruct (app_seq _ _ _ _ Hp) as [Hp1 Hp2].
  rewrite filter_case_kids.
  rewrite (type_slots_map w cs j Hw Hp1).
  cbn [fst snd]. unfold case_name, case_kids, ident.
  assert (Hrest : params_of css = List.seq (6 + (j + length (List.filter (Nat.leb 6) cs)))
                                    (length (params_of css))).
  { unfold params_of. replace (6 + (j + length (List.filter (Nat.leb 6) cs)))
      with (6 + j + length (List.filter (Nat.leb 6) cs)) by lia. exact Hp2. }
  rewrite (IH w (S tg) _ Hw Hrest). reflexivity.
Qed.

Lemma entries_combine : forall (w : gdecl) css s,
  List.map (fun ic : nat * (string * list nat) => (fst (snd ic), (w, fst ic)))
    (List.combine (List.seq s (length css))
       (List.map (fun p : nat * list nat => (cn w (fst p), snd p)) (List.combine (List.seq s (length css)) css)))
  = List.map (fun tg => (cn w tg, (w, tg))) (List.seq s (length css)).
Proof.
  intros w. induction css as [| cs css IH]; intros s; [ reflexivity | ].
  cbn [length List.seq List.combine List.map fst snd]. rewrite (IH (S s)). reflexivity.
Qed.

Lemma map_snd_cases : forall (w : gdecl) css s,
  List.map snd (List.map (fun p : nat * list nat => (cn w (fst p), snd p))
                  (List.combine (List.seq s (length css)) css)) = css.
Proof.
  intros w. induction css as [| cs css IH]; intros s; [ reflexivity | ].
  cbn [length List.seq List.combine List.map snd]. rewrite (IH (S s)). reflexivity.
Qed.

Lemma bytes_name : forall (bs : list nat),
  Forall (fun b => b < 256) bs ->
  List.map nat_of_ascii (list_ascii_of_string (string_of_list_ascii (List.map ascii_of_nat bs)))
  = bs.
Proof.
  intros bs H. rewrite list_ascii_of_string_of_list_ascii, List.map_map.
  induction H as [| b bs Hb H IH]; [ reflexivity | ].
  cbn [List.map]. rewrite (nat_ascii_embedding b Hb). f_equal. exact IH.
Qed.


Lemma length_cases : forall (w : gdecl) css s,
  List.length (List.map (fun p : nat * list nat => (cn w (fst p), snd p))
                 (List.combine (List.seq s (length css)) css)) = length css.
Proof.
  intros w css s. rewrite List.length_map, List.length_combine, List.length_seq.
  apply Nat.min_id.
Qed.

(* The table a printed declaration builds: the group's tags, each named by
   position, and the group as written. *)
Lemma decl_entries_print : forall w,
  WfGroup w ->
  decl_entries (tag_decl_tree w)
  = List.map (fun tg => (cn w tg, (w, tg))) (List.seq 0 (length (snd w))).
Proof.
  intros w Hw. destruct Hw as (Hbytes & Hres & Hne & Hparams) eqn:EW.
  destruct w as [name css]. cbn [fst snd] in *.
  destruct css as [| cs rest]; [ exfalso; exact (Hne eq_refl) | ].
  set (w := (name, cs :: rest)) in *.
  set (kids := [Node R_tag_kw [sym "tag"]; Node R_group_name [ident (gname w)]; sym "="]
               ++ case_tree w 0 cs :: more_case_trees w 1 rest).
  assert (Hgrp : decl_group kids = Some (gname w)) by reflexivity.
  assert (Hcases : decl_cases kids = case_kids_list w 0 (cs :: rest)).
  { unfold kids. cbn [app decl_cases]. unfold case_tree. cbn [case_kids_list].
    rewrite decl_cases_more. reflexivity. }
  assert (Hp0 : params_of (cs :: rest) = List.seq (6 + 0) (length (params_of (cs :: rest)))).
  { cbn [snd] in Hparams. exact Hparams. }
  assert (Hrec : cases_slots (Some (gname w)) 0 (case_kids_list w 0 (cs :: rest))
                 = List.map (fun p : nat * list nat => (cn w (fst p), snd p))
                     (List.combine (List.seq 0 (length (cs :: rest))) (cs :: rest))).
  { apply cases_slots_recover; [ | exact Hp0 ].
    unfold WfGroup. cbn [fst snd]. exact (conj Hbytes (conj Hres (conj Hne Hparams))). }
  assert (Ek : tag_decl_tree w = Node R_tag_decl kids) by reflexivity. rewrite Ek.
  unfold decl_entries. rewrite Hgrp, Hcases, Hrec.
  rewrite (length_cases w (cs :: rest) 0).
  assert (Hmap : List.map snd (List.map (fun p : nat * list nat => (cn w (fst p), snd p))
                                (List.combine (List.seq 0 (length (cs :: rest))) (cs :: rest)))
                 = cs :: rest) by exact (map_snd_cases w (cs :: rest) 0).
  assert (Hname : decl_name kids
                    (List.map (fun p : nat * list nat => (cn w (fst p), snd p))
                       (List.combine (List.seq 0 (length (cs :: rest))) (cs :: rest)))
                  = name).
  { unfold decl_name. rewrite Hgrp. unfold gname. cbn [fst]. exact (bytes_name name Hbytes). }
  cbv zeta. rewrite Hmap, Hname.
  exact (entries_combine w (cs :: rest) 0).
Qed.
