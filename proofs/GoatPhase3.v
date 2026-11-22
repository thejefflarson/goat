(* Phase 3 of ADR 0037: worked examples for tag groups, construction and
   `match` (docs/design/closed-tags-plan.md, docs/design/phase3-proof-plan.md).

   A group is declared by the slots of each of its tags (GoatDefs.v): code 0 is
   the group itself, 1 to 5 are Int, Float, Bool, Unit, String, and 6 + j is
   the group's implicit parameter j (a `_`).  So, in goat source:

     tag Shot  = Miss | Hit(Int)          shot   = [[]; [1]]
     tag Level = Low | Medium | High      level  = [[]; []; []]
     tag List  = Empty | Link(_, List)    list_g = [[]; [6; 0]]

   The accepted examples fail to compile if a rule is dropped.  The rejected
   ones fail if exhaustiveness, or the one type per parameter that makes a
   group generic without mixing, is dropped. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatLit.
Require Import Goat.GoatDefs.
Require Import Goat.GoatRows.
Require Import Goat.GoatTags.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lia.

Definition shot : gdecl := [ []; [1] ].
Definition level : gdecl := [ []; []; [] ].
Definition list_g : gdecl := [ []; [6; 0] ].

(* ---- construction ---- *)

(* Hit(3): the payload is the closed record of the tag's slots. *)
Definition hit3 : exp := e_con shot 1 (e_rec (fs_cons 0 (e_num 3) fs_nil)).

Example hit3_types : typing d_any nil hit3 (typ_Grp shot (spine [])).
Proof.
  unfold hit3. apply T_Con; [ simpl; lia | ].
  cbn. apply T_Record. eapply FT_cons;
    [ apply T_Num; [ solve_uniq | exact I ] | apply FT_nil; solve_uniq ].
Qed.

(* A tag with no payload carries Unit. *)
Example miss_types : typing d_any nil (e_con shot 0 e_unit) (typ_Grp shot (spine [])).
Proof. apply T_Con; [ simpl; lia | cbn; apply T_Unit; solve_uniq ]. Qed.

(* The group's parameter is fresh at each construction: Empty is a list of
   anything. *)
Example empty_is_every_list : forall T,
  typing d_any nil (e_con list_g 0 e_unit) (typ_Grp list_g (spine [T])).
Proof. intros T. apply T_Con; [ simpl; lia | cbn; apply T_Unit; solve_uniq ]. Qed.

(* Link(1, Link(2, Empty)), which is the list literal [1, 2]: one parameter
   fixes the element type of the whole value, and the group's own name in the
   second slot carries the same parameter down the spine. *)
Definition empty_l : exp := e_con list_g 0 e_unit.
Definition link (h t : exp) : exp :=
  e_con list_g 1 (e_rec (fs_cons 0 h (fs_cons 1 t fs_nil))).
Definition one_two : exp := link (e_num 1) (link (e_num 2) empty_l).

Lemma link_types : forall h t T,
  typing d_any nil h T -> typing d_any nil t (typ_Grp list_g (spine [T])) ->
  typing d_any nil (link h t) (typ_Grp list_g (spine [T])).
Proof.
  intros h t T Hh Ht. unfold link. apply T_Con; [ simpl; lia | ].
  cbn. apply T_Record. eapply FT_cons; [ exact Hh | ].
  eapply FT_cons; [ exact Ht | apply FT_nil; solve_uniq ].
Qed.

Example one_two_types : typing d_any nil one_two (typ_Grp list_g (spine [typ_Int])).
Proof.
  unfold one_two. apply link_types.
  - apply T_Num; [ solve_uniq | exact I ].
  - apply link_types; [ apply T_Num; [ solve_uniq | exact I ] | apply empty_is_every_list ].
Qed.

(* ---- match ---- *)

(* match s do Miss then 0 Hit(p) then p.0 done *)
Definition shot_arms : arms :=
  arms_cons 0 (e_num 0) (arms_cons 1 (e_proj (e_fvar_b 0) 0) arms_nil).

Definition read_shot (s : exp) : exp := e_match shot s shot_arms.

Example read_hit3_types : typing d_any nil (read_shot hit3) typ_Int.
Proof.
  unfold read_shot. eapply T_Match with (L := {}) (Ts := []).
  - exact hit3_types.
  - unfold arms_wf. cbn. repeat split.
    + constructor; [ intros [H|H]; [ discriminate | contradiction ] | constructor; [ intros [] | constructor ] ].
    + intros tg [H|[H|[]]]; subst; simpl; lia.
    + right. intros tg Hlt. simpl. destruct tg as [|[|tg]]; [ left | right; left | ]; auto; lia.
  - intros tg body Hf x Hx. unfold shot_arms in Hf. cbn in Hf.
    destruct tg as [|[|tg]]; cbn in Hf.
    + inversion Hf; subst. cbn. apply T_Num; [ solve_uniq | exact I ].
    + inversion Hf; subst. cbn [open_exp_wrt_exp open_exp_wrt_exp_rec tag_payload shot payload_ty slots_row slot_ty nth_error].
      eapply T_Proj. apply T_Var with (s := sch_mono (typ_Record (row_Ext 0 typ_Int row_Empty)));
        [ solve_uniq | apply binds_cons_2; reflexivity | apply inst_mono_self ].
    + discriminate.
  - intros e0 Hd. discriminate.
Qed.

(* It runs: the arm for Hit takes the payload record, and the projection reads
   the Int out of it. *)
Example read_hit3_runs : multistep (read_shot hit3) (e_num 3).
Proof.
  unfold read_shot, hit3, shot_arms.
  eapply ms_step; [ apply st_match_arm; [ repeat constructor | reflexivity ] | ].
  cbn [open_exp_wrt_exp open_exp_wrt_exp_rec open_fields_wrt_exp_rec].
  eapply ms_step; [ apply st_projrec; [ repeat constructor | reflexivity ] | ].
  apply ms_refl.
Qed.

(* An else covers the tags no arm names: Hit(p) then p.0 else 0. *)
Definition shot_else_arms : arms :=
  arms_cons 1 (e_proj (e_fvar_b 0) 0) (arms_else (e_num 0)).

Example else_arm_runs : multistep (e_match shot (e_con shot 0 e_unit) shot_else_arms) (e_num 0).
Proof.
  unfold shot_else_arms.
  eapply ms_step; [ apply st_match_else; [ repeat constructor | reflexivity | reflexivity ] | ].
  apply ms_refl.
Qed.

(* An else on an exhaustive match is accepted too (arms_wf asks for coverage
   only when there is no else). *)
Example else_after_full_cover_is_wf :
  arms_wf shot (arms_cons 0 (e_num 0) (arms_cons 1 (e_num 1) (arms_else (e_num 2)))).
Proof.
  unfold arms_wf. cbn. repeat split.
  - constructor; [ intros [H|[]]; discriminate | constructor; [ intros [] | constructor ] ].
  - intros tg [H|[H|[]]]; subst; simpl; lia.
  - left. discriminate.
Qed.

(* ---- what has no derivation ---- *)

(* A match without an else names every tag of its group: Hit alone does not. *)
Definition partial_arms : arms := arms_cons 1 (e_proj (e_fvar_b 0) 0) arms_nil.

Example partial_match_rejected : forall T,
  ~ typing d_any nil (e_match shot hit3 partial_arms) T.
Proof.
  intros T H. destruct (match_inv _ _ _ _ _ _ H) as [L [Ts [T0 [_ [Hwf _]]]]].
  destruct Hwf as [_ [_ [Hne | Hall]]].
  - apply Hne. reflexivity.
  - assert (Hin : In 0 (arms_idx partial_arms)) by (apply Hall; simpl; lia).
    destruct Hin as [Hin | []]. discriminate Hin.
Qed.

(* A tag twice is rejected as well. *)
Example repeated_arm_rejected : forall T,
  ~ typing d_any nil
      (e_match shot hit3 (arms_cons 0 (e_num 0) (arms_cons 0 (e_num 1) (arms_else (e_num 2))))) T.
Proof.
  intros T H. destruct (match_inv _ _ _ _ _ _ H) as [L [Ts [T0 [_ [Hwf _]]]]].
  destruct Hwf as [Hnd _]. cbn in Hnd. inversion Hnd; subst.
  apply H2. left. reflexivity.
Qed.

(* A tag outside the group does not construct. *)
Example tag_outside_group_rejected : forall T,
  ~ typing d_any nil (e_con shot 2 e_unit) T.
Proof.
  intros T H. destruct (con_inv _ _ _ _ _ _ H) as [Ts [Hlt _]]. simpl in Hlt. lia.
Qed.


(* A group is generic but does not mix: the parameter is one type throughout a
   value.  Link(true, Link("a", Empty)) has no derivation, because the tail
   would have to be a list of Bool and it is a list of String. *)

Lemma true_inv : forall D G T, typing D G e_true T -> teq typ_Bool T.
Proof.
  intros D G T H. remember e_true as e0 eqn:He.
  induction H; try discriminate He.
  - apply teq_refl.
  - eauto using teq_trans.
Qed.

Lemma str_inv : forall D G q T, typing D G (e_str q) T -> teq typ_String T.
Proof.
  intros D G q T H. remember (e_str q) as e0 eqn:He.
  induction H; try discriminate He.
  - eauto using teq_trans.
  - apply teq_refl.
Qed.

(* Link(h, t) at a type: the head has the type of the group's parameter, and
   the tail is a list of the same parameter. *)
Lemma link_inv : forall D G h t T, typing D G (link h t) T ->
  exists A B Ts, typing D G h A /\ typing D G t B /\
    teq A (nth 0 Ts typ_Unit) /\ teq B (typ_Grp list_g (spine Ts)) /\
    teq (typ_Grp list_g (spine Ts)) T.
Proof.
  intros D G h t T H. unfold link in H.
  destruct (con_inv _ _ _ _ _ _ H) as [Ts [_ [Hp Hg]]]. cbn in Hp.
  destruct (rec_inv _ _ _ _ Hp) as [R [Hft Hr]].
  apply teq_Record_inv in Hr. destruct Hr as [R2 [E Hreq]]. injection E as E. subst R2.
  inversion Hft; subst.
  match goal with Hf : field_typing _ _ (fs_cons 1 _ _) _ |- _ => inversion Hf; subst end.
  exists T0, T1, Ts. refine (conj _ (conj _ (conj _ (conj _ Hg)))); try assumption.
  - pose proof (proj2 (req_pres _ _ Hreq) 0) as H0. cbn in H0. inversion H0; subst. assumption.
  - pose proof (proj2 (req_pres _ _ Hreq) 1) as H1. cbn in H1. inversion H1; subst. assumption.
Qed.

Definition mixed : exp := link e_true (link (e_str [97]) empty_l).

Example mixed_list_rejected : forall T, ~ typing d_any nil mixed T.
Proof.
  intros T H. unfold mixed in H.
  destruct (link_inv _ _ _ _ _ H) as [A [B [Ts [Hh [Ht [HA [HB _]]]]]]].
  destruct (link_inv _ _ _ _ _ Ht) as [A' [B' [Ts' [Hh' [_ [HA' [_ Hg']]]]]]].
  pose proof (teq_trans _ _ _ Hg' HB) as Hsp.
  apply teq_Grp_inv in Hsp. destruct Hsp as [Z [E Hz]]. injection E as E. subst Z.
  pose proof (teq_nth _ _ (teq_spine_inv _ _ Hz) 0) as Hn.
  apply true_inv in Hh. apply str_inv in Hh'.
  assert (Hbs : teq typ_Bool typ_String).
  { eapply teq_trans; [ exact Hh | ]. eapply teq_trans; [ exact HA | ].
    eapply teq_trans; [ apply teq_sym; exact Hn | ].
    eapply teq_trans; [ apply teq_sym; exact HA' | ]. apply teq_sym. exact Hh'. }
  apply teq_Bool_inv in Hbs. discriminate Hbs.
Qed.
