(* Completeness of algorithm W, stage 7.6j: the occurs checks of [bind_prop]
   and [bind_row] by size (docs/design/phase7-proof-plan.md).

   [bind_prop] and [bind_row] refuse a variable that occurs in the type or row
   it is bound to.  A substitution [Sg] that unifies the two makes the variable
   as large as the image of the type, and a variable that occurs under a present
   entry makes the type strictly larger, so the check never refuses a unifiable
   pair, except through an entry [Sg] makes absent: an absent entry has size 0,
   so the variable behind it adds nothing (the pairs of stage 7.6f).  The
   hypothesis that replaces "the variable does not occur" is the ratified one:
   an occurrence is under a present entry ([po], [pos]).  The sizes are
   [tsz]/[rsz], which [teq] and [req] preserve and [nfT]/[nfR] leave alone, so the
   argument reads at [teqD]/[reqD] as well.

   Axiom- and admit-free. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatConv.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatCompleteRows.
Require Import Goat.GoatCompleteSorts.
Require Import Goat.GoatCompleteBind.
Require Import Goat.GoatCompleteBindRow.
Require Import Stdlib.micromega.Lia.

(* ---- sizes ignore the normal form ---- *)

Lemma nf_sz : forall D,
  (forall T, tsz (nfT D T) = tsz T) /\ (forall R, rsz (nfR D R) = rsz R).
Proof.
  intros D. apply typ_row_mutind; try (intros; reflexivity).
  - intros A IHA B IHB. cbn [nfT tsz]. rewrite IHA, IHB. reflexivity.
  - intros R IH. cbn [nfT tsz]. rewrite IH. reflexivity.
  - intros l T IHT R IHR. rewrite nfR_ext. cbn [rsz]. rewrite IHT, IHR. reflexivity.
  - intros l P IHP T IHT R IHR. rewrite nfR_maybe.
    destruct (is_abs P && rlacksD D l (nfR D R)) eqn:E.
    + cbv iota. apply andb_prop in E as [Ea _]. cbn [rsz]. rewrite Ea. exact IHR.
    + cbv iota. cbn [rsz]. rewrite nfT_is_abs, IHT, IHR. reflexivity.
Qed.

Lemma teqD_tsz : forall D T T', teqD D T T' -> tsz T = tsz T'.
Proof.
  intros D T T' H. pose proof (teq_tsz _ _ H) as E.
  rewrite (proj1 (nf_sz D)), (proj1 (nf_sz D)) in E. exact E.
Qed.

Lemma reqD_rsz : forall D R R', reqD D R R' -> rsz R = rsz R'.
Proof.
  intros D R R' H. pose proof (req_rsz _ _ H) as E.
  rewrite (proj2 (nf_sz D)), (proj2 (nf_sz D)) in E. exact E.
Qed.

(* ---- occurrence through present entries ---- *)

(* [po S vt vr T]: a type variable satisfying [vt], or a row variable
   satisfying [vr], occurs in [T] with every entry above it present under [S]
   (its presence image is not [Bool]).  A presence position does not count: the
   sizes do not read one. *)
Fixpoint po (S : sub) (vt vr : atom -> Prop) (T : typ) {struct T} : Prop :=
  match T with
  | typ_Var b => vt b
  | typ_Arrow A B => po S vt vr A \/ po S vt vr B
  | typ_Record R => por S vt vr R
  | typ_Grp _ A => po S vt vr A
  | _ => False
  end
with por (S : sub) (vt vr : atom -> Prop) (R : row) {struct R} : Prop :=
  match R with
  | row_Var q => vr q
  | row_Ext _ T R' => po S vt vr T \/ por S vt vr R'
  | row_Maybe _ P T R' => (is_abs (apT S P) = false /\ po S vt vr T) \/ por S vt vr R'
  | row_Empty => False
  end.

(* The same, through at least one present entry. *)
Fixpoint pos (S : sub) (vt vr : atom -> Prop) (R : row) {struct R} : Prop :=
  match R with
  | row_Ext _ T R' => po S vt vr T \/ por S vt vr R'
  | row_Maybe _ P T R' =>
      (is_abs (apT S P) = false /\ (po S vt vr T \/ por S vt vr R')) \/ pos S vt vr R'
  | _ => False
  end.

Lemma po_size : forall S vt vr m,
  (forall b, vt b -> m <= tsz (sT S b)) -> (forall q, vr q -> m <= rsz (sR S q)) ->
  (forall T, po S vt vr T -> m <= tsz (apT S T)) /\
  (forall R, por S vt vr R -> m <= rsz (apR S R)).
Proof.
  intros S vt vr m Hb Hq. unfold apT, apR. apply typ_row_mutind; simpl;
    try (intros; contradiction).
  - intros A IHA B IHB [H|H]; [ pose proof (IHA H) | pose proof (IHB H) ]; lia.
  - intros R IH H. pose proof (IH H). lia.
  - intros a H. exact (Hb a H).
  - intros w B IH H. pose proof (IH H). lia.
  - intros r H. exact (Hq r H).
  - intros l T IHT R IHR [H|H]; [ pose proof (IHT H) | pose proof (IHR H) ]; lia.
  - intros l P IHP T IHT R IHR H.
    change (ap_typ (sT S) (sR S) P) with (apT S P).
    destruct (is_abs (apT S P)) eqn:Ea.
    + destruct H as [[H _]|H]; [ discriminate H | exact (IHR H) ].
    + destruct H as [[_ H]|H]; [ pose proof (IHT H) | pose proof (IHR H) ]; lia.
Qed.

Lemma pos_size : forall S vt vr m,
  (forall b, vt b -> m <= tsz (sT S b)) -> (forall q, vr q -> m <= rsz (sR S q)) ->
  forall R, pos S vt vr R -> m < rsz (apR S R).
Proof.
  intros S vt vr m Hb Hq. destruct (po_size S vt vr m Hb Hq) as [Ht Hr].
  induction R as [ | r | l T R IH | l P T R IH ]; intros H; try (simpl in H; contradiction).
  - rewrite apR_Ext. cbn [rsz]. cbn [pos] in H.
    destruct H as [H|H]; [ pose proof (Ht _ H) | pose proof (Hr _ H) ]; lia.
  - cbn [pos] in H. rewrite apR_Maybe. cbn [rsz]. change (ap_typ (sT S) (sR S) P) with (apT S P).
    destruct (is_abs (apT S P)) eqn:Ea.
    + destruct H as [[H _]|H]; [ discriminate H | exact (IH H) ].
    + destruct H as [[_ [H|H]]|H]; [ pose proof (Ht _ H) | pose proof (Hr _ H) | pose proof (IH H) ]; lia.
Qed.

(* ---- the occurs checks ---- *)

(* A row variable bound to a row it occurs in under a present entry: no
   substitution unifies them, so the occurrence is not there. *)
Lemma bind_row_occ : forall Sg DT r R,
  reqD DT (sR Sg r) (apR Sg R) ->
  (r `in` frv_row R -> pos Sg (fun _ => False) (eq r) R) -> r `notin` frv_row R.
Proof.
  intros Sg DT r R Hreq Hocc Hin.
  pose proof (pos_size Sg (fun _ => False) (eq r) (rsz (sR Sg r))
                (fun b H => match H with end) (fun q Hq => ltac:(subst; apply le_n)) R (Hocc Hin)) as Hlt.
  pose proof (reqD_rsz _ _ _ Hreq) as E. lia.
Qed.

(* The same for a type variable and a type that is not a variable. *)
Lemma bind_prop_occ : forall Sg DT a T,
  (forall v, T <> typ_Var v) -> teqD DT (sT Sg a) (apT Sg T) ->
  (a `in` ftv_typ T -> po Sg (eq a) (fun _ => False) T) -> a `notin` ftv_typ T.
Proof.
  intros Sg DT a T Hv Heq Hocc Hin.
  destruct (po_size Sg (eq a) (fun _ => False) (tsz (sT Sg a))
              (fun b Hb => ltac:(subst; apply le_n)) (fun q H => match H with end)) as [Ht Hr].
  pose proof (Ht T (Hocc Hin)) as Hle. pose proof (teqD_tsz _ _ _ Heq) as E.
  pose proof (Hocc Hin) as Hp.
  destruct T as [ | | | | | A B | R | x | i | B1 | w A1 ]; try (exfalso; exact (Hv _ eq_refl));
    try (simpl in Hp; contradiction).
  - destruct Hp as [H|H]; [ pose proof (Ht A H) | pose proof (Ht B H) ];
      unfold apT in *; simpl in E; lia.
  - pose proof (Hr R Hp). unfold apT, apR in *. simpl in E. lia.
  - pose proof (Ht A1 Hp). unfold apT in *. simpl in E. lia.
Qed.

(* ---- [bind_row] and [bind_prop] under the ratified occurrence condition ---- *)

Theorem bind_row_pres_complete : forall (D DT : denv) Sg r R n,
  DOk D n -> KR D DT Sg -> old n r ->
  (forall x, x `in` ftv_row R -> old n x) -> (forall q, q `in` frv_row R -> old n q) ->
  prf R -> lcrb 0 R = true ->
  (forall x, x `in` ftv_row R -> cmpb (D x) (rk_sort (drk D r))) ->
  (forall q, q `in` frv_row R -> cmpb (rk_sort (drk D q)) (rk_sort (drk D r))) ->
  (r `in` frv_row R -> pos Sg (fun _ => False) (eq r) R) ->
  frld DT Sg (rk_sort (drk D r)) R -> reqD DT (sR Sg r) (apR Sg R) ->
  exists s D' n' S2, bind_row D r R n = Some (s, D', n') /\ KR D' DT S2 /\ n <= n' /\ DOk D' n' /\
    (forall x, old n x -> teq (sT Sg x) (apT S2 (sT s x))) /\
    (forall q, old n q -> reqD DT (sR Sg q) (apR S2 (sR s q))) /\ Cov Sg S2.
Proof.
  intros D DT Sg r R n Hd HK Hr Hot Hoq Hpf Hlc Hcb Hcq Hocc Hfld Hreq.
  exact (bind_row_sorted_complete true D DT Sg r R n Hd HK Hr Hot Hoq Hpf Hlc
           (bind_row_occ Sg DT r R Hreq Hocc) Hcb Hcq Hfld Hreq).
Qed.

Theorem bind_prop_pres_complete : forall (D D1 : denv) Sg a T n,
  DOk D n -> KR D D1 Sg -> old n a -> (forall v, T <> typ_Var v) ->
  (forall b, b `in` ftv_typ T -> old n b) -> (forall q, q `in` frv_typ T -> old n q) ->
  pf T -> lcb 0 T = true -> na T = true ->
  (forall b, b `in` ftv_typ T -> cmpb (D b) (D a)) ->
  (forall q, q `in` frv_typ T -> cmpb (rk_sort (drk D q)) (D a)) ->
  (a `in` ftv_typ T -> po Sg (eq a) (fun _ => False) T) ->
  fld D1 Sg (D a) T -> teqD D1 (sT Sg a) (apT Sg T) ->
  exists s D' n' S2, bind_prop D a T n = Some (s, D', n') /\ KR D' D1 S2 /\
    n <= n' /\ DOk D' n' /\
    (forall x, old n x -> teqD D1 (sT Sg x) (apT S2 (sT s x))) /\
    (forall r, old n r -> sR Sg r = apR S2 (sR s r)) /\ Img Sg S2 /\ Cov Sg S2.
Proof.
  intros D D1 Sg a T n Hd HK Ha Hv Hot Hoq Hpf Hlc Hna Hcb Hcq Hocc Hfld Heq.
  exact (bind_prop_sorted_complete true D D1 Sg a T n Hd HK Ha
           (bind_prop_occ Sg D1 a T Hv Heq Hocc) Hot Hoq Hcb Hcq Hpf Hlc Hna Hfld Heq).
Qed.
