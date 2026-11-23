(* Structural induction over terms that also reaches below the child a tag case
   or a match arm holds. A tag's payload is a record of its slots, and an arm's
   body lies past the bindings of its slots: each is a descendant of the term
   but not its child, so the hypothesis of the case covers every slot of a
   payload record and the term [arm_inner m b] left after any number of the
   bindings an arm's term opens with. *)

From Stdlib Require Import List.
Import ListNotations.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatPrint.
Open Scope list_scope.

Fixpoint fields_all (P : exp -> Prop) (fs : Goat_ott.fields) {struct fs} : Prop :=
  match fs with
  | fs_nil => True
  | fs_cons _ e rest => P e /\ fields_all P rest
  | fs_meth _ e rest => P e /\ fields_all P rest
  end.

Lemma inner_let : forall (P : exp -> Prop) v b,
  P (e_let v b) -> (forall m, P (arm_inner m b)) -> forall m, P (arm_inner m (e_let v b)).
Proof. intros P v b He IH m. destruct m as [| m]; [ exact He | exact (IH m) ]. Qed.

Section Induction.
  Variables (P : exp -> Prop) (Pf : Goat_ott.fields -> Prop) (Pa : arms -> Prop).

  Hypothesis H_bvar : forall i, P (e_fvar_b i).
  Hypothesis H_fvar : forall y, P (e_fvar_f y).
  Hypothesis H_num : forall n, P (e_num n).
  Hypothesis H_dec : forall d, P (e_dec d).
  Hypothesis H_true : P e_true.
  Hypothesis H_false : P e_false.
  Hypothesis H_abs : forall b, P b -> P (e_abs b).
  Hypothesis H_app : forall a, P a -> forall b, P b -> P (e_app a b).
  Hypothesis H_let : forall a, P a -> forall b, P b -> P (e_let a b).
  Hypothesis H_letrec : forall fs, Pf fs -> forall b, P b -> P (e_letrec fs b).
  Hypothesis H_rec : forall fs, Pf fs -> P (e_rec fs).
  Hypothesis H_proj : forall a, P a -> forall l, P (e_proj a l).
  Hypothesis H_unit : P e_unit.
  Hypothesis H_str : forall q, P (e_str q).
  Hypothesis H_ite : forall a, P a -> forall b, P b -> forall c, P c -> P (e_ite a b c).
  Hypothesis H_bin : forall a, P a -> forall o b, P b -> P (e_bin a o b).
  Hypothesis H_tofloat : forall a, P a -> P (e_tofloat a).
  Hypothesis H_con : forall w tg a, P a -> (forall fs, a = e_rec fs -> fields_all P fs) ->
    P (e_con w tg a).
  Hypothesis H_match : forall w a, P a -> forall ars, Pa ars -> P (e_match w a ars).
  Hypothesis H_spread : forall a, P a -> forall l b, P b -> P (e_spread a l b).
  Hypothesis H_restrict : forall a, P a -> forall l, P (e_restrict a l).
  Hypothesis H_fold : forall a, P a -> P (e_fold a).
  Hypothesis H_unfold : forall a, P a -> P (e_unfold a).
  Hypothesis H_fnil : Pf fs_nil.
  Hypothesis H_fcons : forall l e, P e -> forall fs, Pf fs -> Pf (fs_cons l e fs).
  Hypothesis H_fmeth : forall l e, P e -> forall fs, Pf fs -> Pf (fs_meth l e fs).
  Hypothesis H_anil : Pa arms_nil.
  Hypothesis H_aelse : forall e, P e -> Pa (arms_else e).
  Hypothesis H_acons : forall tg e, P e -> (forall m, P (arm_inner m e)) -> forall ars, Pa ars ->
    Pa (arms_cons tg e ars).

  Definition PC (e : exp) : Prop :=
    P e /\ (forall m, P (arm_inner m e)) /\ (forall fs, e = e_rec fs -> fields_all P fs).

  Definition PFC (fs : Goat_ott.fields) : Prop := Pf fs /\ fields_all P fs.

  Local Ltac nonlet Hp :=
    split; [ exact Hp | split;
      [ intros m; destruct m as [| m]; exact Hp
      | intros fs0 Hfs0; discriminate Hfs0 ] ].

  Theorem exp_fields_mutind_chain :
    (forall e, P e) /\ (forall fs, Pf fs) /\ (forall ars, Pa ars).
  Proof.
    assert (Hmain : (forall e, PC e) /\ (forall fs, PFC fs) /\ (forall ars, Pa ars)).
    { apply exp_fields_mutind; unfold PC, PFC.
      - intros i. nonlet (H_bvar i).
      - intros y. nonlet (H_fvar y).
      - intros n. nonlet (H_num n).
      - intros d. nonlet (H_dec d).
      - nonlet H_true.
      - nonlet H_false.
      - intros b [IHb _]. nonlet (H_abs b IHb).
      - intros a [IHa _] b [IHb _]. nonlet (H_app a IHa b IHb).
      - intros a [IHa _] b [IHb [IHc _]].
        assert (Hl : P (e_let a b)) by exact (H_let a IHa b IHb).
        split; [ exact Hl | split; [ exact (inner_let P a b Hl IHc) | intros fs0 Hfs0; discriminate Hfs0 ] ].
      - intros fs [IHfs _] b [IHb _]. nonlet (H_letrec fs IHfs b IHb).
      - intros fs [IHfs IHall].
        split; [ exact (H_rec fs IHfs) | split;
          [ intros m; destruct m as [| m]; exact (H_rec fs IHfs)
          | intros fs' Hfs; injection Hfs as <-; exact IHall ] ].
      - intros a [IHa _] l. nonlet (H_proj a IHa l).
      - nonlet H_unit.
      - intros q. nonlet (H_str q).
      - intros a [IHa _] b [IHb _] c [IHc _]. nonlet (H_ite a IHa b IHb c IHc).
      - intros a [IHa _] o b [IHb _]. nonlet (H_bin a IHa o b IHb).
      - intros a [IHa _]. nonlet (H_tofloat a IHa).
      - intros w tg a [IHa [_ IHall]]. nonlet (H_con w tg a IHa IHall).
      - intros w a [IHa _] ars IHars. nonlet (H_match w a IHa ars IHars).
      - intros a [IHa _] l b [IHb _]. nonlet (H_spread a IHa l b IHb).
      - intros a [IHa _] l. nonlet (H_restrict a IHa l).
      - intros a [IHa _]. nonlet (H_fold a IHa).
      - intros a [IHa _]. nonlet (H_unfold a IHa).
      - exact (conj H_fnil I).
      - intros l e [IHe _] fs [IHfs IHall]. exact (conj (H_fcons l e IHe fs IHfs) (conj IHe IHall)).
      - intros l e [IHe _] fs [IHfs IHall]. exact (conj (H_fmeth l e IHe fs IHfs) (conj IHe IHall)).
      - exact H_anil.
      - intros e [IHe _]. exact (H_aelse e IHe).
      - intros tg e [IHe [IHc _]] ars IHars. exact (H_acons tg e IHe IHc ars IHars). }
    destruct Hmain as [Hexp [Hf Ha]].
    refine (conj (fun e => proj1 (Hexp e)) (conj (fun fs => proj1 (Hf fs)) Ha)).
  Qed.
End Induction.
