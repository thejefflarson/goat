(* The bound indices of a printed term read as the names the printer gave them.
   A bound index reads as the free variable the parser gives its binder's name;
   a projection from a recursive group reads as the free variable of the member
   (ADR 0003: the group's name is one binder, each member's name stands for the
   projection of that member from it). Closing a binder's variable again, or
   binding a group's names, recovers the term. *)

From Stdlib Require Import String List Arith Lia.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatDen.
Require Import Goat.GoatPrint.
Require Import Goat.GoatPrintArm.
Open Scope string_scope.
Open Scope list_scope.

(* [k] binders of the term itself stay bound; the [D] enclosing ones read as
   names. A group's binder, entered at [k + D], joins [G]. *)
Fixpoint inst_rec (var_of : string -> termvar) (G : Grp) (k D : nat) (e : exp) {struct e} : exp :=
  match e with
  | e_fvar_b i =>
      if Nat.ltb i k then e_fvar_b i else e_fvar_f (var_of (nm (k + D - 1 - i)))
  | e_fvar_f y => e_fvar_f y
  | e_num n => e_num n
  | e_dec d => e_dec d
  | e_true => e_true
  | e_false => e_false
  | e_abs b => e_abs (inst_rec var_of G (S k) D b)
  | e_app a b => e_app (inst_rec var_of G k D a) (inst_rec var_of G k D b)
  | e_let a b => e_let (inst_rec var_of G k D a) (inst_rec var_of G (S k) D b)
  | e_letrec fs b =>
      e_letrec (inst_fields var_of ((k + D, flen fs) :: G) (S k) D fs)
               (inst_rec var_of ((k + D, flen fs) :: G) (S k) D b)
  | e_rec fs => e_rec (inst_fields var_of G k D fs)
  | e_proj a l =>
      match a with
      | e_fvar_b i =>
          if Nat.ltb i k then e_proj (e_fvar_b i) l
          else match grp_size G (k + D - 1 - i) with
               | Some _ => e_fvar_f (var_of (gm (k + D - 1 - i) l))
               | None => e_proj (e_fvar_f (var_of (nm (k + D - 1 - i)))) l
               end
      | _ => e_proj (inst_rec var_of G k D a) l
      end
  | e_unit => e_unit
  | e_str q => e_str q
  | e_ite a b c =>
      e_ite (inst_rec var_of G k D a) (inst_rec var_of G k D b) (inst_rec var_of G k D c)
  | e_bin a o b => e_bin (inst_rec var_of G k D a) o (inst_rec var_of G k D b)
  | e_tofloat a => e_tofloat (inst_rec var_of G k D a)
  | e_con w tg a => e_con w tg (inst_rec var_of G k D a)
  | e_match w a ars => e_match w (inst_rec var_of G k D a) (inst_arms var_of G k D ars)
  | e_spread a l b => e_spread (inst_rec var_of G k D a) l (inst_rec var_of G k D b)
  | e_restrict a l => e_restrict (inst_rec var_of G k D a) l
  | e_fold a => e_fold (inst_rec var_of G k D a)
  | e_unfold a => e_unfold (inst_rec var_of G k D a)
  end
with inst_fields (var_of : string -> termvar) (G : Grp) (k D : nat) (fs : Goat_ott.fields)
  {struct fs} : Goat_ott.fields :=
  match fs with
  | fs_nil => fs_nil
  | fs_cons l e rest => fs_cons l (inst_rec var_of G k D e) (inst_fields var_of G k D rest)
  | fs_meth l e rest => fs_meth l (inst_rec var_of G k D e) (inst_fields var_of G k D rest)
  end
with inst_arms (var_of : string -> termvar) (G : Grp) (k D : nat) (ars : arms) {struct ars} : arms :=
  match ars with
  | arms_nil => arms_nil
  | arms_else e => arms_else (inst_rec var_of G k D e)
  | arms_cons tg e ars' =>
      arms_cons tg (inst_rec var_of G (S k) D e) (inst_arms var_of G k D ars')
  end.

Definition inst (var_of : string -> termvar) (G : Grp) (D : nat) (e : exp) : exp :=
  inst_rec var_of G 0 D e.

Lemma inst_bvar : forall var_of G D i,
  inst var_of G D (e_fvar_b i) = e_fvar_f (var_of (nm (D - 1 - i))).
Proof. intros var_of G D i. reflexivity. Qed.

(* A group's member names, from member [i], and the members' values. *)
Fixpoint gnames (D i n : nat) : list string :=
  match n with
  | 0 => []
  | S n' => gm D i :: gnames D (S i) n'
  end.

Lemma gnames_length : forall D n i, length (gnames D i n) = n.
Proof. intros D n. induction n as [| n IH]; intros i; [ reflexivity | simpl; rewrite IH; reflexivity ]. Qed.

Fixpoint fvals (fs : Goat_ott.fields) : list exp :=
  match fs with
  | fs_nil => []
  | fs_cons _ v rest => v :: fvals rest
  | fs_meth _ v rest => v :: fvals rest
  end.

Lemma scoped_group_fields : forall fs G n i, scoped_group G n i fs -> scoped_fields G n fs.
Proof.
  induction fs as [| l v rest IH | l v rest IH]; intros G n i H; simpl in H.
  - exact I.
  - destruct H as (_ & _ & Hv & Hrest). exact (conj Hv (IH _ _ _ Hrest)).
  - destruct H.
Qed.

Lemma grp_size_here : forall L n G, grp_size ((L, n) :: G) L = Some n.
Proof. intros L n G. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma grp_size_there : forall l L n G, l <> L -> grp_size ((l, n) :: G) L = grp_size G L.
Proof.
  intros l L n G H. simpl. destruct (Nat.eqb l L) eqn:E; [ | reflexivity ].
  apply Nat.eqb_eq in E. contradiction.
Qed.

Lemma close_fvar_eq : forall k x, close_exp_rec k x (e_fvar_f x) = e_fvar_b k.
Proof.
  intros k x. cbn [close_exp_rec]. destruct (x == x) as [_ | H]; [ reflexivity | exfalso; apply H; reflexivity ].
Qed.

Lemma close_fvar_ne : forall k x y, y <> x -> close_exp_rec k x (e_fvar_f y) = e_fvar_f y.
Proof.
  intros k x y Hne. cbn [close_exp_rec]. destruct (y == x) as [H | _]; [ contradiction | reflexivity ].
Qed.

Lemma inst_proj_other : forall var_of G k D a l,
  (forall i, a <> e_fvar_b i) ->
  inst_rec var_of G k D (e_proj a l) = e_proj (inst_rec var_of G k D a) l.
Proof. intros var_of G k D a l H. destruct a; try reflexivity. exfalso. exact (H _ eq_refl). Qed.

Lemma scoped_proj_other : forall G n a l,
  (forall i, a <> e_fvar_b i) -> scoped G n (e_proj a l) -> scoped G n a.
Proof. intros G n a l H Hs. destruct a; try exact Hs. exfalso. exact (H _ eq_refl). Qed.

Lemma bvar_or_not : forall a, (exists i, a = e_fvar_b i) \/ (forall i, a <> e_fvar_b i).
Proof.
  intros a. destruct a;
    first [ (left; eexists; reflexivity) | (right; intros i H; discriminate H) ].
Qed.

Lemma close_proj : forall k x a l,
  close_exp_rec k x (e_proj a l) = e_proj (close_exp_rec k x a) l.
Proof. reflexivity. Qed.

Lemma bind_proj : forall k names a l,
  bind_group_rec k names (e_proj a l) = e_proj (bind_group_rec k names a) l.
Proof. reflexivity. Qed.

(* ---- closing the variable of a binder ---- *)

Lemma close_inst_projb : forall var_of, names_distinct var_of -> forall D i l G k,
  grp_size G D = None -> i < k + S D ->
  close_exp_rec k (var_of (nm D)) (inst_rec var_of G k (S D) (e_proj (e_fvar_b i) l))
  = inst_rec var_of G (S k) D (e_proj (e_fvar_b i) l).
Proof.
  intros var_of (Hnm & Hgm & Hdis) D i l G k HD Hi.
  cbn [inst_rec]. destruct (Nat.ltb i k) eqn:Hik.
  - assert (Hlt : Nat.ltb i (S k) = true)
      by (apply Nat.ltb_lt; apply Nat.ltb_lt in Hik; lia).
    rewrite Hlt. cbn [close_exp_rec]. reflexivity.
  - apply Nat.ltb_ge in Hik.
    destruct (Nat.eq_dec i k) as [-> | Hne].
    + assert (E : k + S D - 1 - k = D) by lia. rewrite E, HD.
      assert (Hlt : Nat.ltb k (S k) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt. cbn [close_exp_rec].
      destruct (var_of (nm D) == var_of (nm D)) as [_ | Hc];
        [ reflexivity | exfalso; apply Hc; reflexivity ].
    + assert (Hlt : Nat.ltb i (S k) = false) by (apply Nat.ltb_ge; lia).
      rewrite Hlt.
      assert (E : S k + D - 1 - i = k + S D - 1 - i) by lia. rewrite E.
      destruct (grp_size G (k + S D - 1 - i)).
      * cbn [close_exp_rec].
        destruct (var_of (gm (k + S D - 1 - i) l) == var_of (nm D)) as [H | _];
          [ exfalso; exact (Hdis D _ l (eq_sym H)) | reflexivity ].
      * cbn [close_exp_rec].
        destruct (var_of (nm (k + S D - 1 - i)) == var_of (nm D)) as [H | _];
          [ exfalso; apply Hnm in H; lia | reflexivity ].
Qed.

Lemma close_inst : forall var_of, names_distinct var_of -> forall D,
  (forall e G k, grp_size G D = None -> scoped G (k + S D) e ->
     close_exp_rec k (var_of (nm D)) (inst_rec var_of G k (S D) e)
     = inst_rec var_of G (S k) D e) /\
  (forall fs G k, grp_size G D = None -> scoped_fields G (k + S D) fs ->
     close_fields_rec k (var_of (nm D)) (inst_fields var_of G k (S D) fs)
     = inst_fields var_of G (S k) D fs) /\
  (forall ars : arms, forall w G k, grp_size G D = None -> scoped_arms G (k + S D) w ars ->
     close_arms_rec k (var_of (nm D)) (inst_arms var_of G k (S D) ars)
     = inst_arms var_of G (S k) D ars).
Proof.
  intros var_of Hdist D. pose proof Hdist as (Hnm & Hgm & Hdis).
  apply exp_fields_mutind.
  - (* bound index *)
    intros i G k HD (Hi & _).
    cbn [inst_rec]. destruct (Nat.ltb i k) eqn:Hik.
    + assert (Hlt : i < k) by (apply Nat.ltb_lt; exact Hik).
      assert (Hlt' : Nat.ltb i (S k) = true) by (apply Nat.ltb_lt; lia).
      cbn [close_exp_rec inst_rec]. rewrite Hlt'. reflexivity.
    + assert (Hge : k <= i) by (apply Nat.ltb_ge; exact Hik).
      cbn [close_exp_rec inst_rec].
      destruct (var_of (nm (k + S D - 1 - i)) == var_of (nm D)) as [Heq | Hne].
      * assert (Hnm' : k + S D - 1 - i = D) by (apply Hnm; exact Heq).
        assert (Hik' : i = k) by lia.
        subst i. assert (Hlt' : Nat.ltb k (S k) = true) by (apply Nat.ltb_lt; lia).
        rewrite Hlt'. reflexivity.
      * destruct (Nat.ltb i (S k)) eqn:Hlt'.
        { exfalso. apply Nat.ltb_lt in Hlt'.
          assert (Hik' : i = k) by lia. subst i.
          apply Hne. replace (k + S D - 1 - k) with D by lia. reflexivity. }
        replace (S k + D - 1 - i) with (k + S D - 1 - i) by lia.
        reflexivity.
  - intros y G k HD Hs. destruct Hs.
  - intros n G k HD Hs. reflexivity.
  - intros d G k HD Hs. reflexivity.
  - intros G k HD Hs. reflexivity.
  - intros G k HD Hs. reflexivity.
  - (* abs *)
    intros b IH G k HD Hs. simpl in Hs. simpl.
    destruct Hs as [-> | Hs]; [ reflexivity | ].
    rewrite (IH G (S k) HD Hs). reflexivity.
  - (* app *)
    intros a IHa b IHb G k HD [Ha Hb]. simpl.
    rewrite (IHa G k HD Ha).
    destruct Hb as [-> | Hb]; [ reflexivity | ].
    rewrite (IHb G k HD Hb). reflexivity.
  - (* let *)
    intros a IHa b IHb G k HD (Ha & Hb & _). simpl.
    rewrite (IHa G k HD Ha), (IHb G (S k) HD Hb). reflexivity.
  - (* recursive group *)
    intros fs IHfs b IHb G k HD (Hlen & Hgrp & Hb & _).
    assert (HD' : grp_size ((k + S D, flen fs) :: G) D = None).
    { rewrite grp_size_there; [ exact HD | lia ]. }
    assert (EG : (k + S D, flen fs) :: G = (S k + D, flen fs) :: G)
      by (f_equal; f_equal; lia).
    cbn [inst_rec close_exp_rec].
    rewrite (IHfs _ (S k) HD' (scoped_group_fields _ _ _ _ Hgrp)), (IHb _ (S k) HD' Hb).
    rewrite EG. reflexivity.
  - (* record *)
    intros fs IH G k HD Hs. simpl in *. rewrite (IH G k HD Hs). reflexivity.
  - (* projection *)
    intros a IH l G k HD Hs.
    destruct (bvar_or_not a) as [[i ->] | Hnb].
    + exact (close_inst_projb var_of Hdist D i l G k HD (proj1 Hs)).
    + rewrite (inst_proj_other var_of G k (S D) a l Hnb), close_proj,
        (IH G k HD (scoped_proj_other _ _ _ _ Hnb Hs)),
        (inst_proj_other var_of G (S k) D a l Hnb).
      reflexivity.
  - intros G k HD Hs. destruct Hs.
  - intros q G k HD Hs. reflexivity.
  - (* conditional *)
    intros a IHa b IHb c IHc G k HD (Ha & Hb & Hc). simpl.
    rewrite (IHa G k HD Ha), (IHb G k HD Hb).
    destruct Hc as [-> | Hc]; [ reflexivity | rewrite (IHc G k HD Hc); reflexivity ].
  - (* operation *)
    intros a IHa o b IHb G k HD [Ha Hb]. simpl.
    rewrite (IHa G k HD Ha), (IHb G k HD Hb). reflexivity.
  - intros a IH G k HD Hs. destruct Hs.
  - (* tag construction *)
    intros w tg a IH G k HD [Htg Ha]. cbn [inst_rec close_exp_rec].
    destruct (payload_scoped _ _ _ Ha) as [-> | Hs]; [ reflexivity | ].
    rewrite (IH G k HD Hs). reflexivity.
  - (* match *)
    intros w a IHa ars IHars G k HD [Ha Hars].
    destruct ars as [| e | tg b rest]; try (exfalso; exact Hars).
    cbn [inst_rec close_exp_rec]. rewrite (IHa G k HD Ha), (IHars w G k HD Hars). reflexivity.
  - intros a IHa l b IHb G k HD [Ha Hb]. simpl.
    rewrite (IHa G k HD Ha), (IHb G k HD Hb). reflexivity.
  - intros a IH l G k HD Hs. destruct Hs.
  - intros a IH G k HD Hs. destruct Hs.
  - intros a IH G k HD Hs. destruct Hs.
  - intros G k HD Hs. reflexivity.
  - intros l e IHe fs IHfs G k HD [He Hfs]. simpl.
    rewrite (IHe G k HD He), (IHfs G k HD Hfs). reflexivity.
  - intros l e IHe fs IHfs G k HD Hs. destruct Hs.
  - intros w G k HD Hs. reflexivity.
  - intros e IH w G k HD Hs. cbn [inst_arms close_arms_rec]. rewrite (IH G k HD Hs). reflexivity.
  - intros tg b IHb ars IHars w G k HD (Htg & Hs & _ & _ & Hr). cbn [inst_arms close_arms_rec].
    rewrite (IHb G (S k) HD Hs), (IHars w G k HD Hr). reflexivity.
Qed.

Lemma close_inst_exp : forall var_of G D b,
  names_distinct var_of -> grp_size G D = None -> scoped G (S D) b ->
  close_exp (var_of (nm D)) (inst_rec var_of G 0 (S D) b) = inst_rec var_of G 1 D b.
Proof.
  intros var_of G D b Hdist HD Hs. unfold close_exp.
  exact (proj1 (close_inst var_of Hdist D) b G 0 HD Hs).
Qed.

(* ---- binding a group's names ---- *)

Lemma index_in_gnames : forall var_of D,
  (forall d i e j, var_of (gm d i) = var_of (gm e j) -> d = e /\ i = j) ->
  forall n i l, i <= l -> l < i + n ->
  index_in (var_of (gm D l)) (List.map var_of (gnames D i n)) = Some (l - i).
Proof.
  intros var_of D Hgm n. induction n as [| n IH]; intros i l Hil Hln.
  - lia.
  - cbn [gnames List.map index_in].
    destruct (var_of (gm D l) == var_of (gm D i)) as [Heq | Hne].
    + apply Hgm in Heq. destruct Heq as [_ ->]. replace (i - i) with 0 by lia. reflexivity.
    + assert (Hli : l <> i) by (intros ->; apply Hne; reflexivity).
      rewrite (IH (S i) l); [ | lia | lia ].
      cbn [option_map]. f_equal. lia.
Qed.

Lemma index_in_none : forall var_of D y,
  (forall j, y <> var_of (gm D j)) ->
  forall n i, index_in y (List.map var_of (gnames D i n)) = None.
Proof.
  intros var_of D y Hy n. induction n as [| n IH]; intros i; [ reflexivity | ].
  cbn [gnames List.map index_in].
  destruct (y == var_of (gm D i)) as [Heq | Hne]; [ exfalso; exact (Hy i Heq) | ].
  rewrite (IH (S i)). reflexivity.
Qed.

Lemma bind_inst_projb : forall var_of, names_distinct var_of -> forall D n i l G k,
  grp_size G D = Some n -> i < k + S D ->
  (forall m, grp_size G (k + S D - 1 - i) = Some m -> l < m) ->
  bind_group_rec k (List.map var_of (gnames D 0 n))
                 (inst_rec var_of G k (S D) (e_proj (e_fvar_b i) l))
  = inst_rec var_of G (S k) D (e_proj (e_fvar_b i) l).
Proof.
  intros var_of (Hnm & Hgm & Hdis) D n i l G k HD Hi Hl.
  cbn [inst_rec]. destruct (Nat.ltb i k) eqn:Hik.
  - assert (Hlt : Nat.ltb i (S k) = true)
      by (apply Nat.ltb_lt; apply Nat.ltb_lt in Hik; lia).
    rewrite Hlt. cbn [bind_group_rec]. reflexivity.
  - apply Nat.ltb_ge in Hik.
    destruct (Nat.eq_dec i k) as [-> | Hne].
    + assert (E : k + S D - 1 - k = D) by lia. rewrite E in Hl |- *. rewrite HD.
      assert (Hlt : Nat.ltb k (S k) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt. cbn [bind_group_rec].
      assert (Hln : l < n) by exact (Hl n HD).
      rewrite (index_in_gnames var_of D Hgm n 0 l); [ | lia | lia ].
      cbn [option_map]. rewrite Nat.sub_0_r. reflexivity.
    + assert (Hlt : Nat.ltb i (S k) = false) by (apply Nat.ltb_ge; lia).
      rewrite Hlt.
      assert (E : S k + D - 1 - i = k + S D - 1 - i) by lia. rewrite E.
      destruct (grp_size G (k + S D - 1 - i)).
      * cbn [bind_group_rec]. rewrite (index_in_none var_of D); [ reflexivity | ].
        intros j H. apply Hgm in H. destruct H as [H _]. lia.
      * cbn [bind_group_rec]. rewrite (index_in_none var_of D); [ reflexivity | ].
        intros j H. exact (Hdis _ _ _ H).
Qed.

Lemma bind_inst : forall var_of, names_distinct var_of -> forall D n,
  (forall e G k, grp_size G D = Some n -> scoped G (k + S D) e ->
     bind_group_rec k (List.map var_of (gnames D 0 n)) (inst_rec var_of G k (S D) e)
     = inst_rec var_of G (S k) D e) /\
  (forall fs G k, grp_size G D = Some n -> scoped_fields G (k + S D) fs ->
     bind_group_fields k (List.map var_of (gnames D 0 n)) (inst_fields var_of G k (S D) fs)
     = inst_fields var_of G (S k) D fs) /\
  (forall ars : arms, forall w G k, grp_size G D = Some n -> scoped_arms G (k + S D) w ars ->
     bind_group_arms k (List.map var_of (gnames D 0 n)) (inst_arms var_of G k (S D) ars)
     = inst_arms var_of G (S k) D ars).
Proof.
  intros var_of Hdist D n. pose proof Hdist as (Hnm & Hgm & Hdis).
  apply exp_fields_mutind.
  - (* bound index: scoped rules out the group's own binder *)
    intros i G k HD (Hi & Hg).
    cbn [inst_rec]. destruct (Nat.ltb i k) eqn:Hik.
    + assert (Hlt : Nat.ltb i (S k) = true)
        by (apply Nat.ltb_lt; apply Nat.ltb_lt in Hik; lia).
      rewrite Hlt. cbn [bind_group_rec]. reflexivity.
    + apply Nat.ltb_ge in Hik.
      assert (Hne : i <> k).
      { intros ->. replace (k + S D - 1 - k) with D in Hg by lia.
        rewrite HD in Hg. discriminate Hg. }
      assert (Hlt : Nat.ltb i (S k) = false) by (apply Nat.ltb_ge; lia).
      rewrite Hlt. cbn [bind_group_rec].
      rewrite (index_in_none var_of D); [ | intros j H; exact (Hdis _ _ _ H) ].
      replace (S k + D - 1 - i) with (k + S D - 1 - i) by lia. reflexivity.
  - intros y G k HD Hs. destruct Hs.
  - intros m G k HD Hs. reflexivity.
  - intros d G k HD Hs. reflexivity.
  - intros G k HD Hs. reflexivity.
  - intros G k HD Hs. reflexivity.
  - (* abs *)
    intros b IH G k HD Hs. simpl in Hs. simpl.
    destruct Hs as [-> | Hs]; [ reflexivity | ].
    rewrite (IH G (S k) HD Hs). reflexivity.
  - (* app *)
    intros a IHa b IHb G k HD [Ha Hb]. simpl.
    rewrite (IHa G k HD Ha).
    destruct Hb as [-> | Hb]; [ reflexivity | ].
    rewrite (IHb G k HD Hb). reflexivity.
  - (* let *)
    intros a IHa b IHb G k HD (Ha & Hb & _). simpl.
    rewrite (IHa G k HD Ha), (IHb G (S k) HD Hb). reflexivity.
  - (* recursive group *)
    intros fs IHfs b IHb G k HD (Hlen & Hgrp & Hb & _).
    assert (HD' : grp_size ((k + S D, flen fs) :: G) D = Some n).
    { rewrite grp_size_there; [ exact HD | lia ]. }
    assert (EG : (k + S D, flen fs) :: G = (S k + D, flen fs) :: G)
      by (f_equal; f_equal; lia).
    cbn [inst_rec bind_group_rec].
    rewrite (IHfs _ (S k) HD' (scoped_group_fields _ _ _ _ Hgrp)), (IHb _ (S k) HD' Hb).
    rewrite EG. reflexivity.
  - (* record *)
    intros fs IH G k HD Hs. simpl in *. rewrite (IH G k HD Hs). reflexivity.
  - (* projection *)
    intros a IH l G k HD Hs.
    destruct (bvar_or_not a) as [[i ->] | Hnb].
    + exact (bind_inst_projb var_of Hdist D n i l G k HD (proj1 Hs) (proj2 Hs)).
    + rewrite (inst_proj_other var_of G k (S D) a l Hnb), bind_proj,
        (IH G k HD (scoped_proj_other _ _ _ _ Hnb Hs)),
        (inst_proj_other var_of G (S k) D a l Hnb).
      reflexivity.
  - intros G k HD Hs. destruct Hs.
  - intros q G k HD Hs. reflexivity.
  - (* conditional *)
    intros a IHa b IHb c IHc G k HD (Ha & Hb & Hc). simpl.
    rewrite (IHa G k HD Ha), (IHb G k HD Hb).
    destruct Hc as [-> | Hc]; [ reflexivity | rewrite (IHc G k HD Hc); reflexivity ].
  - (* operation *)
    intros a IHa o b IHb G k HD [Ha Hb]. simpl.
    rewrite (IHa G k HD Ha), (IHb G k HD Hb). reflexivity.
  - intros a IH G k HD Hs. destruct Hs.
  - (* tag construction *)
    intros w tg a IH G k HD [Htg Ha]. cbn [inst_rec bind_group_rec].
    destruct (payload_scoped _ _ _ Ha) as [-> | Hs]; [ reflexivity | ].
    rewrite (IH G k HD Hs). reflexivity.
  - (* match *)
    intros w a IHa ars IHars G k HD [Ha Hars].
    destruct ars as [| e | tg b rest]; try (exfalso; exact Hars).
    cbn [inst_rec bind_group_rec]. rewrite (IHa G k HD Ha), (IHars w G k HD Hars). reflexivity.
  - intros a IHa l b IHb G k HD [Ha Hb]. simpl.
    rewrite (IHa G k HD Ha), (IHb G k HD Hb). reflexivity.
  - intros a IH l G k HD Hs. destruct Hs.
  - intros a IH G k HD Hs. destruct Hs.
  - intros a IH G k HD Hs. destruct Hs.
  - intros G k HD Hs. reflexivity.
  - intros l e IHe fs IHfs G k HD [He Hfs]. simpl.
    rewrite (IHe G k HD He), (IHfs G k HD Hfs). reflexivity.
  - intros l e IHe fs IHfs G k HD Hs. destruct Hs.
  - intros w G k HD Hs. reflexivity.
  - intros e IH w G k HD Hs. cbn [inst_arms bind_group_arms]. rewrite (IH G k HD Hs). reflexivity.
  - intros tg b IHb ars IHars w G k HD (Htg & Hs & _ & _ & Hr). cbn [inst_arms bind_group_arms].
    rewrite (IHb G (S k) HD Hs), (IHars w G k HD Hr). reflexivity.
Qed.

(* The record of a group's members, as the denotation builds it from the
   members' values, is the instantiated fields. *)
Lemma group_fields_inst : forall var_of, names_distinct var_of -> forall D n G,
  grp_size G D = Some n ->
  forall fs i, scoped_group G (S D) i fs ->
  group_fields_from (List.map var_of (gnames D 0 n)) i
    (List.map (inst_rec var_of G 0 (S D)) (fvals fs))
  = inst_fields var_of G 1 D fs.
Proof.
  intros var_of Hdist D n G HD fs.
  induction fs as [| l v rest IH | l v rest IH]; intros i Hs.
  - reflexivity.
  - destruct Hs as (Hl & _ & Hv & Hrest). subst l.
    cbn [fvals List.map group_fields_from inst_fields].
    unfold bind_group.
    rewrite (proj1 (bind_inst var_of Hdist D n) v G 0 HD Hv), (IH _ Hrest). reflexivity.
  - destruct Hs.
Qed.
