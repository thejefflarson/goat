(* Soundness of algorithm W (GoatInfer.v) against the declarative [typing]:
   every type the algorithm infers is derivable (ADR 0037, decision 2).

   Read the statement of [infer_sound] first.  The algorithm threads a
   substitution [s], a kinding environment [D'] and a type [T]; the theorem
   says that, once [s] is applied to the context, the term has type [T] in
   [D'].  The side facts [OkS s] and [EvT T] are the even/odd bookkeeping of
   GoatInferSub.v that keeps substitutions off the quantified variables of
   schemes; [DOk] (GoatInferSort.v) says the environment is [Any] on the atoms
   the algorithm has not used, and [Good] bundles what each step of the
   algorithm preserves. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatTags.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSubst.
Require Import Goat.GoatSound.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferSub.
Require Import Goat.GoatInferSort.
Require Import Goat.GoatInferTyp.
Require Import Goat.GoatInferRen.
Require Import Goat.GoatInferUnify.
Require Import Goat.GoatInferGen.
Require Import Goat.GoatInferRec.
Require Import Goat.GoatElab.
Require Import Goat.GoatClose.
Require Import Goat.GoatKnot.
Require Import Goat.GoatInferKnot.
Require Import Goat.GoatCoerce.
Require Import Goat.GoatInferW.
Require Import Stdlib.Lists.List.
From Stdlib Require Import Lia.
Import ListNotations.

Lemma lookup_binds : forall x G s, lookup x G = Some s -> binds x s G.
Proof.
  intros x G. induction G as [|[y sy] G IH]; intros s H; simpl in H; [discriminate|].
  destruct (Atom.eq_dec x y) as [->|Hne].
  - inversion H; subst. apply binds_cons_2; reflexivity.
  - apply binds_cons_3. apply IH. exact H.
Qed.

Lemma fresh_var_notin_dom : forall G e, fresh_var G e `notin` dom G.
Proof.
  intros G e. unfold fresh_var. intro H.
  apply (fresh_not_in (AtomSetImpl.elements (dom G `union` fv_exp e))).
  apply In_elements. fsetdec.
Qed.

Lemma fresh_var_notin_fv : forall G e, fresh_var G e `notin` fv_exp e.
Proof.
  intros G e. unfold fresh_var. intro H.
  apply (fresh_not_in (AtomSetImpl.elements (dom G `union` fv_exp e))).
  apply In_elements. fsetdec.
Qed.

Lemma apT_sid : forall T, apT sid T = T.
Proof. intros T. unfold apT, sid; simpl. apply ap_typ_pointwise_id; reflexivity. Qed.

Lemma apC_sid : forall G, apC sid G = G.
Proof.
  induction G as [|[x sc] G IH]; simpl; [reflexivity|].
  rewrite IH. destruct sc as [q r b]. unfold apS in *. cbn [s_tq s_rq s_body].
  rewrite apT_sid. reflexivity.
Qed.

Lemma EvT_Int : EvT typ_Int.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Lemma EvT_Float : EvT typ_Float.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Lemma EvT_String : EvT typ_String.
Proof. split; intros a Ha; simpl in Ha; fsetdec. Qed.

Definition ground (T : typ) : Prop :=
  T = typ_Int \/ T = typ_Float \/ T = typ_String \/ T = typ_Bool.

Lemma ground_ap : forall s T, ground T -> apT s T = T.
Proof. intros s T [H|[H|[H|H]]]; subst; reflexivity. Qed.

Lemma ground_EvT : forall T, ground T -> EvT T.
Proof.
  intros T [H|[H|[H|H]]]; subst;
    first [ apply EvT_Int | apply EvT_Float | apply EvT_String | apply EvT_Bool ].
Qed.

Lemma EvT_arrow : forall A B, EvT A -> EvT B -> EvT (typ_Arrow A B).
Proof.
  intros A B [H1 H2] [H3 H4]. split; intros a Ha; simpl in Ha;
    apply AtomSetFacts.union_iff in Ha; destruct Ha as [Ha|Ha]; auto.
Qed.

Lemma pin_of_ev : forall D T, EvT T -> EvT (pin_of (lit_vars D T)).
Proof.
  intros D T [Ht Hr]. unfold lit_vars.
  assert (Hin : forall la, (forall a, In a la -> ev a) -> EvT (pin_of la)).
  { induction la as [|a la IH]; intros H; simpl.
    - apply EvT_Unit.
    - apply EvT_arrow; [ apply EvT_var; apply H; left; reflexivity | ].
      apply IH. intros b Hb. apply H. right. exact Hb. }
  apply Hin. intros a Ha. apply filter_In in Ha as [Ha _].
  apply Ht. apply In_elements. exact Ha.
Qed.

Lemma let_pin_EvT : forall D e T, EvT T -> EvT (let_pin D e T).
Proof.
  intros D e T H. unfold let_pin. destruct (let_open e); [ apply EvT_Unit | apply pin_of_ev; exact H ].
Qed.

(* What a [let] keeps monomorphic: nothing for a function or a bare numeral,
   and the [Literal] variables of its type, only those, for any other value. *)
Lemma let_pin_open : forall D e T, let_open e = true -> let_pin D e T = typ_Unit.
Proof. intros D e T H. unfold let_pin. rewrite H. reflexivity. Qed.

Lemma ftv_pin_of : forall la a, a `in` ftv_typ (pin_of la) <-> In a la.
Proof.
  induction la as [|b la IH]; intros a; simpl.
  - split; [ intros H; exfalso; fsetdec | intros [] ].
  - rewrite AtomSetFacts.union_iff, AtomSetFacts.singleton_iff, IH.
    split; intros [->|H]; [ left; reflexivity | right; exact H | left; reflexivity | right; exact H ].
Qed.

Lemma let_pin_ftv : forall D e T a,
  let_open e = false ->
  (a `in` ftv_typ (let_pin D e T) <-> a `in` ftv_typ T /\ D a = k_Literal).
Proof.
  intros D e T a H. unfold let_pin. rewrite H, ftv_pin_of. unfold lit_vars.
  rewrite filter_In, In_elements.
  split; intros [H1 H2]; split; auto.
  - destruct (D a); simpl in H2; congruence.
  - rewrite H2. reflexivity.
Qed.

Example numeral_binding_pins_nothing : forall D n T, let_pin D (e_num n) T = typ_Unit.
Proof. intros. apply let_pin_open. reflexivity. Qed.

Example function_binding_pins_nothing : forall D e T, let_pin D (e_abs e) T = typ_Unit.
Proof. intros. apply let_pin_open. reflexivity. Qed.

Example name_binding_pins_its_literals : forall (D : denv) x T a,
  a `in` ftv_typ T -> D a = k_Literal -> a `in` ftv_typ (let_pin D (e_fvar_f x) T).
Proof. intros D x T a H1 H2. apply let_pin_ftv; [ reflexivity | split; assumption ]. Qed.

Example record_binding_leaves_other_sorts_open : forall (D : denv) fs T a,
  D a <> k_Literal -> a `notin` ftv_typ (let_pin D (e_rec fs) T).
Proof.
  intros D fs T a H Hin. apply let_pin_ftv in Hin; [ | reflexivity ]. destruct Hin as [_ Hin]. contradiction.
Qed.


(* ------------------------------------------------------------------ *)
(* What each step of the algorithm preserves                            *)
(* ------------------------------------------------------------------ *)

(* A step from environment [D] with supply [n] to [D'] with supply [n'],
   applying [s]: [D] is [Any] beyond [n], [s] is a substitution of the
   algorithm, the supply only grows, [D'] refines [D], and [s] respects the
   sorts. *)
Definition Good (D : denv) (n : nat) (s : sub) (D' : denv) (n' : nat) : Prop :=
  DOk D n /\ OkS s /\ DOk D' n' /\ n <= n' /\ kres D D' idt /\ kres D D' (sT s).

Lemma Good_id : forall D n, DOk D n -> Good D n sid D n.
Proof.
  intros D n H.
  exact (conj H (conj OkS_id (conj H (conj (le_n n) (conj (kres_id D) (kres_id D)))))).
Qed.

Lemma Good_comp : forall D n s1 D1 n1 s2 D2 n2,
  Good D n s1 D1 n1 -> Good D1 n1 s2 D2 n2 -> Good D n (scomp s2 s1) D2 n2.
Proof.
  intros D n s1 D1 n1 s2 D2 n2 (Hd & Hs1 & Hd1 & Hl1 & Hi1 & Hk1) (_ & Hs2 & Hd2 & Hl2 & Hi2 & Hk2).
  exact (conj Hd (conj (OkS_comp _ _ Hs2 Hs1) (conj Hd2 (conj (Nat.le_trans _ _ _ Hl1 Hl2)
    (conj (kres_idt_trans _ _ _ (DOk_rtriv _ _ Hd1) Hi1 Hi2)
          (kres_scomp _ _ _ _ _ (DOk_rtriv _ _ Hd1) Hk1 Hk2)))))).
Qed.

Lemma Good_unify : forall D n s n',
  OkS s -> kres D D (sT s) -> n <= n' -> DOk D n -> Good D n s D n'.
Proof.
  intros D n s n' Hs Hk Hl Hd.
  exact (conj Hd (conj Hs (conj (DOk_mono D n n' Hd Hl) (conj Hl (conj (kres_id D) Hk))))).
Qed.

Lemma Good_lift : forall D n D' n' s D'' n'',
  Good D n sid D' n' -> Good D' n' s D'' n'' -> Good D n s D'' n''.
Proof.
  intros D n D' n' s D'' n'' (Hd & _ & Hd1 & Hl1 & Hi1 & _) (_ & Hs & Hd2 & Hl2 & Hi2 & Hk2).
  exact (conj Hd (conj Hs (conj Hd2 (conj (Nat.le_trans _ _ _ Hl1 Hl2)
    (conj (kres_idt_trans _ _ _ (DOk_rtriv _ _ Hd1) Hi1 Hi2) (kres_refine_l _ _ _ _ Hi1 Hk2)))))).
Qed.

Lemma Good_upd : forall D n k, DOk D n -> Good D n sid (upd D (ea n) k) (S n).
Proof.
  intros D n k H.
  exact (conj H (conj OkS_id (conj (DOk_upd D n k H) (conj (le_S _ _ (le_n n))
    (conj (kres_upd D n k H) (kres_upd D n k H)))))).
Qed.

Lemma Good_pre : forall D n m s D' n',
  n <= m -> DOk D n -> Good D m s D' n' -> Good D n s D' n'.
Proof.
  intros D n m s D' n' Hnm Hd (_ & Hs & Hd' & Hl & Hi & Hk).
  exact (conj Hd (conj Hs (conj Hd' (conj (Nat.le_trans _ _ _ Hnm Hl) (conj Hi Hk))))).
Qed.

(* The environment of a step of the algorithm has no constrained row variable:
   a hypothesis that it is well kept ([DOk]) or the source or target of a good
   step says so. *)
Ltac solve_rtriv :=
  multimatch goal with
  | H : rtriv _ |- _ => exact H
  | H : DOk _ _ |- _ => exact (DOk_rtriv _ _ H)
  | H : Good _ _ _ _ _ |- _ => exact (DOk_rtriv _ _ (proj1 H))
  | H : Good _ _ _ _ _ |- _ => exact (DOk_rtriv _ _ (proj1 (proj2 (proj2 H))))
  end.

Lemma typing_ap_G : forall D n s D' n' G e T,
  Good D n s D' n' -> WfCtx G -> typing D G e T -> typing D' (apC s G) e (apT s T).
Proof.
  intros D n s D' n' G e T (Hd & Hs & Hd' & _ & _ & Hk) HG Hty.
  exact (typing_ap D D' s G e T Hs HG (DOk_supp D n Hd) (DOk_supp D' n' Hd') Hk
           (rkres_triv _ _ _ (DOk_rtriv _ _ Hd)) Hty).
Qed.

Lemma typing_refine : forall D n D' n' G e T,
  Good D n sid D' n' -> WfCtx G -> typing D G e T -> typing D' G e T.
Proof.
  intros D n D' n' G e T Hg HG Hty.
  pose proof (typing_ap_G D n sid D' n' G e T Hg HG Hty) as H.
  rewrite apC_sid, apT_sid in H. exact H.
Qed.

(* The sorts the generalization records survive a step of the algorithm. *)
Lemma kres_ext_lift : forall D D' s V k,
  OkS s -> kres D D' (sT s) -> (forall a, a `in` V -> od a) ->
  kres (ext D V k) (ext D' V k) (sT s).
Proof.
  intros D D' s V k Hs Hk Hodd a.
  destruct Hs as [_ [Ht [_ [Hfx _]]]].
  destruct (AtomSetImpl.mem a V) eqn:Em.
  - apply AtomSetFacts.mem_iff in Em. rewrite (ext_in _ _ _ _ Em).
    rewrite (Hfx a (not_ev_od a (Hodd a Em))). cbn [sat]. rewrite (ext_in _ _ _ _ Em). apply finer_refl.
  - apply AtomSetFacts.not_mem_iff in Em. unfold kres in Hk.
    pose proof (Hk a) as Hka.
    rewrite (ext_out _ _ _ _ Em).
    apply sat_ext_out; [ exact Hka | ].
    intros b Hb Hbv.
    assert (Hna : ~ ev a).
    { intro Hea. pose proof (Ht a Hea) as HE.
      exact (ev_od b ((proj1 HE) b Hb) (Hodd b Hbv)). }
    rewrite (Hfx a Hna) in Hb. simpl in Hb.
    assert (b = a) by fsetdec. subst. contradiction.
Qed.

(* ------------------------------------------------------------------ *)
(* Tag groups                                                           *)
(* ------------------------------------------------------------------ *)

Lemma apT_grp : forall s w A, apT s (typ_Grp w A) = typ_Grp w (apT s A).
Proof. reflexivity. Qed.

Lemma apT_spine : forall s Ts, apT s (spine Ts) = spine (map (apT s) Ts).
Proof. intros s Ts. exact (ap_spine (sT s) (sR s) Ts). Qed.

Lemma apT_tag_payload : forall s w Ts tg,
  apT s (tag_payload w Ts tg) = tag_payload w (map (apT s) Ts) tg.
Proof. intros s w Ts tg. exact (ap_tag_payload (sT s) (sR s) w Ts tg). Qed.

Lemma apS_mono : forall s T, apS s (sch_mono T) = sch_mono (apT s T).
Proof. reflexivity. Qed.

Lemma map_apT_comp : forall s2 s1 Ts,
  map (apT s2) (map (apT s1) Ts) = map (apT (scomp s2 s1)) Ts.
Proof. intros s2 s1 Ts. rewrite map_map. apply map_ext. intros T. apply apT_comp. Qed.

Lemma EvT_grp : forall w A, EvT A -> EvT (typ_Grp w A).
Proof. intros w A H. exact H. Qed.

Lemma EvT_spine : forall Ts, Forall EvT Ts -> EvT (spine Ts).
Proof.
  intros Ts H. induction H; simpl; [ apply EvT_Unit | apply EvT_arrow; assumption ].
Qed.

Lemma EvT_nth : forall Ts j, Forall EvT Ts -> EvT (nth j Ts typ_Unit).
Proof.
  intros Ts j H. revert j. induction H as [|T Ts HT HTs IH]; intros [|j]; simpl;
    [ apply EvT_Unit | apply EvT_Unit | exact HT | apply IH ].
Qed.

Lemma EvT_slot_ty : forall w Ts c, Forall EvT Ts -> EvT (slot_ty w Ts c).
Proof.
  intros w Ts c H. unfold slot_ty. destruct c as [|[|[|[|[|[|c]]]]]]; simpl;
    first [ apply EvT_Int | apply EvT_Float | apply EvT_Bool | apply EvT_Unit | apply EvT_String
          | (apply EvT_grp; apply EvT_spine; exact H) | (apply EvT_nth; exact H) ].
Qed.

Lemma EvR_slots_row : forall w Ts cs i, Forall EvT Ts -> EvR (slots_row w Ts i cs).
Proof.
  intros w Ts cs. induction cs as [|c cs IH]; intros i H; simpl;
    [ apply EvR_Empty | apply EvR_ext; [ apply EvT_slot_ty; exact H | apply IH; exact H ] ].
Qed.

Lemma EvT_tag_payload : forall w Ts tg, Forall EvT Ts -> EvT (tag_payload w Ts tg).
Proof.
  intros w Ts tg H. unfold tag_payload. destruct (nth_error w tg) as [cs|]; [|apply EvT_Unit].
  unfold payload_ty. destruct cs; [ apply EvT_Unit | apply EvT_Record; apply EvR_slots_row; exact H ].
Qed.

Lemma EvT_fresh_tys : forall k n, Forall EvT (fresh_tys n k).
Proof.
  induction k as [|k IH]; intros n; simpl; [ constructor | constructor; [ apply EvT_var, ev_ea | apply IH ] ].
Qed.

Lemma Forall_EvT_ap : forall s Ts, OkS s -> Forall EvT Ts -> Forall EvT (map (apT s) Ts).
Proof.
  intros s Ts Hs H. induction H; simpl; constructor; [ apply EvT_ap; assumption | assumption ].
Qed.

Lemma nodup_b_sound : forall l, nodup_b l = true -> NoDup l.
Proof.
  induction l as [|a l IH]; intros H; simpl in H; [ constructor | ].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2]. constructor.
  - intro Hin. apply Bool.negb_true_iff in H1.
    assert (Hex : existsb (Nat.eqb a) l = true)
      by (apply existsb_exists; exists a; split; [ exact Hin | apply Nat.eqb_refl ]).
    congruence.
  - apply IH. exact H2.
Qed.

Lemma arms_wf_b_sound : forall w ars, arms_wf_b w ars = true -> arms_wf w ars.
Proof.
  intros w ars H. unfold arms_wf_b in H. rewrite !Bool.andb_true_iff in H.
  destruct H as [[H1 H2] H3]. unfold arms_wf. split; [ apply nodup_b_sound; exact H1 | split ].
  - intros tg Hin. rewrite forallb_forall in H2. apply Nat.ltb_lt. apply H2. exact Hin.
  - destruct (arms_default ars) as [e|] eqn:Ed; [ left; discriminate | right ].
    intros tg Hlt. rewrite forallb_forall in H3.
    assert (Hs : In tg (seq 0 (length w))) by (apply in_seq; lia).
    pose proof (H3 tg Hs) as Hex. apply existsb_exists in Hex.
    destruct Hex as [y [Hy Heq]]. apply Nat.eqb_eq in Heq. subst. exact Hy.
Qed.

(* What [T_Match] asks of the arms of a match. *)
Definition arms_typ (L : vars) (D : denv) (G : ctx) (w : gdecl) (Ts : list typ)
  (ars : arms) (T : typ) : Prop :=
  (forall tg body, arms_find tg ars = Some body -> forall y, y `notin` L ->
     typing D ((y ~ sch_mono (tag_payload w Ts tg)) ++ G)
       (open_exp_wrt_exp body (e_fvar_f y)) T) /\
  (forall e0, arms_default ars = Some e0 -> typing D G e0 T).

Lemma arms_typ_nil : forall L D G w Ts T, arms_typ L D G w Ts arms_nil T.
Proof.
  intros L D G w Ts T. split; intros; simpl in *; discriminate.
Qed.

Lemma arms_typ_else : forall L D G w Ts e T,
  typing D G e T -> arms_typ L D G w Ts (arms_else e) T.
Proof.
  intros L D G w Ts e T H. split.
  - intros tg body Hf. simpl in Hf. discriminate.
  - intros e0 Hd. simpl in Hd. inversion Hd; subst. exact H.
Qed.

Lemma arms_typ_cons : forall L D G w Ts tg e rest T,
  (forall y, y `notin` L ->
     typing D ((y ~ sch_mono (tag_payload w Ts tg)) ++ G) (open_exp_wrt_exp e (e_fvar_f y)) T) ->
  arms_typ L D G w Ts rest T -> arms_typ L D G w Ts (arms_cons tg e rest) T.
Proof.
  intros L D G w Ts tg e rest T Hb [Hr Hd]. split.
  - intros tg0 body Hf y Hy. simpl in Hf. destruct (Nat.eqb tg0 tg) eqn:E.
    + inversion Hf; subst. apply Nat.eqb_eq in E. subst. apply Hb. exact Hy.
    + eapply Hr; eauto.
  - intros e0 Hd0. simpl in Hd0. apply Hd. exact Hd0.
Qed.

Lemma arms_typ_L : forall L1 L2 D G w Ts ars T,
  L1 [<=] L2 -> arms_typ L1 D G w Ts ars T -> arms_typ L2 D G w Ts ars T.
Proof.
  intros L1 L2 D G w Ts ars T Hsub [Hr Hd]. split.
  - intros tg body Hf y Hy. eapply Hr; [ exact Hf | fsetdec ].
  - exact Hd.
Qed.

(* A derivation under the payload binder survives a step of the algorithm. *)
Lemma arm_lift : forall D n s D' n' G w Ts tg y b T,
  Good D n s D' n' -> WfCtx G -> Forall EvT Ts -> y `notin` dom G ->
  typing D ((y ~ sch_mono (tag_payload w Ts tg)) ++ G) b T ->
  typing D' ((y ~ sch_mono (tag_payload w (map (apT s) Ts) tg)) ++ apC s G) b (apT s T).
Proof.
  intros D n s D' n' G w Ts tg y b T Hg HG HTs Hy Hty.
  assert (Hwf : WfCtx ((y ~ sch_mono (tag_payload w Ts tg)) ++ G))
    by (apply WfCtx_cons; [ exact HG | exact Hy | apply WfSch_mono, EvT_tag_payload; exact HTs ]).
  pose proof (typing_ap_G D n s D' n' _ _ _ Hg Hwf Hty) as H.
  rewrite apC_app, apC_single, apS_mono, apT_tag_payload in H. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* Binders: the elaborated body is closed over the fresh variable        *)
(* ------------------------------------------------------------------ *)

Lemma typing_open_cl : forall D G x y sc e T,
  typing D ((x ~ sc) ++ G) e T -> lce 0 e -> y `notin` dom ((x ~ sc) ++ G) ->
  typing D ((y ~ sc) ++ G) (open_exp_wrt_exp (cl 0 x e) (e_fvar_f y)) T.
Proof.
  intros D G x y sc e T Hty Hlc Hy. unfold open_exp_wrt_exp.
  rewrite (proj1 open_cl_mut e 0 x y Hlc).
  exact (proj1 (typing_rename_var_mut x y sc G) _ _ _ _ Hty nil eq_refl Hy).
Qed.

Lemma fields_open_cl : forall D G x y sc fs R,
  field_typing D ((x ~ sc) ++ G) fs R -> lcef 0 fs -> y `notin` dom ((x ~ sc) ++ G) ->
  field_typing D ((y ~ sc) ++ G) (open_fields_wrt_exp (clf 0 x fs) (e_fvar_f y)) R.
Proof.
  intros D G x y sc fs R Hty Hlc Hy. unfold open_fields_wrt_exp.
  rewrite (proj1 (proj2 open_cl_mut) fs 0 x y Hlc).
  exact (proj2 (typing_rename_var_mut x y sc G) _ _ _ _ Hty nil eq_refl Hy).
Qed.

Lemma bind_ok : forall x b b',
  erase b' = open_exp_wrt_exp b (e_fvar_f x) -> lce 0 b' -> x `notin` fv_exp b ->
  erase (cl 0 x b') = b /\ lce 1 (cl 0 x b').
Proof.
  intros x b b' Her Hlc Hx. split.
  - rewrite (proj1 erase_cl_mut), Her. apply (proj1 cl_open_mut b 0 x); [ | exact Hx ].
    apply (proj1 lce_open_inv_mut b 0 x). unfold open_exp_wrt_exp in Her.
    rewrite <- Her. apply (proj1 lce_erase_mut). exact Hlc.
  - apply (proj1 lce_cl_mut). exact Hlc.
Qed.

Lemma bind_ok_fields : forall x fs fs',
  erase_fields fs' = open_fields_wrt_exp fs (e_fvar_f x) -> lcef 0 fs' -> x `notin` fv_fields fs ->
  erase_fields (clf 0 x fs') = fs /\ lcef 1 (clf 0 x fs').
Proof.
  intros x fs fs' Her Hlc Hx. split.
  - rewrite (proj1 (proj2 erase_cl_mut)), Her. apply (proj1 (proj2 cl_open_mut) fs 0 x); [ | exact Hx ].
    apply (proj1 (proj2 lce_open_inv_mut) fs 0 x). unfold open_fields_wrt_exp in Her.
    rewrite <- Her. apply (proj1 (proj2 lce_erase_mut)). exact Hlc.
  - apply (proj1 (proj2 lce_cl_mut)). exact Hlc.
Qed.

(* The members of a recursive group stay functions through elaboration: the
   algorithm builds a function's elaboration as a function. *)
Lemma infer_abs_shape : forall f D G b n s D' T n' e',
  infer f D G (e_abs b) n = Some (s, D', T, n', e') -> exists b', e' = e_abs b'.
Proof.
  intros f D G b n s D' T n' e' H. destruct f as [|f]; [ discriminate H | ].
  cbn [infer] in H.
  destruct (infer f D ((fresh_var G b ~ sch_mono (typ_Var (ea n))) ++ G)
              (open_exp_wrt_exp b (e_fvar_f (fresh_var G b))) (S n))
    as [[[[[s0 D1] T0] n0] b0]|]; [ | discriminate H ].
  inversion H; subst. eexists. reflexivity.
Qed.

Lemma is_fn_group_open_rec : forall fs k u,
  is_fn_group fs = true -> is_fn_group (open_fields_wrt_exp_rec k u fs) = true.
Proof.
  induction fs as [|l e rest IH|l e rest IH]; intros k u H; simpl in *; [ reflexivity | | discriminate H ].
  destruct e; try discriminate H. simpl. apply IH. exact H.
Qed.

Lemma infer_fields_fn_group : forall f D G fs n s D' R n' fs',
  is_fn_group fs = true -> infer_fields f D G fs n = Some (s, D', R, n', fs') ->
  fn_group fs'.
Proof.
  intros f D G fs. revert f D G. induction fs as [|l e rest IH|l e rest IH]; intros f D G n s D' R n' fs' Hg H;
    destruct f as [|f]; try discriminate H; cbn [infer_fields] in H.
  - inversion H; subst. constructor.
  - destruct e; try discriminate Hg. cbn [is_fn_group] in Hg.
    destruct (infer f D G (e_abs e) n) as [[[[[s1 D1] T1] n1] e1']|] eqn:E1; [ | discriminate H ].
    destruct (infer_fields f D1 (apC s1 G) rest n1) as [[[[[s2 D2] R2] n2] rest']|] eqn:E2;
      [ | discriminate H ].
    inversion H; subst.
    destruct (infer_abs_shape _ _ _ _ _ _ _ _ _ _ E1) as [b' ->].
    constructor. exact (IH _ _ _ _ _ _ _ _ _ Hg E2).
Qed.

Lemma infer_fields_no_meth : forall f D G fs n s D' R n' fs',
  infer_fields f D G fs n = Some (s, D', R, n', fs') -> no_meth fs' = true.
Proof.
  intros f D G fs. revert f D G. induction fs as [|l e rest IH|l e rest IH];
    intros f D G n s D' R n' fs' H; destruct f as [|f]; try discriminate H; cbn [infer_fields] in H.
  - inversion H; subst. reflexivity.
  - destruct (infer f D G e n) as [[[[[s1 D1] T1] n1] e1']|]; [ | discriminate H ].
    destruct (infer_fields f D1 (apC s1 G) rest n1) as [[[[[s2 D2] R2] n2] rest']|] eqn:E2;
      [ | discriminate H ].
    inversion H; subst. cbn [no_meth]. exact (IH _ _ _ _ _ _ _ _ _ E2).
Qed.

Lemma fn_group_clf : forall fs k x, fn_group fs -> fn_group (clf k x fs).
Proof.
  intros fs k x H. induction H; cbn [clf cl]; constructor. exact IHfn_group.
Qed.

Lemma arms_wf_b_erase : forall w a, arms_wf_b w (erase_arms a) = arms_wf_b w a.
Proof.
  intros w a. unfold arms_wf_b.
  assert (Hi : arms_idx (erase_arms a) = arms_idx a).
  { induction a; cbn [erase_arms arms_idx]; [ reflexivity | reflexivity | rewrite IHa; reflexivity ]. }
  rewrite Hi, erase_arms_default. destruct (arms_default a); reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Method literals: the receiver and the slots                           *)
(* ------------------------------------------------------------------ *)

Lemma fields_ap_G : forall D n s D' n' G fs R,
  Good D n s D' n' -> WfCtx G -> field_typing D G fs R -> field_typing D' (apC s G) fs (apR s R).
Proof.
  intros D n s D' n' G fs R (Hd & Hs & Hd' & _ & _ & Hk) HG Hty.
  exact (fields_ap0 D D' s G fs R Hs HG (DOk_supp D n Hd) (DOk_supp D' n' Hd') Hk
           (rkres_triv _ _ _ (DOk_rtriv _ _ Hd)) Hty).
Qed.

(* A method field's type is a function of the receiver [P]. *)
Inductive meth_ty (P : typ) : fields -> row -> Prop :=
 | MT_nil : meth_ty P fs_nil row_Empty
 | MT_cons : forall l e rest T R,
     meth_ty P rest R -> meth_ty P (fs_cons l e rest) (row_Ext l T R)
 | MT_meth : forall l e rest T1 R,
     meth_ty P rest R -> meth_ty P (fs_meth l e rest) (row_Ext l (typ_Arrow P T1) R).

Lemma meth_ty_ap : forall s P fs R, meth_ty P fs R -> meth_ty (apT s P) fs (apR s R).
Proof. intros s P fs R H. induction H; simpl; constructor; assumption. Qed.

(* Each method field's type meets its slot up to unrolling. *)
Inductive meth_rel : fields -> row -> row -> Prop :=
 | MRl_nil : meth_rel fs_nil row_Empty row_Empty
 | MRl_cons : forall l e rest T A R Rsl,
     meth_rel rest R Rsl -> meth_rel (fs_cons l e rest) (row_Ext l T R) (row_Ext l A Rsl)
 | MRl_meth : forall l e rest T A R Rsl n,
     unroll_eq n A T -> meth_rel rest R Rsl ->
     meth_rel (fs_meth l e rest) (row_Ext l T R) (row_Ext l A Rsl).

Lemma meths_shared_of : forall fs R Rsl, meth_rel fs R Rsl ->
  forall P Rs fs2, meth_ty P fs R -> P = typ_Record Rs -> marks fs2 = marks fs ->
  meths_shared Rs fs2 Rsl.
Proof.
  intros fs R Rsl H. induction H; intros P Rs fs2 Hty HP Hm.
  - destruct fs2; try discriminate Hm. constructor.
  - inversion Hty; subst.
    destruct fs2 as [|l2 e2 fs2|l2 e2 fs2]; try discriminate Hm.
    simpl in Hm. injection Hm as Hl Hm. subst l2. constructor. eapply IHmeth_rel; eauto.
  - inversion Hty; subst.
    destruct fs2 as [|l2 e2 fs2|l2 e2 fs2]; try discriminate Hm.
    simpl in Hm. injection Hm as Hl Hm. subst l2. eapply MS_meth; [ exact H | ].
    eapply IHmeth_rel; eauto.
Qed.

Lemma tie_obj_sound : forall f D fs R Rsl n s n' fs2,
  tie_obj f D fs R Rsl n = Some (s, n', fs2) ->
  forall G, WfCtx G -> DOk D n -> EvR R -> EvR Rsl -> field_typing D G fs R -> lcef 0 fs ->
  Good D n s D n' /\ field_typing D (apC s G) fs2 (apR s Rsl) /\
  erase_fields fs2 = erase_fields fs /\ lcef 0 fs2 /\ marks fs2 = marks fs /\
  meth_rel fs (apR s R) (apR s Rsl).
Proof.
  intros f D fs. induction fs as [|l e rest IH|l e rest IH];
    intros R Rsl n s n' fs2 H G HG HD HR HRsl Hft Hlc;
    destruct R as [|r|l1 T R'|l1 P0 T0 R'], Rsl as [|r2|l2 A Rsl'|l2 P2 T2 R2'];
    simpl in H; try discriminate H.
  - inversion H; subst; clear H.
    refine (conj (Good_id _ _ HD) _).
    rewrite apC_sid, apR_id. refine (conj _ (conj eq_refl (conj I (conj eq_refl MRl_nil)))).
    apply FT_nil. exact (proj1 HG).
  - destruct (Nat.eqb l l1 && Nat.eqb l l2) eqn:Hl; [ | discriminate H ].
    apply Bool.andb_true_iff in Hl. destruct Hl as [Hl1 Hl2].
    apply Nat.eqb_eq in Hl1. apply Nat.eqb_eq in Hl2. subst l1 l2.
    destruct (unify_co f D T A n) as [[[s1 cs] n1]|] eqn:E1; [ | discriminate H ].
    destruct (tie_obj f D rest (apR s1 R') (apR s1 Rsl') n1) as [[[s2 n2] rest']|] eqn:E2; [ | discriminate H ].
    inversion H; subst; clear H.
    inversion Hft as [ | D0 G0 l0 e0 T0 fs0 R0 Hty0 Hrest0 | D0 G0 l0 e0 T0 fs0 R0 Hty0 Hrest0 ]; subst.
    destruct (EvR_ext_inv _ _ _ HR) as [HT HR'].
    destruct (EvR_ext_inv _ _ _ HRsl) as [HA HRsl'].
    destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E1 HT HA) as (Hs1 & Hch & Hk1 & Hl1).
    pose proof (Good_unify D n s1 n1 Hs1 Hk1 Hl1 HD) as Gd1.
    pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
    pose proof (DOk_mono D n n1 HD Hl1) as HD1.
    destruct (IH _ _ _ _ _ _ E2 (apC s1 G) HG1 HD1 (EvR_ap _ _ Hs1 HR') (EvR_ap _ _ Hs1 HRsl')
                (fields_ap_G _ _ _ _ _ _ _ _ Gd1 HG Hrest0) (proj2 Hlc))
      as (Gd2 & Hty2 & Her2 & Hlc2 & Hmk2 & Hmr2).
    pose proof Gd2 as (_ & Hs2 & _).
    refine (conj (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) _).
    rewrite <- apC_comp, <- apR_comp, !apR_Ext, <- !apT_comp.
    refine (conj _ (conj _ (conj _ (conj _ _)))).
    + eapply FT_cons; [ | exact Hty2 ].
      apply (typing_ap_G _ _ _ _ _ _ _ _ Gd2 HG1).
      eapply coerce_typing; [ exact Hch | ].
      apply (typing_ap_G _ _ _ _ _ _ _ _ Gd1 HG). exact Hty0.
    + cbn [erase_fields]. rewrite erase_coerce, Her2. reflexivity.
    + cbn [lcef]. split; [ apply lce_coerce; exact (proj1 Hlc) | exact Hlc2 ].
    + cbn [marks]. rewrite Hmk2. reflexivity.
    + constructor. rewrite !apR_comp in Hmr2. rewrite apR_comp. exact Hmr2.
  - destruct (Nat.eqb l l1 && Nat.eqb l l2) eqn:Hl; [ | discriminate H ].
    apply Bool.andb_true_iff in Hl. destruct Hl as [Hl1 Hl2].
    apply Nat.eqb_eq in Hl1. apply Nat.eqb_eq in Hl2. subst l1 l2.
    destruct (unify_co f D T A n) as [[[s1 cs] n1]|] eqn:E1; [ | discriminate H ].
    destruct (tie_obj f D rest (apR s1 R') (apR s1 Rsl') n1) as [[[s2 n2] rest']|] eqn:E2; [ | discriminate H ].
    inversion H; subst; clear H.
    inversion Hft as [ | D0 G0 l0 e0 T0 fs0 R0 Hty0 Hrest0 | D0 G0 l0 e0 T0 fs0 R0 Hty0 Hrest0 ]; subst.
    destruct (EvR_ext_inv _ _ _ HR) as [HT HR'].
    destruct (EvR_ext_inv _ _ _ HRsl) as [HA HRsl'].
    destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E1 HT HA) as (Hs1 & Hch & Hk1 & Hl1).
    pose proof (Good_unify D n s1 n1 Hs1 Hk1 Hl1 HD) as Gd1.
    pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
    pose proof (DOk_mono D n n1 HD Hl1) as HD1.
    destruct (IH _ _ _ _ _ _ E2 (apC s1 G) HG1 HD1 (EvR_ap _ _ Hs1 HR') (EvR_ap _ _ Hs1 HRsl')
                (fields_ap_G _ _ _ _ _ _ _ _ Gd1 HG Hrest0) (proj2 Hlc))
      as (Gd2 & Hty2 & Her2 & Hlc2 & Hmk2 & Hmr2).
    pose proof Gd2 as (_ & Hs2 & _).
    refine (conj (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) _).
    assert (Hu : unroll_eq (length cs) (apT s2 (apT s1 A)) (apT s2 (apT s1 T))).
    { exact (unroll_ap (sT s2) (sR s2) _ _ _ (OkS_lc s2 Hs2)
               (unroll_sym _ _ _ (chain_unroll_eq _ _ _ Hch))). }
    rewrite <- apC_comp, <- apR_comp, !apR_Ext, <- !apT_comp.
    refine (conj _ (conj _ (conj _ (conj _ _)))).
    + eapply FT_meth; [ | exact Hty2 ].
      apply (typing_ap_G _ _ _ _ _ _ _ _ Gd2 HG1).
      eapply coerce_typing; [ exact Hch | ].
      apply (typing_ap_G _ _ _ _ _ _ _ _ Gd1 HG). exact Hty0.
    + cbn [erase_fields]. rewrite erase_coerce, Her2. reflexivity.
    + cbn [lcef]. split; [ apply lce_coerce; exact (proj1 Hlc) | exact Hlc2 ].
    + cbn [marks]. rewrite Hmk2. reflexivity.
    + eapply MRl_meth; [ exact Hu | ]. rewrite !apR_comp in Hmr2. rewrite apR_comp. exact Hmr2.
Qed.

(* ---- a recursive group's members against their slots ---- *)

(* [e'] is [e] at the slot type [A] it met: the same term when the types are
   equal, and for a function the head coercions [cs] on its result, written
   under its lambda. *)
Inductive mem_co : exp -> exp -> typ -> typ -> Prop :=
 | mc_same : forall e T A, teq T A -> mem_co e e T A
 | mc_abs : forall b X Y X' Y' cs,
     teq X X' -> chain cs Y Y' ->
     mem_co (e_abs b) (e_abs (coerce cs b)) (typ_Arrow X Y) (typ_Arrow X' Y').

Inductive pw_co : fields -> row -> row -> fields -> Prop :=
 | pc_nil : pw_co fs_nil row_Empty row_Empty fs_nil
 | pc_cons : forall l e e' T A fs R R' fs',
     mem_co e e' T A -> pw_co fs R R' fs' ->
     pw_co (fs_cons l e fs) (row_Ext l T R) (row_Ext l A R') (fs_cons l e' fs').

Lemma open_coerce : forall cs e k u,
  open_exp_wrt_exp_rec k u (coerce cs e) = coerce cs (open_exp_wrt_exp_rec k u e).
Proof.
  induction cs as [|d cs IH]; intros e k u; cbn [coerce]; [ reflexivity | ].
  rewrite IH. destruct d; reflexivity.
Qed.

Lemma mem_co_typing : forall D G e e' T A,
  mem_co e e' T A -> typing D G e T -> typing D G e' A.
Proof.
  intros D G e e' T A H Hty. destruct H as [e T A Ht | b X Y X' Y' cs Hx Hc].
  - eapply T_Conv; eassumption.
  - destruct (abs_inv _ _ _ _ Hty) as (L & T1 & T2 & Hbody & Hteq).
    destruct (teq_Arrow_inv _ _ _ Hteq) as (A1 & B1 & Heq & Ha & Hb).
    injection Heq as <- <-.
    eapply T_Conv; [ | apply teq_arrow; [ exact Hx | apply teq_refl ] ].
    eapply T_Conv; [ | apply teq_arrow; [ exact Ha | apply teq_refl ] ].
    apply (T_Abs L). intros x Hx0.
    unfold open_exp_wrt_exp. rewrite open_coerce.
    eapply coerce_typing; [ | exact (Hbody x Hx0) ].
    eapply ch_conv; [ exact Hb | exact Hc ].
Qed.

Lemma pw_co_typing : forall D G fs R R' fs',
  field_typing D G fs R -> pw_co fs R R' fs' -> field_typing D G fs' R'.
Proof.
  intros D G fs R R' fs' Hf Hp. revert Hf.
  induction Hp as [|l e e' T A fs0 R0 R0' fs0' Hm Hp IH]; intros Hf.
  - exact Hf.
  - inversion Hf; subst. eapply FT_cons; [ eapply mem_co_typing; eassumption | apply IH; assumption ].
Qed.

Lemma mem_co_ap : forall s e e' T A, OkS s ->
  mem_co e e' T A -> mem_co e e' (apT s T) (apT s A).
Proof.
  intros s e e' T A Hs H. destruct H as [e T A Ht | b X Y X' Y' cs Hx Hc].
  - apply mc_same. apply teq_apT. exact Ht.
  - change (mem_co (e_abs b) (e_abs (coerce cs b)) (typ_Arrow (apT s X) (apT s Y)) (typ_Arrow (apT s X') (apT s Y'))).
    apply mc_abs; [ apply teq_apT; exact Hx | apply chain_apT; assumption ].
Qed.

Lemma unify_mem_sound : forall f D e T A n s n' e', rtriv D ->
  unify_mem f D e T A n = Some (s, n', e') -> EvT T -> EvT A ->
  OkS s /\ mem_co e e' (apT s T) (apT s A) /\ kres D D (sT s) /\ n <= n' /\
  erase e' = erase e /\ (lce 0 e -> lce 0 e') /\ (forall b, e = e_abs b -> exists b', e' = e_abs b').
Proof.
  intros f D e T A n s n' e' Hrt H HT HA. unfold unify_mem in H.
  destruct (unify_t f D T A n) as [[s0 n0]|] eqn:Et.
  - inversion H; subst; clear H.
    destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ ltac:(solve_rtriv) Et HT HA) as (Hs & Ht & Hk & Hl).
    refine (conj Hs (conj (mc_same _ _ _ Ht) (conj Hk (conj Hl (conj eq_refl (conj (fun h => h) _)))))).
    intros b ->. eexists; reflexivity.
  - destruct e as [ | | | | | | b | | | | | | | | | | | | | | | | ]; try discriminate H.
    destruct T as [ | | | | | X Y | | | | | ]; try discriminate H.
    destruct A as [ | | | | | X' Y' | | | | | ]; try discriminate H.
    destruct (unify_t f D X X' n) as [[s1 n1]|] eqn:E1; [ | discriminate H ].
    destruct (unify_co f D (apT s1 Y) (apT s1 Y') n1) as [[[s2 cs] n2]|] eqn:E2; [ | discriminate H ].
    inversion H; subst; clear H.
    destruct (EvT_arrow_inv _ _ HT) as [HX HY]. destruct (EvT_arrow_inv _ _ HA) as [HX' HY'].
    destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ ltac:(solve_rtriv) E1 HX HX') as (Hs1 & Hx & Hk1 & Hl1).
    destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E2 (EvT_ap _ _ Hs1 HY) (EvT_ap _ _ Hs1 HY'))
      as (Hs2 & Hc & Hk2 & Hl2).
    refine (conj (OkS_comp _ _ Hs2 Hs1) (conj _ (conj (kres_scomp D D D s1 s2 ltac:(solve_rtriv) Hk1 Hk2) (conj _ (conj _ (conj _ _)))))).
    + change (mem_co (e_abs b) (e_abs (coerce cs b))
                (typ_Arrow (apT (scomp s2 s1) X) (apT (scomp s2 s1) Y))
                (typ_Arrow (apT (scomp s2 s1) X') (apT (scomp s2 s1) Y'))).
      rewrite <- !apT_comp. apply mc_abs; [ apply teq_apT; exact Hx | exact Hc ].
    + lia.
    + cbn [erase]. rewrite erase_coerce. reflexivity.
    + cbn [lce]. apply lce_coerce.
    + intros b0 Hb. eexists; reflexivity.
Qed.

Lemma pw_co_ap : forall s fs R R' fs', OkS s ->
  pw_co fs R R' fs' -> pw_co fs (apR s R) (apR s R') fs'.
Proof.
  intros s fs R R' fs' Hs H. induction H.
  - change (apR s row_Empty) with row_Empty. constructor.
  - rewrite !apR_Ext. constructor; [ apply mem_co_ap; assumption | assumption ].
Qed.

Lemma unify_grp_sound : forall f D fs R1 R2 n s n' fs2, rtriv D ->
  unify_grp f D fs R1 R2 n = Some (s, n', fs2) -> EvR R1 -> EvR R2 ->
  OkS s /\ pw_co fs (apR s R1) (apR s R2) fs2 /\ kres D D (sT s) /\ n <= n' /\
  erase_fields fs2 = erase_fields fs /\ (lcef 0 fs -> lcef 0 fs2) /\ (fn_group fs -> fn_group fs2).
Proof.
  induction f as [|f IH]; intros D fs R1 R2 n s n' fs2 Hrt H H1 H2; [ discriminate | ].
  cbn [unify_grp] in H.
  destruct fs as [|l e rest|l e rest]; destruct R1 as [|r|l1 T R1'|lm Pm Tm Rm];
    destruct R2 as [|r2|l2 A R2'|lm2 Pm2 Tm2 Rm2]; try discriminate H.
  - inversion H; subst; clear H.
    refine (conj OkS_id (conj _ (conj (kres_id D) (conj (le_n _) (conj eq_refl (conj (fun h => h) (fun h => h))))))).
    rewrite apR_id. constructor.
  - destruct (Nat.eqb l l1 && Nat.eqb l l2) eqn:Hl; [ | discriminate H ].
    apply Bool.andb_true_iff in Hl. destruct Hl as [Hl1 Hl2].
    apply Nat.eqb_eq in Hl1. apply Nat.eqb_eq in Hl2. subst l1 l2.
    destruct (unify_mem f D e T A n) as [[[s1 n1] e']|] eqn:E1; [ | discriminate H ].
    destruct (unify_grp f D rest (apR s1 R1') (apR s1 R2') n1) as [[[s2 n2] rest']|] eqn:E2; [ | discriminate H ].
    inversion H; subst; clear H.
    destruct (EvR_ext_inv _ _ _ H1) as [HT HR1]. destruct (EvR_ext_inv _ _ _ H2) as [HA HR2].
    destruct (unify_mem_sound _ _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E1 HT HA) as (Hs1 & Hm & Hk1 & Hl1 & Her1 & Hlc1 & Hab1).
    destruct (IH _ _ _ _ _ _ _ _ Hrt E2 (EvR_ap s1 _ Hs1 HR1) (EvR_ap s1 _ Hs1 HR2))
      as (Hs2 & Hp & Hk2 & Hl2 & Her2 & Hlc2 & Hab2).
    refine (conj (OkS_comp _ _ Hs2 Hs1) (conj _ (conj (kres_scomp D D D s1 s2 ltac:(solve_rtriv) Hk1 Hk2) (conj _ (conj _ (conj _ _)))))).
    + rewrite !apR_Ext. rewrite <- !apT_comp, <- !apR_comp.
      constructor; [ apply mem_co_ap; assumption | exact Hp ].
    + lia.
    + cbn [erase_fields]. rewrite Her1, Her2. reflexivity.
    + cbn [lcef]. intros [Ha Hb]. split; [ apply Hlc1; exact Ha | apply Hlc2; exact Hb ].
    + intros Hfg. inversion Hfg; subst.
      destruct (Hab1 _ eq_refl) as [b' ->]. constructor. apply Hab2. assumption.
Qed.


Lemma EvR_obj_row : forall fs n m, EvR (obj_row fs n (row_Var (ea m))).
Proof.
  induction fs as [|l e rest IH|l e rest IH]; intros n m; simpl.
  - apply EvR_var, ev_ea.
  - apply EvR_ext; [ apply EvT_var, ev_ea | apply IH ].
  - apply EvR_ext; [ apply EvT_var, ev_ea | apply IH ].
Qed.

Lemma apT_Record : forall s R, apT s (typ_Record R) = typ_Record (apR s R).
Proof. reflexivity. Qed.

Lemma obj_row_ap : forall s fs n tl,
  apR s (obj_row fs n tl) = row_tail_with (apR s (group_row fs n)) (apR s tl).
Proof.
  intros s. induction fs as [|l e rest IH|l e rest IH]; intros n tl; cbn [obj_row group_row].
  - reflexivity.
  - rewrite !apR_Ext. cbn [row_tail_with]. rewrite IH. reflexivity.
  - rewrite !apR_Ext. cbn [row_tail_with]. rewrite IH. reflexivity.
Qed.

Theorem infer_sound : forall f,
  (forall D G e n s D' T n' e', infer f D G e n = Some (s, D', T, n', e') -> WfCtx G -> DOk D n ->
     Good D n s D' n' /\ EvT T /\
     (typing D' (apC s G) e' T /\ erase e' = e /\ lce 0 e')) /\
  (forall D G fs n s D' R n' fs', infer_fields f D G fs n = Some (s, D', R, n', fs') -> WfCtx G -> DOk D n ->
     Good D n s D' n' /\ EvR R /\
     (field_typing D' (apC s G) fs' R /\ erase_fields fs' = fs /\ lcef 0 fs')) /\
  (forall D G w Ts x res ars n s D' T n' ars',
     infer_arms f D G w Ts x res ars n = Some (s, D', T, n', ars') ->
     WfCtx G -> DOk D n -> Forall EvT Ts -> EvT res ->
     x `notin` dom G `union` fv_arms ars ->
     Good D n s D' n' /\ EvT T /\ T = apT s res /\
     (arms_typ (dom G `union` {{x}}) D' (apC s G) w (map (apT s) Ts) ars' T /\
      erase_arms ars' = ars /\ lcea 0 ars')) /\
  (forall D G p Tp fs n s D' R n' fs',
     infer_obj f D G p Tp fs n = Some (s, D', R, n', fs') ->
     WfCtx G -> DOk D n -> EvT Tp -> p `notin` dom G `union` fv_fields fs ->
     Good D n s D' n' /\ EvR R /\
     (field_typing D' (apC s G) fs' R /\ erase_fields fs' = fs /\ lcef 0 fs' /\
      marks fs' = marks fs /\ meth_ty (apT s Tp) fs' R)).
Proof.
  induction f as [|f IH]; [ refine (conj _ (conj _ (conj _ _))); intros; discriminate | ].
  destruct IH as [IHe [IHf [IHa IHo]]]. refine (conj _ (conj _ (conj _ _))).
  - intros D G e n s D' T n' e' H HG HD. cbn [infer] in H.
    destruct e as [i | x | k | d | | | b | e1 e2 | e1 e2 | fl el | fs | e1 l | | q | c0 a0 b0 | a1 o a2 | a3 | w1 tg1 a6 | w2 a7 ars2 | a8 l8 a9 | a10 l10 | a4 | a5];
      try discriminate H.
    + (* variable *)
      destruct (lookup x G) as [sc|] eqn:Hl; [|discriminate].
      destruct (instantiate D sc n) as [[T0 D1] n1] eqn:Hi.
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      pose proof (lookup_binds _ _ _ Hl) as Hb.
      destruct (instantiate_sound _ _ _ _ _ _ Hi ((proj2 HG) _ _ Hb) HD) as (Hinst & Hev & HD1 & Hk).
      assert (Hle : n <= n1) by (unfold instantiate in Hi; inversion Hi; lia).
      split; [ exact (conj HD (conj OkS_id (conj HD1 (conj Hle (conj Hk Hk))))) | ].
      split; [exact Hev|].
      rewrite apC_sid. refine (conj _ (conj eq_refl I)).
      eapply T_Var; [ exact (proj1 HG) | exact Hb | exact Hinst ].
    + (* numeral *)
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      split; [ apply Good_upd; exact HD | ].
      split; [apply EvT_var, ev_ea|].
      refine (conj _ (conj eq_refl I)).
      apply T_Num; [ apply uniq_apC; exact (proj1 HG) | ].
      cbn [sat]. rewrite upd_same. apply finer_refl.
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_Float|].
      refine (conj _ (conj eq_refl I)). apply T_Dec. apply uniq_apC. exact (proj1 HG).
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_Bool|].
      refine (conj _ (conj eq_refl I)). apply T_True. apply uniq_apC. exact (proj1 HG).
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_Bool|].
      refine (conj _ (conj eq_refl I)). apply T_False. apply uniq_apC. exact (proj1 HG).
    + (* abstraction *)
      destruct (infer f D ((fresh_var G b ~ sch_mono (typ_Var (ea n))) ++ G)
                  (open_exp_wrt_exp b (e_fvar_f (fresh_var G b))) (S n))
        as [[[[[s0 D1] T0] n0] us0]|] eqn:Ei; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      assert (Hbeta : EvT (typ_Var (ea n))) by (apply EvT_var, ev_ea).
      assert (Hwf : WfCtx ((fresh_var G b ~ sch_mono (typ_Var (ea n))) ++ G))
        by (apply WfCtx_cons; [ exact HG | apply fresh_var_notin_dom | apply WfSch_mono; exact Hbeta ]).
      destruct (IHe _ _ _ _ _ _ _ _ _ Ei Hwf (DOk_mono D n (S n) HD (le_S _ _ (le_n n)))) as (Gd0 & HT0 & Hty & Her_Hty & Hlc_Hty).
      pose proof (Good_pre D n (S n) s0 D1 n0 (le_S _ _ (le_n n)) HD Gd0) as Gd.
      destruct Gd0 as (_ & Hs0 & _).
      destruct (bind_ok _ b _ Her_Hty Hlc_Hty (fresh_var_notin_fv G b)) as [Her' Hlc'].
      split; [exact Gd|]. split.
      { apply EvT_arrow; [ apply EvT_ap; auto | exact HT0 ]. }
      refine (conj _ (conj _ Hlc')).
      2: { cbn [erase]. rewrite Her'. reflexivity. }
      rewrite apC_app, apC_single in Hty.
      apply T_Abs with (L := dom G `union` {{fresh_var G b}}).
      intros y Hy.
      assert (Hdom : y `notin` dom ((fresh_var G b ~ apS s0 (sch_mono (typ_Var (ea n)))) ++ apC s0 G))
        by (simpl; rewrite dom_apC; fsetdec).
      exact (typing_open_cl D1 (apC s0 G) _ y _ _ _ Hty Hlc_Hty Hdom).
    + (* application *)
      destruct (infer f D G e1 n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (infer f D1 (apC s1 G) e2 n1) as [[[[[s2 D2] T2] n2] us2]|] eqn:E2; [|discriminate].
      destruct (unify_co f D2 (apT s2 T1) (typ_Arrow T2 (typ_Var (ea n2))) (S n2))
        as [[[s3 cs3] n3]|] eqn:E3; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHe _ _ _ _ _ _ _ _ _ E2 HG1 HD1) as (Gd2 & HT2 & Hty2 & Her_Hty2 & Hlc_Hty2).
      pose proof Gd2 as (_ & Hs2 & HD2 & _).
      pose proof (WfCtx_ap s2 _ Hs2 HG1) as HG2.
      assert (Hbeta : EvT (typ_Var (ea n2))) by (apply EvT_var, ev_ea).
      destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E3 (EvT_ap s2 T1 Hs2 HT1)
                  (EvT_arrow _ _ HT2 Hbeta)) as (Hs3 & Hch & Hk3 & Hl3).
      pose proof (Good_unify D2 n2 s3 n3 Hs3 Hk3 ltac:(lia) HD2) as Gd3.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3) | ].
      split; [ apply EvT_ap; auto | ].
      refine (conj _ (conj _ _)).
      2: { cbn [erase]. rewrite erase_coerce, Her_Hty1, Her_Hty2. reflexivity. }
      2: { cbn [lce]. split; [ apply lce_coerce; exact Hlc_Hty1 | exact Hlc_Hty2 ]. }
      rewrite <- !apC_comp.
      eapply T_App.
      * eapply coerce_typing; [ exact Hch | ].
        apply (typing_ap_G D2 n2 s3 D2 n3 _ _ _ Gd3 HG2).
        apply (typing_ap_G D1 n1 s2 D2 n2 _ _ _ Gd2 HG1). exact Hty1.
      * apply (typing_ap_G D2 n2 s3 D2 n3 _ _ _ Gd3 HG2). exact Hty2.
    + (* let *)
      destruct (infer f D G e1 n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (is_gen_value us1) eqn:Hgv.
      2: { (* a computed value: monomorphic *)
      destruct (infer f D1 ((fresh_var (apC s1 G) e2 ~ sch_mono T1) ++ apC s1 G)
                  (open_exp_wrt_exp e2 (e_fvar_f (fresh_var (apC s1 G) e2))) n1)
        as [[[[[s2 D2] T2] n2] us2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      assert (Hwf : WfCtx ((fresh_var (apC s1 G) e2 ~ sch_mono T1) ++ apC s1 G))
        by (apply WfCtx_cons; [ exact HG1 | apply fresh_var_notin_dom | apply WfSch_mono; exact HT1 ]).
      destruct (IHe _ _ _ _ _ _ _ _ _ E2 Hwf HD1) as (Gd2 & HT2 & Hty2 & Her_Hty2 & Hlc_Hty2).
      destruct (bind_ok _ e2 _ Her_Hty2 Hlc_Hty2 (fresh_var_notin_fv (apC s1 G) e2)) as [Her' Hlc'].
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ]. split; [ exact HT2 | ].
      refine (conj _ (conj _ (conj Hlc_Hty1 Hlc'))).
      2: { cbn [erase]. rewrite Her_Hty1, Her'. reflexivity. }
      rewrite <- apC_comp.
      rewrite apC_app, apC_single in Hty2.
      apply T_LetMono with (L := dom G `union` {{fresh_var (apC s1 G) e2}}) (T1 := apT s2 T1).
      * apply (typing_ap_G D1 n1 s2 D2 n2 _ _ _ Gd2 HG1). exact Hty1.
      * intros y Hy.
        destruct Gd2 as (_ & Hs2 & _).
        assert (Hdom : y `notin` dom ((fresh_var (apC s1 G) e2 ~ apS s2 (sch_mono T1)) ++ apC s2 (apC s1 G)))
          by (simpl; rewrite dom_apC, dom_apC; fsetdec).
        exact (typing_open_cl D2 (apC s2 (apC s1 G)) _ y _ _ _ Hty2 Hlc_Hty2 Hdom). }
      destruct (infer f D1
                  ((fresh_var (apC s1 G) e2 ~ gen_ren D1 (pin_ctx (let_pin D1 e1 T1) (apC s1 G)) T1) ++ apC s1 G)
                  (open_exp_wrt_exp e2 (e_fvar_f (fresh_var (apC s1 G) e2))) n1)
        as [[[[[s2 D2] T2] n2] us2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      set (Tm := let_pin D1 e1 T1) in *.
      set (Pz := (fresh_var (apC s1 G) e2 ~ sch_mono Tm) ++ apC s1 G).
      assert (HTm : EvT Tm) by (apply let_pin_EvT; exact HT1).
      assert (HPz : WfCtx Pz)
        by (apply WfCtx_cons; [ exact HG1 | apply fresh_var_notin_dom | apply WfSch_mono; exact HTm ]).
      assert (Hsc : gen_ren D1 (pin_ctx Tm (apC s1 G)) T1 = gen_ren D1 Pz T1) by reflexivity.
      rewrite Hsc in E2.
      pose proof (gen_ren_wf D1 Pz T1 HT1) as Hwsc.
      assert (Hwf : WfCtx ((fresh_var (apC s1 G) e2 ~ gen_ren D1 Pz T1) ++ apC s1 G))
        by (apply WfCtx_cons; [ exact HG1 | apply fresh_var_notin_dom | exact Hwsc ]).
      destruct (IHe _ _ _ _ _ _ _ _ _ E2 Hwf HD1) as (Gd2 & HT2 & Hty2 & Her_Hty2 & Hlc_Hty2).
      pose proof Gd2 as (_ & Hs2 & HD2 & Hl2 & Hi2 & Hk2).
      destruct (bind_ok _ e2 _ Her_Hty2 Hlc_Hty2 (fresh_var_notin_fv (apC s1 G) e2)) as [Her' Hlc'].
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ]. split; [ exact HT2 | ].
      refine (conj _ (conj _ (conj Hlc_Hty1 Hlc'))).
      2: { cbn [erase]. rewrite Her_Hty1, Her'. reflexivity. }
      rewrite <- apC_comp.
      rewrite apC_app, apC_single in Hty2.
      pose proof (gen_ren_equiv D1 Pz T1 s2 Hs2 HPz HT1) as Hequiv.
      pose proof Hequiv as (Htq & _).
      assert (Hpt : ftv_ctx (apC s2 Pz) [=] ftv_ctx (pin_ctx (apT s2 Tm) (apC s2 (apC s1 G)))).
      { unfold Pz, pin_ctx. simpl. unfold ftv_sch. simpl. fsetdec. }
      assert (Hpr : frv_ctx (apC s2 Pz) [=] frv_ctx (pin_ctx (apT s2 Tm) (apC s2 (apC s1 G)))).
      { unfold Pz, pin_ctx. simpl. unfold frv_sch. simpl. fsetdec. }
      apply T_Let with (L := dom G `union` {{fresh_var (apC s1 G) e2}})
                       (T1 := apT s2 (s_body (gen_ren D1 Pz T1)))
                       (k := s_sk (gen_ren D1 Pz T1)) (rk := s_rk (gen_ren D1 Pz T1)) (Tm := apT s2 Tm).
      * exact Hgv.
      * pose proof (typing_gen_ren_on D1 Pz T1 (apC s1 G) n1 us1
                      ltac:(unfold Pz; simpl; fsetdec) ltac:(unfold Pz; simpl; fsetdec)
                      HD1 Hty1) as Hg.
        destruct (DOk_supp D1 n1 HD1) as [S1 HS1].
        destruct (DOk_supp D2 n2 HD2) as [S2 HS2].
        pose proof (typing_ap (ext D1 (s_tq (gen_ren D1 Pz T1)) (s_sk (gen_ren D1 Pz T1)))
                      (ext D2 (s_tq (gen_ren D1 Pz T1)) (s_sk (gen_ren D1 Pz T1)))
                      s2 (apC s1 G) us1 (s_body (gen_ren D1 Pz T1)) Hs2 HG1
                      (ex_intro _ _ (supp_ok_ext_set _ _ _ _ HS1))
                      (ex_intro _ _ (supp_ok_ext_set _ _ _ _ HS2))
                      (kres_ext_lift D1 D2 s2 _ _ Hs2 Hk2 (gen_ren_od_t D1 Pz T1))
                      (rkres_triv _ _ _ (DOk_rtriv _ _ HD1)) Hg) as Hl.
        eapply typing_pw; [ exact Hl | ].
        eapply denv_eq_trans.
        -- apply ext_set_eq_d.
           cbn [apS s_tq gen s_body s_sk] in Htq. rewrite Htq. rewrite Hpt. reflexivity.
        -- apply denv_eq_extr_triv; [ exact (DOk_rtriv _ _ HD2) | intros r; reflexivity ].
      * intros y Hy.
        assert (Hdom : y `notin` dom ((fresh_var (apC s1 G) e2 ~ apS s2 (gen_ren D1 Pz T1)) ++ apC s2 (apC s1 G)))
          by (simpl; rewrite dom_apC, dom_apC; fsetdec).
        pose proof (typing_open_cl D2 (apC s2 (apC s1 G)) (fresh_var (apC s1 G) e2) y
                      (apS s2 (gen_ren D1 Pz T1)) us2 T2 Hty2 Hlc_Hty2 Hdom) as Hren.
        eapply typing_sch_equiv_ctx; [ exact Hren | ].
        apply ctx_equiv_cons; [ | apply ctx_equiv_refl ].
        eapply sch_equiv_trans; [ exact Hequiv | ].
        unfold sch_equiv, gen. cbn [s_tq s_rq s_body s_sk s_rk].
        split; [ | split; [ | split; [ reflexivity | split; [ intros a Ha; reflexivity | intros r Hr; reflexivity ] ] ] ]; fsetdec.
    + (* recursive group *)
      destruct (is_fn_group fl) eqn:Hfg; [|discriminate].
      set (p := fresh_var G (e_rec fl)) in *.
      set (R0 := group_row fl n) in *.
      destruct (infer_fields f D ((p ~ sch_mono (typ_Record R0)) ++ G)
                  (open_fields_wrt_exp fl (e_fvar_f p)) (n + nfields fl))
        as [[[[[s1 D1] R1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (unify_grp f D1 us1 R1 (apR s1 R0) n1) as [[[s2 n2] us2]|] eqn:E2; [|discriminate].
      set (G1 := apC (scomp s2 s1) G) in *.
      set (Rf := apR (scomp s2 s1) R0) in *.
      set (q := fresh_var G1 el) in *.
      destruct (infer f D1 ((q ~ gen_ren D1 G1 (typ_Record Rf)) ++ G1)
                  (open_exp_wrt_exp el (e_fvar_f q)) n2)
        as [[[[[s3 D3] T3] n3] us3]|] eqn:E3; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      assert (HR0 : EvR R0) by apply EvR_group_row.
      assert (Hwf0 : WfCtx ((p ~ sch_mono (typ_Record R0)) ++ G))
        by (apply WfCtx_cons; [ exact HG | apply fresh_var_notin_dom | apply WfSch_mono, EvT_Record; exact HR0 ]).
      assert (Hnn : n <= n + nfields fl) by lia.
      destruct (IHf _ _ _ _ _ _ _ _ _ E1 Hwf0 (DOk_mono D n _ HD Hnn)) as (Gd1' & HR1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof (Good_pre D n _ s1 D1 n1 Hnn HD Gd1') as Gd1.
      pose proof Gd1 as (_ & Hs1 & HD1 & Hl1 & Hi1 & Hk1).
      rewrite apC_app, apC_single in Hty1.
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      pose proof (EvR_ap s1 _ Hs1 HR0) as HR0'.
      destruct (unify_grp_sound f D1 _ _ _ _ _ _ _ ltac:(solve_rtriv) E2 HR1 HR0') as (Hs2 & Hpw & Hk2 & Hl2 & Her_u & Hlc_u & Hfg_u).
      pose proof (Good_unify D1 n1 s2 n2 Hs2 Hk2 Hl2 HD1) as Gd2.
      pose proof (DOk_supp D1 n1 HD1) as HS1.
      pose proof (fields_ap D1 D1 s2 (apC s1 G) p _ _ _ Hs2 HG1 HS1 HS1 Hk2
                    (rkres_triv _ _ _ (DOk_rtriv _ _ HD1)) Hty1) as Hty2.
      pose proof (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) as Gd21.
      assert (Hs21 : OkS (scomp s2 s1)) by (destruct Gd21 as (_ & H21 & _); exact H21).
      assert (HRf : EvR Rf) by (apply EvR_ap; assumption).
      assert (HG21 : WfCtx G1) by (apply WfCtx_ap; assumption).
      assert (Hty3 : field_typing D1 ((p ~ sch_mono (typ_Record Rf)) ++ G1) us2 Rf).
      { unfold Rf, G1. rewrite <- apR_comp. rewrite <- apC_comp.
        refine (pw_co_typing _ _ _ _ _ _ _ Hpw).
        change (typ_Record (apR s2 (apR s1 R0))) with (apT s2 (apT s1 (typ_Record R0))) in Hty2.
        exact Hty2. }
      pose proof (gen_ren_wf D1 G1 (typ_Record Rf) (proj2 (EvT_Record _) HRf)) as Hwsc.
      assert (Hwf1 : WfCtx ((q ~ gen_ren D1 G1 (typ_Record Rf)) ++ G1))
        by (apply WfCtx_cons; [ exact HG21 | apply fresh_var_notin_dom | exact Hwsc ]).
      destruct (IHe _ _ _ _ _ _ _ _ _ E3 Hwf1 (DOk_mono D1 n1 n2 HD1 Hl2)) as (Gd3' & HT3 & Hty4 & Her_Hty4 & Hlc_Hty4).
      pose proof Gd3' as Gd3.
      pose proof Gd3 as (_ & Hs3 & HD3 & Hl3 & Hi3 & Hk3).
      pose proof (Good_comp _ _ _ _ _ _ _ _ Gd21 Gd3) as Gdf.
      destruct (bind_ok_fields p fl _ (eq_trans Her_u Her_Hty1) (Hlc_u Hlc_Hty1) (fresh_var_notin_fv G (e_rec fl))) as [Herf Hlcf].
      destruct (bind_ok q el _ Her_Hty4 Hlc_Hty4 (fresh_var_notin_fv G1 el)) as [Herb Hlcb].
      split; [ exact Gdf | ]. split; [ exact HT3 | ].
      refine (conj _ (conj _ (conj Hlcf Hlcb))).
      2: { cbn [erase]. rewrite Herf, Herb. reflexivity. }
      rewrite <- apC_comp. fold G1.
      rewrite apC_app, apC_single in Hty4.
      pose proof (gen_ren_equiv D1 G1 (typ_Record Rf) s3 Hs3 HG21 (proj2 (EvT_Record _) HRf)) as Hequiv.
      pose proof Hequiv as (Htq & _).
      pose proof (fields_gen_ren D1 n2 G1 p Rf _ (DOk_mono D1 n1 n2 HD1 Hl2) Hty3) as Hty5.
      destruct (DOk_supp D1 n2 (DOk_mono D1 n1 n2 HD1 Hl2)) as [S1' HS1'].
      destruct (DOk_supp D3 n3 HD3) as [S3 HS3].
      pose proof (fields_ap (ext D1 (s_tq (gen_ren D1 G1 (typ_Record Rf))) (s_sk (gen_ren D1 G1 (typ_Record Rf))))
                    (ext D3 (s_tq (gen_ren D1 G1 (typ_Record Rf))) (s_sk (gen_ren D1 G1 (typ_Record Rf))))
                    s3 G1 p _ _ _ Hs3 HG21
                    (ex_intro _ _ (supp_ok_ext_set _ _ _ _ HS1'))
                    (ex_intro _ _ (supp_ok_ext_set _ _ _ _ HS3))
                    (kres_ext_lift D1 D3 s3 _ _ Hs3 Hk3 (gen_ren_od_t D1 G1 (typ_Record Rf)))
                    (rkres_triv _ _ _ (DOk_rtriv _ _ HD1)) Hty5) as Hty6.
      apply T_Letrec with (L := dom G `union` {{p}} `union` {{q}})
        (R := apR s3 (ap_row (rename_t (gen_vars_t G1 (typ_Record Rf)))
                             (rename_r (gen_vars_r G1 (typ_Record Rf))) Rf))
        (k := s_sk (gen_ren D1 G1 (typ_Record Rf))) (rk := s_rk (gen_ren D1 G1 (typ_Record Rf))).
      * apply fn_group_clf. apply Hfg_u. exact (infer_fields_fn_group _ _ _ _ _ _ _ _ _ _
                                     (is_fn_group_open_rec fl 0 (e_fvar_f p) Hfg) E1).
      * intros y Hy.
        pose proof (fields_open_cl _ (apC s3 G1) p y _ _ _ Hty6 (Hlc_u Hlc_Hty1)
                      ltac:(simpl; rewrite dom_apC; unfold G1; rewrite dom_apC; fsetdec)) as Hf.
        eapply field_typing_pw; [ exact Hf | ].
        eapply denv_eq_trans.
        -- apply ext_set_eq_d. exact Htq.
        -- apply denv_eq_extr_triv; [ exact (DOk_rtriv _ _ HD3) | intros r; reflexivity ].
      * intros y Hy.
        pose proof (typing_open_cl D3 (apC s3 G1) q y
                      (apS s3 (gen_ren D1 G1 (typ_Record Rf))) us3 T3 Hty4 Hlc_Hty4
                      ltac:(simpl; rewrite dom_apC; unfold G1; rewrite dom_apC; fsetdec)) as Hren.
        eapply typing_sch_equiv_ctx; [ exact Hren | ].
        apply ctx_equiv_cons; [ | apply ctx_equiv_refl ].
        exact Hequiv.
    + (* record *)
      destruct (no_meth fs) eqn:Hnm.
      all: try (rewrite Hnm in H).
      * destruct (infer_fields f D G fs n) as [[[[[s0 D1] R0] n0] us0]|] eqn:Ei; [|discriminate].
        inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
        destruct (IHf _ _ _ _ _ _ _ _ _ Ei HG HD) as (Gd0 & HR0 & Hty & Her_Hty & Hlc_Hty).
        split; [exact Gd0|]. split; [ apply EvT_Record; exact HR0 | ].
        refine (conj _ (conj _ Hlc_Hty)).
        2: { cbn [erase]. rewrite Her_Hty. reflexivity. }
        apply T_Record; [ exact Hty | eapply infer_fields_no_meth; exact Ei ].
      * (* methods share one receiver *)
        set (p := fresh_var G (e_rec fs)) in *.
        set (Tp := typ_Record (obj_row fs n (row_Var (ea (n + nfields fs))))) in *.
        destruct (infer_obj f D G p Tp fs (S (n + nfields fs)))
          as [[[[[s1 D1] R1] n1] fs1]|] eqn:Eo; [|discriminate].
        destruct (tie_obj f D1 fs1 R1 (apR s1 (group_row fs n)) n1) as [[[s2 n2] fs2]|] eqn:Et; [|discriminate].
        inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
        assert (HTp : EvT Tp) by (apply EvT_Record; apply EvR_obj_row).
        assert (Hle : n <= S (n + nfields fs)) by lia.
        assert (Hpd : p `notin` dom G) by apply fresh_var_notin_dom.
        assert (Hpf : p `notin` fv_exp (e_rec fs)) by apply fresh_var_notin_fv.
        simpl in Hpf.
        destruct (IHo _ _ _ _ _ _ _ _ _ _ _ Eo HG (DOk_mono D n _ HD Hle) HTp
                    ltac:(fsetdec))
          as (Gd1' & HR1 & Hft1 & Her1 & Hlc1 & Hmk1 & Hmt1).
        pose proof (Good_pre D n _ s1 D1 n1 Hle HD Gd1') as Gd1.
        pose proof Gd1 as (_ & Hs1 & HD1 & _).
        pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
        destruct (tie_obj_sound _ _ _ _ _ _ _ _ _ Et (apC s1 G) HG1 HD1 HR1
                    (EvR_ap _ _ Hs1 (EvR_group_row fs n)) Hft1 Hlc1)
          as (Gd2 & Hft2 & Her2 & Hlc2 & Hmk2 & Hmr2).
        pose proof Gd2 as (_ & Hs2 & _).
        pose proof (OkS_comp _ _ Hs2 Hs1) as Hs21.
        split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
        split; [ apply EvT_Record; apply EvR_ap; [ exact Hs21 | apply EvR_group_row ] | ].
        refine (conj _ (conj _ Hlc2)).
        2: { cbn [erase]. rewrite Her2, Her1. reflexivity. }
        rewrite <- apC_comp, <- apR_comp.
        assert (Hap : apT s2 (apT s1 Tp)
                      = typ_Record (row_tail_with (apR s2 (apR s1 (group_row fs n)))
                                                  (apR s2 (apR s1 (row_Var (ea (n + nfields fs))))))).
        { subst Tp. rewrite apT_comp, apT_Record, obj_row_ap, <- !apR_comp. reflexivity. }
        eapply T_Obj with (Rt := apR s2 (apR s1 (row_Var (ea (n + nfields fs))))).
        { exact Hft2. }
        eapply meths_shared_of.
        { exact Hmr2. }
        { exact (meth_ty_ap s2 _ _ _ Hmt1). }
        { exact Hap. }
        { exact Hmk2. }
    + (* projection *)
      destruct (infer f D G e1 n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (unify_co f D1 T1 (typ_Record (row_Ext l (typ_Var (ea n1)) (row_Var (ea (S n1)))))
                  (n1 + 2)) as [[[s2 cs2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      assert (Hrow : EvT (typ_Record (row_Ext l (typ_Var (ea n1)) (row_Var (ea (S n1)))))).
      { apply EvT_Record, EvR_ext; [ apply EvT_var, ev_ea | apply EvR_var, ev_ea ]. }
      destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E2 HT1 Hrow) as (Hs2 & Hch & Hk2 & Hl2).
      pose proof (Good_unify D1 n1 s2 n2 Hs2 Hk2 ltac:(lia) HD1) as Gd2.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ apply EvT_ap; [exact Hs2 | apply EvT_var, ev_ea] | ].
      refine (conj _ (conj _ _)).
      2: { cbn [erase]. rewrite erase_coerce, Her_Hty1. reflexivity. }
      2: { cbn [lce]. apply lce_coerce. exact Hlc_Hty1. }
      rewrite <- apC_comp.
      eapply T_Proj.
      eapply coerce_typing; [ exact Hch | ].
      apply (typing_ap_G D1 n1 s2 D1 n2 _ _ _ Gd2 HG1). exact Hty1.
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_Unit|].
      refine (conj _ (conj eq_refl I)). apply T_Unit. apply uniq_apC. exact (proj1 HG).
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvT_String|].
      refine (conj _ (conj eq_refl I)). apply T_Str. apply uniq_apC. exact (proj1 HG).
    + (* conditional *)
      destruct (infer f D G c0 n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (unify_co f D1 T1 typ_Bool n1) as [[[s2 cs2] n2]|] eqn:E2; [|discriminate].
      destruct (infer f D1 (apC s2 (apC s1 G)) a0 n2) as [[[[[s3 D3] T2] n3] us3]|] eqn:E3; [|discriminate].
      destruct (infer f D3 (apC s3 (apC s2 (apC s1 G))) b0 n3) as [[[[[s4 D4] T3] n4] us4]|] eqn:E4;
        [|discriminate].
      destruct (unify_co f D4 (apT s4 T2) T3 n4) as [[[s5 cs5] n5]|] eqn:E5; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E2 HT1 EvT_Bool) as (Hs2 & Hch2 & Hk2 & Hl2).
      pose proof (Good_unify D1 n1 s2 n2 Hs2 Hk2 Hl2 HD1) as Gd2.
      pose proof (WfCtx_ap s2 _ Hs2 HG1) as HG2.
      assert (HD2 : DOk D1 n2) by (destruct Gd2 as (_ & _ & H2 & _); exact H2).
      destruct (IHe _ _ _ _ _ _ _ _ _ E3 HG2 HD2) as (Gd3 & HT2 & Hty2 & Her_Hty2 & Hlc_Hty2).
      pose proof Gd3 as (_ & Hs3 & HD3 & _).
      pose proof (WfCtx_ap s3 _ Hs3 HG2) as HG3.
      destruct (IHe _ _ _ _ _ _ _ _ _ E4 HG3 HD3) as (Gd4 & HT3 & Hty3 & Her_Hty3 & Hlc_Hty3).
      pose proof Gd4 as (_ & Hs4 & HD4 & _).
      pose proof (WfCtx_ap s4 _ Hs4 HG3) as HG4.
      destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E5 (EvT_ap s4 T2 Hs4 HT2) HT3)
        as (Hs5 & Hch5 & Hk5 & Hl5).
      pose proof (Good_unify D4 n4 s5 n5 Hs5 Hk5 Hl5 HD4) as Gd5.
      pose proof (WfCtx_ap s5 _ Hs5 HG4) as HG5.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _
                 (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3) Gd4) Gd5) | ].
      split; [ apply EvT_ap; auto | ].
      refine (conj _ (conj _ _)).
      2: { cbn [erase]. rewrite !erase_coerce, Her_Hty1, Her_Hty2, Her_Hty3. reflexivity. }
      2: { cbn [lce]. split; [ apply lce_coerce; exact Hlc_Hty1 | split; [ apply lce_coerce; exact Hlc_Hty2 | exact Hlc_Hty3 ] ]. }
      rewrite <- !apC_comp.
      assert (Hc : typing D1 (apC s2 (apC s1 G)) (coerce cs2 us1) typ_Bool).
      { eapply coerce_typing; [ exact Hch2 | ].
        apply (typing_ap_G D1 n1 s2 D1 n2 _ _ _ Gd2 HG1). exact Hty1. }
      eapply T_If.
      * exact (typing_ap_G D4 n4 s5 D4 n5 _ _ _ Gd5 HG4
                 (typing_ap_G D3 n3 s4 D4 n4 _ _ _ Gd4 HG3
                   (typing_ap_G D1 n2 s3 D3 n3 _ _ _ Gd3 HG2 Hc))).
      * eapply coerce_typing; [ exact Hch5 | ].
        apply (typing_ap_G D4 n4 s5 D4 n5 _ _ _ Gd5 HG4).
        apply (typing_ap_G D3 n3 s4 D4 n4 _ _ _ Gd4 HG3). exact Hty2.
      * apply (typing_ap_G D4 n4 s5 D4 n5 _ _ _ Gd5 HG4). exact Hty3.
    + (* binary operation *)
      destruct (infer f D G a1 n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (infer f D1 (apC s1 G) a2 n1) as [[[[[s2 D2] T2] n2] us2]|] eqn:E2; [|discriminate].
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHe _ _ _ _ _ _ _ _ _ E2 HG1 HD1) as (Gd2 & HT2 & Hty2 & Her_Hty2 & Hlc_Hty2).
      pose proof Gd2 as (_ & Hs2 & HD2 & _).
      pose proof (WfCtx_ap s2 _ Hs2 HG1) as HG2.
      destruct (is_generic_op o) eqn:Hring.
      * (* [+ - * // %] and a comparison: both operands at one variable's type, of the operator's sort *)
        assert (Hko : kind o = k_ring \/ kind o = k_whole \/ kind o = k_cmp)
          by (unfold is_generic_op in Hring; destruct (kind o); [ left; reflexivity | discriminate | right; left; reflexivity | right; right; reflexivity ]).
        set (D2' := upd D2 (ea n2) (generic_sort o)) in *.
        destruct (unify_co f D2' (apT s2 T1) (typ_Var (ea n2)) (S n2)) as [[[s3 cs3] n3]|] eqn:E3; [|discriminate].
        destruct (unify_co f D2' (apT s3 T2) (apT s3 (typ_Var (ea n2))) n3) as [[[s4 cs4] n4]|] eqn:E4; [|discriminate].
        inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
        assert (HN : D2' (ea n2) = generic_sort o) by (unfold D2'; apply upd_same).
        assert (HEc : EvT (typ_Var (ea n2))) by (apply EvT_var, ev_ea).
        pose proof (Good_upd D2 n2 (generic_sort o) HD2) as GdU.
        fold D2' in GdU.
        assert (HD2' : DOk D2' (S n2)) by (destruct GdU as (_ & _ & H2 & _); exact H2).
        destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E3 (EvT_ap s2 T1 Hs2 HT1) HEc)
          as (Hs3 & Hch3 & Hk3 & Hl3).
        pose proof (Good_unify D2' (S n2) s3 n3 Hs3 Hk3 Hl3 HD2') as Gd3.
        pose proof (WfCtx_ap s3 _ Hs3 HG2) as HG3.
        destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E4 (EvT_ap s3 T2 Hs3 HT2)
                    (EvT_ap s3 _ Hs3 HEc)) as (Hs4 & Hch4 & Hk4 & Hl4).
        pose proof (Good_unify D2' n3 s4 n4 Hs4 Hk4 Hl4 (DOk_mono D2' (S n2) n3 HD2' Hl3)) as Gd4.
        split.
        { exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2)
                   (Good_lift _ _ _ _ _ _ _ GdU Gd3)) Gd4). }
        split.
        { unfold bin_res. destruct (kind o);
            first [ apply EvT_Bool | (apply EvT_ap; [ exact Hs4 | apply EvT_ap; [ exact Hs3 | exact HEc ] ]) ]. }
        refine (conj _ (conj _ _)).
        2: { cbn [erase]. rewrite !erase_coerce, Her_Hty1, Her_Hty2. reflexivity. }
        2: { cbn [lce]. split; apply lce_coerce; assumption. }
        rewrite <- !apC_comp.
        assert (Hsat : sat D2' (generic_sort o) (apT s4 (apT s3 (typ_Var (ea n2))))).
        { pose proof (Hk3 (ea n2)) as H3. rewrite HN in H3.
          exact (sat_ap D2' D2' (generic_sort o) _ (sT s4) (sR s4) Hk4 (rkres_triv _ _ _ (DOk_rtriv _ _ HD2')) H3). }
        eapply T_Bin with (A := apT s4 (apT s3 (typ_Var (ea n2)))).
        -- pose proof (chain_apT s4 _ _ _ Hs4 Hch3) as Hch3'.
           eapply coerce_typing; [ exact Hch3' | ].
           apply (typing_ap_G D2' n3 s4 D2' n4 _ _ _ Gd4 HG3).
           apply (typing_ap_G D2' (S n2) s3 D2' n3 _ _ _ Gd3 HG2).
           apply (typing_refine D2 n2 D2' (S n2) _ _ _ GdU HG2).
           apply (typing_ap_G D1 n1 s2 D2 n2 _ _ _ Gd2 HG1). exact Hty1.
        -- eapply coerce_typing; [ exact Hch4 | ].
           apply (typing_ap_G D2' n3 s4 D2' n4 _ _ _ Gd4 HG3).
           apply (typing_ap_G D2' (S n2) s3 D2' n3 _ _ _ Gd3 HG2).
           apply (typing_refine D2 n2 D2' (S n2) _ _ _ GdU HG2). exact Hty2.
        -- unfold bin_res, generic_sort in *. destruct Hko as [Hko | [Hko | Hko]]; rewrite Hko in *;
             first [ (apply sig_ring; assumption) | (apply sig_whole; assumption) | (apply sig_cmp; assumption) ].
      * (* [/]: both operands at Float *)
        assert (Ho : o = bop_div)
          by (unfold is_generic_op in Hring; destruct o; first [ reflexivity | (cbn in Hring; discriminate Hring) ]).
        destruct (unify_co f D2 (apT s2 T1) typ_Float n2) as [[[s3 cs3] n3]|] eqn:E4; [|discriminate].
        destruct (unify_co f D2 (apT s3 T2) typ_Float n3) as [[[s4 cs4] n4]|] eqn:E5; [|discriminate].
        inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
        assert (Hg : ground typ_Float) by (right; left; reflexivity).
        pose proof (ground_EvT _ Hg) as HTa.
        destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E4 (EvT_ap s2 T1 Hs2 HT1) HTa)
          as (Hs3 & Hch3 & Hk3 & Hl3).
        pose proof (Good_unify D2 n2 s3 n3 Hs3 Hk3 Hl3 HD2) as Gd3.
        pose proof (WfCtx_ap s3 _ Hs3 HG2) as HG3.
        destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E5 (EvT_ap s3 T2 Hs3 HT2) HTa)
          as (Hs4 & Hch4 & Hk4 & Hl4).
        pose proof (Good_unify D2 n3 s4 n4 Hs4 Hk4 Hl4 (DOk_mono D2 n2 n3 HD2 Hl3)) as Gd4.
        pose proof (WfCtx_ap s4 _ Hs4 HG3) as HG4.
        rewrite (ground_ap s3 _ Hg) in Hch3.
        rewrite (ground_ap s4 _ Hg) in Hch4.
        split.
        { exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3) Gd4). }
        split; [ exact HTa | ].
        refine (conj _ (conj _ _)).
        2: { cbn [erase]. rewrite !erase_coerce, Her_Hty1, Her_Hty2. reflexivity. }
        2: { cbn [lce]. split; apply lce_coerce; assumption. }
        rewrite <- !apC_comp.
        eapply T_Bin; [ | | rewrite Ho; apply sig_quot ].
        -- pose proof (chain_apT s4 _ _ _ Hs4 Hch3) as Hch3'.
           rewrite (ground_ap s4 _ Hg) in Hch3'.
           eapply coerce_typing; [ exact Hch3' | ].
           apply (typing_ap_G D2 n3 s4 D2 n4 _ _ _ Gd4 HG3).
           apply (typing_ap_G D2 n2 s3 D2 n3 _ _ _ Gd3 HG2).
           apply (typing_ap_G D1 n1 s2 D2 n2 _ _ _ Gd2 HG1). exact Hty1.
        -- eapply coerce_typing; [ exact Hch4 | ].
           apply (typing_ap_G D2 n3 s4 D2 n4 _ _ _ Gd4 HG3).
           apply (typing_ap_G D2 n2 s3 D2 n3 _ _ _ Gd3 HG2). exact Hty2.
    + (* Int-to-Float coercion at any Numeric type *)
      destruct (infer f D G a3 n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      set (D1' := upd D1 (ea n1) k_Literal) in *.
      destruct (unify_co f D1' T1 (typ_Var (ea n1)) (S n1)) as [[[s2 cs2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      assert (HN : D1' (ea n1) = k_Literal) by (unfold D1'; apply upd_same).
      assert (HEc : EvT (typ_Var (ea n1))) by (apply EvT_var, ev_ea).
      pose proof (Good_upd D1 n1 k_Literal HD1) as GdU. fold D1' in GdU.
      assert (HD1' : DOk D1' (S n1)) by (destruct GdU as (_ & _ & H2 & _); exact H2).
      destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E2 HT1 HEc) as (Hs2 & Hch & Hk2 & Hl2).
      pose proof (Good_unify D1' (S n1) s2 n2 Hs2 Hk2 Hl2 HD1') as Gd2.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 (Good_lift _ _ _ _ _ _ _ GdU Gd2)) | ].
      split; [ apply EvT_Float | ].
      refine (conj _ (conj _ _)).
      2: { cbn [erase]. rewrite erase_coerce, Her_Hty1. reflexivity. }
      2: { cbn [lce]. apply lce_coerce. exact Hlc_Hty1. }
      rewrite <- apC_comp.
      apply T_ToFloat with (A := apT s2 (typ_Var (ea n1))).
      * eapply coerce_typing; [ exact Hch | ].
        apply (typing_ap_G D1' (S n1) s2 D1' n2 _ _ _ Gd2 HG1).
        apply (typing_refine D1 n1 D1' (S n1) _ _ _ GdU HG1). exact Hty1.
      * pose proof (Hk2 (ea n1)) as H3. rewrite HN in H3. exact H3.
    + (* tag construction *)
      destruct (Nat.ltb tg1 (length w1)) eqn:Hlt; [|discriminate].
      destruct (infer f D G a6 n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (unify_co f D1 T1 (tag_payload w1 (fresh_tys n1 (nparams w1)) tg1) (n1 + nparams w1))
        as [[[s2 cs2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      pose proof (EvT_fresh_tys (nparams w1) n1) as HTs.
      destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E2 HT1 (EvT_tag_payload _ _ _ HTs))
        as (Hs2 & Hch & Hk2 & Hl2).
      pose proof (Good_unify D1 (n1 + nparams w1) s2 n2 Hs2 Hk2 Hl2
                    (DOk_mono D1 n1 (n1 + nparams w1) HD1 ltac:(lia))) as Gd2'.
      pose proof (Good_pre D1 n1 (n1 + nparams w1) s2 D1 n2 ltac:(lia) HD1 Gd2') as Gd2.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ apply EvT_ap; [ exact Hs2 | apply EvT_grp, EvT_spine; exact HTs ] | ].
      refine (conj _ (conj _ _)).
      2: { cbn [erase]. rewrite erase_coerce, Her_Hty1. reflexivity. }
      2: { cbn [lce]. apply lce_coerce. exact Hlc_Hty1. }
      rewrite <- apC_comp. rewrite apT_grp, apT_spine.
      apply T_Con; [ apply Nat.ltb_lt; exact Hlt | ].
      rewrite <- apT_tag_payload.
      eapply coerce_typing; [ exact Hch | ].
      apply (typing_ap_G D1 n1 s2 D1 n2 _ _ _ Gd2 HG1). exact Hty1.
    + (* match *)
      destruct (arms_wf_b w2 ars2) eqn:Hwb; [|discriminate].
      destruct (infer f D G a7 n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (unify_co f D1 T1 (typ_Grp w2 (spine (fresh_tys n1 (nparams w2)))) (n1 + nparams w2))
        as [[[s2 cs2] n2]|] eqn:E2; [|discriminate].
      destruct (infer_arms f D1 (apC s2 (apC s1 G)) w2 (map (apT s2) (fresh_tys n1 (nparams w2)))
                  (fresh_var G (e_match w2 a7 ars2)) (typ_Var (ea n2)) ars2 (S n2))
        as [[[[[s3 D3] T3] n3] us3]|] eqn:E3; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      pose proof (EvT_fresh_tys (nparams w2) n1) as HTs.
      destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E2 HT1 (EvT_grp _ _ (EvT_spine _ HTs)))
        as (Hs2 & Hch & Hk2 & Hl2).
      pose proof (Good_unify D1 (n1 + nparams w2) s2 n2 Hs2 Hk2 Hl2
                    (DOk_mono D1 n1 (n1 + nparams w2) HD1 ltac:(lia))) as Gd2'.
      pose proof (Good_pre D1 n1 (n1 + nparams w2) s2 D1 n2 ltac:(lia) HD1 Gd2') as Gd2.
      assert (HD2 : DOk D1 n2) by (destruct Gd2 as (_ & _ & H2 & _); exact H2).
      pose proof (WfCtx_ap s2 _ Hs2 HG1) as HG2.
      assert (Hx : fresh_var G (e_match w2 a7 ars2) `notin` dom (apC s2 (apC s1 G)) `union` fv_arms ars2).
      { pose proof (fresh_var_notin_dom G (e_match w2 a7 ars2)) as H1.
        pose proof (fresh_var_notin_fv G (e_match w2 a7 ars2)) as H2. simpl in H2.
        pose proof (dom_apC s1 G) as H3. pose proof (dom_apC s2 (apC s1 G)) as H4. fsetdec. }
      destruct (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ E3 HG2 (DOk_mono D1 n2 (S n2) HD2 (le_S _ _ (le_n n2)))
                  (Forall_EvT_ap s2 _ Hs2 HTs) (EvT_var _ (ev_ea n2)) Hx)
        as (Gd3' & HT3 & _ & Harms & Herarms & Hlcarms).
      pose proof (Good_pre D1 n2 (S n2) s3 D3 n3 (le_S _ _ (le_n n2)) HD2 Gd3') as Gd3.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3) | ].
      split; [ exact HT3 | ].
      refine (conj _ (conj _ (conj _ Hlcarms))).
      2: { cbn [erase]. rewrite erase_coerce, Her_Hty1, Herarms. reflexivity. }
      2: { apply lce_coerce. exact Hlc_Hty1. }
      rewrite <- !apC_comp.
      apply T_Match with (L := dom G `union` {{fresh_var G (e_match w2 a7 ars2)}})
        (w := w2) (Ts := map (apT s3) (map (apT s2) (fresh_tys n1 (nparams w2)))).
      * assert (Hc : typing D1 (apC s2 (apC s1 G)) (coerce cs2 us1)
                       (typ_Grp w2 (spine (map (apT s2) (fresh_tys n1 (nparams w2)))))).
        { rewrite <- apT_spine, <- apT_grp.
          eapply coerce_typing; [ exact Hch | ].
          apply (typing_ap_G D1 n1 s2 D1 n2 _ _ _ Gd2 HG1). exact Hty1. }
        pose proof (typing_ap_G D1 n2 s3 D3 n3 _ _ _ Gd3 HG2 Hc) as Hl.
        rewrite apT_grp, apT_spine in Hl. exact Hl.
      * apply arms_wf_b_sound. rewrite <- arms_wf_b_erase, Herarms. exact Hwb.
      * intros tg body Hf y Hy.
        apply (proj1 Harms tg body Hf y).
        pose proof (dom_apC s1 G) as H3. pose proof (dom_apC s2 (apC s1 G)) as H4. fsetdec.
      * intros e0 Hd. exact (proj2 Harms e0 Hd).
    + (* spread *)
      destruct (infer f D G a8 n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (infer f D1 (apC s1 G) a9 n1) as [[[[[s2 D2] T2] n2] us2]|] eqn:E2; [|discriminate].
      destruct (unify_co f D2 (apT s2 T1)
                  (typ_Record (row_Maybe l8 (typ_Var (ea n2)) T2 (row_Var (ea (S n2))))) (n2 + 2))
        as [[[s3 cs3] n3]|] eqn:E3; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHe _ _ _ _ _ _ _ _ _ E2 HG1 HD1) as (Gd2 & HT2 & Hty2 & Her_Hty2 & Hlc_Hty2).
      pose proof Gd2 as (_ & Hs2 & HD2 & _).
      pose proof (WfCtx_ap s2 _ Hs2 HG1) as HG2.
      assert (Hrow : EvT (typ_Record (row_Maybe l8 (typ_Var (ea n2)) T2 (row_Var (ea (S n2)))))).
      { apply EvT_Record, EvR_maybe; [ apply EvT_var, ev_ea | exact HT2 | apply EvR_var, ev_ea ]. }
      destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E3 (EvT_ap s2 T1 Hs2 HT1) Hrow)
        as (Hs3 & Hch & Hk3 & Hl3).
      pose proof (Good_unify D2 n2 s3 n3 Hs3 Hk3 ltac:(lia) HD2) as Gd3.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) Gd3) | ].
      split.
      { apply EvT_ap; [ exact Hs3 | ]. apply EvT_Record, EvR_ext; [ exact HT2 | apply EvR_var, ev_ea ]. }
      refine (conj _ (conj _ _)).
      2: { cbn [erase]. rewrite erase_coerce, Her_Hty1, Her_Hty2. reflexivity. }
      2: { cbn [lce]. split; [ apply lce_coerce; exact Hlc_Hty1 | exact Hlc_Hty2 ]. }
      rewrite <- !apC_comp.
      apply T_Spread with (P := apT s3 (typ_Var (ea n2))) (T := apT s3 T2)
        (R := apR s3 (row_Var (ea (S n2)))).
      * eapply coerce_typing; [ exact Hch | ].
        apply (typing_ap_G D2 n2 s3 D2 n3 _ _ _ Gd3 HG2).
        apply (typing_ap_G D1 n1 s2 D2 n2 _ _ _ Gd2 HG1). exact Hty1.
      * apply (typing_ap_G D2 n2 s3 D2 n3 _ _ _ Gd3 HG2). exact Hty2.
    + (* restrict *)
      destruct (infer f D G a10 n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (unify_co f D1 T1 (typ_Record (row_Ext l10 (typ_Var (ea n1)) (row_Var (ea (S n1)))))
                  (n1 + 2)) as [[[s2 cs2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      assert (Hrow : EvT (typ_Record (row_Ext l10 (typ_Var (ea n1)) (row_Var (ea (S n1)))))).
      { apply EvT_Record, EvR_ext; [ apply EvT_var, ev_ea | apply EvR_var, ev_ea ]. }
      destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E2 HT1 Hrow) as (Hs2 & Hch & Hk2 & Hl2).
      pose proof (Good_unify D1 n1 s2 n2 Hs2 Hk2 ltac:(lia) HD1) as Gd2.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ apply EvT_ap; [ exact Hs2 | apply EvT_Record, EvR_var, ev_ea ] | ].
      refine (conj _ (conj _ _)).
      2: { cbn [erase]. rewrite erase_coerce, Her_Hty1. reflexivity. }
      2: { cbn [lce]. apply lce_coerce. exact Hlc_Hty1. }
      rewrite <- apC_comp.
      apply T_Restrict with (R0 := apR s2 (row_Ext l10 (typ_Var (ea n1)) (row_Var (ea (S n1)))))
        (T := apT s2 (typ_Var (ea n1))).
      * eapply coerce_typing; [ exact Hch | ].
        apply (typing_ap_G D1 n1 s2 D1 n2 _ _ _ Gd2 HG1). exact Hty1.
      * unfold rm. simpl. rewrite Nat.eqb_refl. reflexivity.
  - intros D G fs n s D' R n' fs' H HG HD. cbn [infer_fields] in H.
    destruct fs as [| l e rest | l e rest]; try discriminate H.
    + inversion H; try subst s; try subst D'; try subst R; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvR_Empty|].
      refine (conj _ (conj eq_refl I)).
      apply FT_nil. apply uniq_apC. exact (proj1 HG).
    + destruct (infer f D G e n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (infer_fields f D1 (apC s1 G) rest n1) as [[[[[s2 D2] R2] n2] us2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst R; try subst n'; try subst e'; try subst fs'; try subst ars'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (IHf _ _ _ _ _ _ _ _ _ E2 HG1 HD1) as (Gd2 & HR2 & Hty2 & Her_Hty2 & Hlc_Hty2).
      pose proof Gd2 as (_ & Hs2 & _).
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ apply EvR_ext; [ apply EvT_ap; auto | exact HR2 ] | ].
      refine (conj _ (conj _ (conj Hlc_Hty1 Hlc_Hty2))).
      2: { cbn [erase_fields]. rewrite Her_Hty1, Her_Hty2. reflexivity. }
      rewrite <- apC_comp.
      eapply FT_cons.
      * apply (typing_ap_G D1 n1 s2 D2 n2 _ _ _ Gd2 HG1). exact Hty1.
      * exact Hty2.
  - intros D G w Ts x res ars n s D' T n' ars' H HG HD HTs Hres Hx. cbn [infer_arms] in H.
    destruct ars as [|e|tg e rest].
    + inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst ars'; clear H.
      split; [ apply Good_id; exact HD | ]. split; [ exact Hres | ].
      split; [ rewrite apT_sid; reflexivity | ].
      refine (conj _ (conj eq_refl I)). apply arms_typ_nil.
    + destruct (infer f D G e n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (unify_co f D1 T1 (apT s1 res) n1) as [[[s2 cs2] n2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst ars'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her1 & Hlc1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E2 HT1 (EvT_ap s1 res Hs1 Hres))
        as (Hs2 & Hch & Hk2 & Hl2).
      pose proof (Good_unify D1 n1 s2 n2 Hs2 Hk2 Hl2 HD1) as Gd2.
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ exact (EvT_ap s2 _ Hs2 (EvT_ap s1 res Hs1 Hres)) | ].
      split; [ apply apT_comp | ].
      refine (conj _ (conj _ _)).
      2: { cbn [erase_arms]. rewrite erase_coerce, Her1. reflexivity. }
      2: { cbn [lcea]. apply lce_coerce. exact Hlc1. }
      apply arms_typ_else. rewrite <- apC_comp.
      eapply coerce_typing; [ exact Hch | ].
      apply (typing_ap_G D1 n1 s2 D1 n2 _ _ _ Gd2 HG1). exact Hty1.
    + simpl in Hx.
      destruct (infer f D ((x ~ sch_mono (tag_payload w Ts tg)) ++ G)
                  (open_exp_wrt_exp e (e_fvar_f x)) n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (unify_co f D1 T1 (apT s1 res) n1) as [[[s2 cs2] n2]|] eqn:E2; [|discriminate].
      destruct (infer_arms f D1 (apC (scomp s2 s1) G) w (map (apT (scomp s2 s1)) Ts) x
                  (apT s2 (apT s1 res)) rest n2)
        as [[[[[s3 D3] T3] n3] us3]|] eqn:E3; [|discriminate].
      inversion H; try subst s; try subst D'; try subst T; try subst n'; try subst ars'; clear H.
      assert (Hwf : WfCtx ((x ~ sch_mono (tag_payload w Ts tg)) ++ G))
        by (apply WfCtx_cons; [ exact HG | fsetdec | apply WfSch_mono; apply EvT_tag_payload; exact HTs ]).
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 Hwf HD) as (Gd1 & HT1 & Hty1 & Her1 & Hlc1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      rewrite apC_app, apC_single, apS_mono, apT_tag_payload in Hty1.
      destruct (unify_co_sound _ _ _ _ _ _ _ _ ltac:(solve_rtriv) E2 HT1 (EvT_ap s1 res Hs1 Hres))
        as (Hs2 & Hch2 & Hk2 & Hl2).
      pose proof (Good_unify D1 n1 s2 n2 Hs2 Hk2 Hl2 HD1) as Gd2.
      pose proof (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) as Gd12.
      pose proof Gd12 as (_ & Hs12 & _).
      pose proof (WfCtx_ap _ G Hs12 HG) as HG12.
      assert (HD2 : DOk D1 n2) by (destruct Gd2 as (_ & _ & H2 & _); exact H2).
      assert (Hx3 : x `notin` dom (apC (scomp s2 s1) G) `union` fv_arms rest)
        by (pose proof (dom_apC (scomp s2 s1) G) as H3; fsetdec).
      destruct (IHa _ _ _ _ _ _ _ _ _ _ _ _ _ E3 HG12 HD2 (Forall_EvT_ap _ _ Hs12 HTs)
                  (EvT_ap s2 _ Hs2 (EvT_ap s1 res Hs1 Hres)) Hx3)
        as (Gd3 & HT3 & HT3eq & Harms & Herrest & Hlcrest).
      pose proof Gd3 as (_ & Hs3 & _).
      destruct (bind_ok x e (coerce cs2 us1)
                  (eq_trans (erase_coerce cs2 us1) Her1)
                  (lce_coerce cs2 us1 0 Hlc1) ltac:(fsetdec)) as [Her' Hlc'].
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd12 Gd3) | ].
      split; [ exact HT3 | ].
      split.
      { rewrite HT3eq, (apT_comp s2 s1 res), (apT_comp s3 (scomp s2 s1) res). reflexivity. }
      refine (conj _ (conj _ (conj Hlc' Hlcrest))).
      2: { cbn [erase_arms]. rewrite Her', Herrest. reflexivity. }
      rewrite <- (apC_comp s3 (scomp s2 s1) G), <- (map_apT_comp s3 (scomp s2 s1) Ts).
      apply arms_typ_cons.
      * intros y Hy.
        assert (Hyd : y `notin` dom (apC s1 G)) by (rewrite dom_apC; fsetdec).
        assert (Hxd : x `notin` dom (apC s1 G)) by (rewrite dom_apC; fsetdec).
        pose proof (arm_lift D1 n1 s2 D1 n2 (apC s1 G) w (map (apT s1) Ts) tg x _ _
                      Gd2 HG1 (Forall_EvT_ap _ _ Hs1 HTs) Hxd Hty1) as Hlift2.
        pose proof (coerce_typing _ _ _ _ _ _ Hch2 Hlift2) as Hco.
        assert (Hxd2 : x `notin` dom (apC s2 (apC s1 G))) by (rewrite !dom_apC; fsetdec).
        pose proof (arm_lift D1 n2 s3 D3 n3 (apC s2 (apC s1 G)) w (map (apT s2) (map (apT s1) Ts)) tg x _ _
                      Gd3 (WfCtx_ap s2 _ Hs2 HG1) (Forall_EvT_ap _ _ Hs2 (Forall_EvT_ap _ _ Hs1 HTs))
                      Hxd2 Hco) as Hlift3.
        rewrite (map_apT_comp s2 s1 Ts), (apC_comp s2 s1 G) in Hlift3.
        rewrite HT3eq.
        refine (typing_open_cl D3 (apC s3 (apC (scomp s2 s1) G)) x y _ _ _ Hlift3
                  (lce_coerce cs2 us1 0 Hlc1) _).
        simpl. pose proof (dom_apC s3 (apC (scomp s2 s1) G)) as H3.
        pose proof (dom_apC (scomp s2 s1) G) as H4. fsetdec.
      * eapply arms_typ_L; [ | exact Harms ].
        pose proof (dom_apC (scomp s2 s1) G) as H3. fsetdec.
  - intros D G p Tp fs n s D' R n' fs' H HG HD HTp Hp. cbn [infer_obj] in H.
    destruct fs as [| l e rest | l e rest]; try discriminate H.
    + inversion H; try subst s; try subst D'; try subst R; try subst n'; try subst fs'; clear H.
      split; [apply Good_id; exact HD|]. split; [apply EvR_Empty|].
      refine (conj _ (conj eq_refl (conj I (conj eq_refl _)))).
      * apply FT_nil. apply uniq_apC. exact (proj1 HG).
      * rewrite apT_sid. constructor.
    + destruct (infer f D G e n) as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (infer_obj f D1 (apC s1 G) p (apT s1 Tp) rest n1)
        as [[[[[s2 D2] R2] n2] us2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst R; try subst n'; try subst fs'; clear H.
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 HG HD) as (Gd1 & HT1 & Hty1 & Her_Hty1 & Hlc_Hty1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      simpl in Hp.
      destruct (IHo _ _ _ _ _ _ _ _ _ _ _ E2 HG1 HD1 (EvT_ap s1 Tp Hs1 HTp)
                  ltac:(rewrite dom_apC; fsetdec))
        as (Gd2 & HR2 & Hty2 & Her2 & Hlc2 & Hmk2 & Hmt2).
      pose proof Gd2 as (_ & Hs2 & _).
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split; [ apply EvR_ext; [ apply EvT_ap; auto | exact HR2 ] | ].
      refine (conj _ (conj _ (conj (conj Hlc_Hty1 Hlc2) (conj _ _)))).
      4: { rewrite <- apT_comp. constructor. exact Hmt2. }
      3: { cbn [marks]. rewrite Hmk2. reflexivity. }
      2: { cbn [erase_fields]. rewrite Her_Hty1, Her2. reflexivity. }
      rewrite <- apC_comp.
      eapply FT_cons.
      * apply (typing_ap_G _ _ _ _ _ _ _ _ Gd2 HG1). exact Hty1.
      * exact Hty2.
    + destruct e; try discriminate H.
      destruct (infer f D ((p ~ sch_mono Tp) ++ G) (open_exp_wrt_exp e (e_fvar_f p)) n)
        as [[[[[s1 D1] T1] n1] us1]|] eqn:E1; [|discriminate].
      destruct (infer_obj f D1 (apC s1 G) p (apT s1 Tp) rest n1)
        as [[[[[s2 D2] R2] n2] us2]|] eqn:E2; [|discriminate].
      inversion H; try subst s; try subst D'; try subst R; try subst n'; try subst fs'; clear H.
      simpl in Hp.
      assert (Hwf : WfCtx ((p ~ sch_mono Tp) ++ G))
        by (apply WfCtx_cons; [ exact HG | fsetdec | apply WfSch_mono; exact HTp ]).
      destruct (IHe _ _ _ _ _ _ _ _ _ E1 Hwf HD) as (Gd1 & HT1 & Hty1 & Her1 & Hlc1).
      pose proof Gd1 as (_ & Hs1 & HD1 & _).
      pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
      destruct (bind_ok _ e _ Her1 Hlc1 ltac:(fsetdec)) as [Her' Hlc'].
      destruct (IHo _ _ _ _ _ _ _ _ _ _ _ E2 HG1 HD1 (EvT_ap s1 Tp Hs1 HTp)
                  ltac:(rewrite dom_apC; fsetdec))
        as (Gd2 & HR2 & Hty2 & Her2 & Hlc2 & Hmk2 & Hmt2).
      pose proof Gd2 as (_ & Hs2 & _).
      split; [ exact (Good_comp _ _ _ _ _ _ _ _ Gd1 Gd2) | ].
      split.
      { apply EvR_ext; [ | exact HR2 ].
        apply EvT_arrow; [ apply EvT_ap; [ exact Hs2 | apply EvT_ap; [ exact Hs1 | exact HTp ] ]
                         | apply EvT_ap; [ exact Hs2 | exact HT1 ] ]. }
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      5: { rewrite <- apT_comp. constructor. exact Hmt2. }
      4: { cbn [marks]. rewrite Hmk2. reflexivity. }
      3: { cbn [lcef]. split; [ exact Hlc' | exact Hlc2 ]. }
      2: { cbn [erase_fields erase]. rewrite Her', Her2. reflexivity. }
      rewrite <- apC_comp.
      rewrite apC_app, apC_single in Hty1.
      eapply FT_meth.
      * refine (typing_ap_G _ _ _ _ _ _ (e_abs (cl 0 p us1)) (typ_Arrow (apT s1 Tp) T1) Gd2 HG1 _).
        apply T_Abs with (L := dom G `union` {{p}}).
        intros y Hy.
        assert (Hdom : y `notin` dom ((p ~ apS s1 (sch_mono Tp)) ++ apC s1 G))
          by (simpl; rewrite dom_apC; fsetdec).
        exact (typing_open_cl D1 (apC s1 G) _ y _ _ _ Hty1 Hlc1 Hdom).
      * exact Hty2.
Qed.

(* The statement for programs: a closed term the algorithm accepts has an
   elaboration, which has the type the algorithm returns, in the kinding
   environment it returns, which records the sort of each variable the type
   leaves free, and which erases to the program. *)
Theorem infer_closed_sound : forall fuel e D T e',
  infer_closed_elab fuel e = Some (D, T, e') -> typing D nil e' T /\ erase e' = e.
Proof.
  intros fuel e D T e' H. unfold infer_closed_elab in H.
  destruct (infer fuel d_any nil e 0) as [[[[[s D0] T0] n] us]|] eqn:Ei; [|discriminate].
  inversion H; subst; clear H.
  assert (Hwf : WfCtx nil) by (split; [constructor | intros x sc Hb; inversion Hb]).
  destruct ((proj1 (infer_sound fuel)) _ _ _ _ _ _ _ _ _ Ei Hwf (d_any_DOk 0))
    as (_ & _ & Hty & Her & _).
  exact (conj Hty Her).
Qed.
