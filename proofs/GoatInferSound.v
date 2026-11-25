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
Require Import Goat.GoatConv.
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

Lemma typing_ap_G : forall D n s D' n' G e T,
  Good D n s D' n' -> WfCtx G -> typing D G e T -> typing D' (apC s G) e (apT s T).
Proof.
  intros D n s D' n' G e T (Hd & Hs & Hd' & _ & _ & [Hk Hkr]) HG Hty.
  exact (typing_ap D D' s G e T Hs HG (DOk_supp D n Hd) (DOk_supp D' n' Hd') Hk Hkr Hty).
Qed.

Lemma typing_refine : forall D n D' n' G e T,
  Good D n sid D' n' -> WfCtx G -> typing D G e T -> typing D' G e T.
Proof.
  intros D n D' n' G e T Hg HG Hty.
  pose proof (typing_ap_G D n sid D' n' G e T Hg HG Hty) as H.
  rewrite apC_sid, apT_sid in H. exact H.
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
  intros w Ts tg H. unfold tag_payload. destruct (nth_error (gtags w) tg) as [cs|]; [|apply EvT_Unit].
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
    assert (Hs : In tg (seq 0 (length (gtags w)))) by (apply in_seq; lia).
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
Lemma infer_abs_shape : forall f D G b n s D' T n' e' H,
  infer f D G (e_abs b) n = Some (s, D', T, n', e', H) -> exists b', e' = e_abs b'.
Proof.
  intros f D G b n s D' T n' e' Hh H. destruct f as [|f]; [ discriminate H | ].
  cbn [infer] in H.
  destruct (infer f D ((fresh_var G b ~ sch_mono (typ_Var (ea n))) ++ G)
              (open_exp_wrt_exp b (e_fvar_f (fresh_var G b))) (S n))
    as [[[[[[s0 D1] T0] n0] b0] H0]|]; [ | discriminate H ].
  inversion H; subst. eexists. reflexivity.
Qed.

Lemma is_fn_group_open_rec : forall fs k u,
  is_fn_group fs = true -> is_fn_group (open_fields_wrt_exp_rec k u fs) = true.
Proof.
  induction fs as [|l e rest IH|l e rest IH]; intros k u H; simpl in *; [ reflexivity | | discriminate H ].
  destruct e; try discriminate H. simpl. apply IH. exact H.
Qed.

Lemma infer_fields_fn_group : forall f D G fs n s D' R n' fs' H,
  is_fn_group fs = true -> infer_fields f D G fs n = Some (s, D', R, n', fs', H) ->
  fn_group fs'.
Proof.
  intros f D G fs. revert f D G. induction fs as [|l e rest IH|l e rest IH]; intros f D G n s D' R n' fs' Hh Hg H;
    destruct f as [|f]; try discriminate H; cbn [infer_fields] in H.
  - inversion H; subst. constructor.
  - destruct e; try discriminate Hg. cbn [is_fn_group] in Hg.
    destruct (infer f D G (e_abs e) n) as [[[[[[s1 D1] T1] n1] e1'] H1]|] eqn:E1; [ | discriminate H ].
    destruct (infer_fields f D1 (apC s1 G) rest n1) as [[[[[[s2 D2] R2] n2] rest'] H2]|] eqn:E2;
      [ | discriminate H ].
    inversion H; subst.
    destruct (infer_abs_shape _ _ _ _ _ _ _ _ _ _ _ E1) as [b' ->].
    constructor. exact (IH _ _ _ _ _ _ _ _ _ _ Hg E2).
Qed.

Lemma infer_fields_no_meth : forall f D G fs n s D' R n' fs' H,
  infer_fields f D G fs n = Some (s, D', R, n', fs', H) -> no_meth fs' = true.
Proof.
  intros f D G fs. revert f D G. induction fs as [|l e rest IH|l e rest IH];
    intros f D G n s D' R n' fs' Hh H; destruct f as [|f]; try discriminate H; cbn [infer_fields] in H.
  - inversion H; subst. reflexivity.
  - destruct (infer f D G e n) as [[[[[[s1 D1] T1] n1] e1'] H1]|]; [ | discriminate H ].
    destruct (infer_fields f D1 (apC s1 G) rest n1) as [[[[[[s2 D2] R2] n2] rest'] H2]|] eqn:E2;
      [ | discriminate H ].
    inversion H; subst. cbn [no_meth]. exact (IH _ _ _ _ _ _ _ _ _ _ E2).
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
  intros D n s D' n' G fs R (Hd & Hs & Hd' & _ & _ & [Hk Hkr]) HG Hty.
  exact (fields_ap0 D D' s G fs R Hs HG (DOk_supp D n Hd) (DOk_supp D' n' Hd') Hk Hkr Hty).
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

Lemma tie_obj_sound : forall f fs D R Rsl n s D' n' fs2,
  tie_obj f D fs R Rsl n = Some (s, D', n', fs2) ->
  forall G, WfCtx G -> DOk D n -> EvR R -> EvR Rsl -> field_typing D G fs R -> lcef 0 fs ->
  Good D n s D' n' /\ field_typing D' (apC s G) fs2 (apR s Rsl) /\
  erase_fields fs2 = erase_fields fs /\ lcef 0 fs2 /\ marks fs2 = marks fs /\
  meth_rel fs (apR s R) (apR s Rsl).
Proof.
  intros f fs. induction fs as [|l e rest IH|l e rest IH];
    intros D R Rsl n s D' n' fs2 H G HG HD HR HRsl Hft Hlc;
    destruct R as [|r|l1 T R'|l1 P0 T0 R'], Rsl as [|r2|l2 A Rsl'|l2 P2 T2 R2'];
    simpl in H; try discriminate H.
  - inversion H; subst; clear H.
    refine (conj (Good_id _ _ HD) _).
    rewrite apC_sid, apR_id. refine (conj _ (conj eq_refl (conj I (conj eq_refl MRl_nil)))).
    apply FT_nil. exact (proj1 HG).
  - destruct (Nat.eqb l l1 && Nat.eqb l l2) eqn:Hl; [ | discriminate H ].
    apply Bool.andb_true_iff in Hl. destruct Hl as [Hl1 Hl2].
    apply Nat.eqb_eq in Hl1. apply Nat.eqb_eq in Hl2. subst l1 l2.
    destruct (unify_co f D T A n) as [[[[s1 D1] cs] n1]|] eqn:E1; [ | discriminate H ].
    destruct (tie_obj f D1 rest (apR s1 R') (apR s1 Rsl') n1) as [[[[s2 D2] n2] rest']|] eqn:E2; [ | discriminate H ].
    inversion H; subst; clear H.
    inversion Hft as [ | D0 G0 l0 e0 T0 fs0 R0 Hty0 Hrest0 | D0 G0 l0 e0 T0 fs0 R0 Hty0 Hrest0 ]; subst.
    destruct (EvR_ext_inv _ _ _ HR) as [HT HR'].
    destruct (EvR_ext_inv _ _ _ HRsl) as [HA HRsl'].
    destruct (unify_co_sound _ _ _ _ _ _ _ _ _ E1 HT HA) as (Hs1 & Hch & Hgu1).
    pose proof ((proj2 Hgu1) HD) as Gd1.
    pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
    pose proof (proj1 (proj2 (proj2 Gd1))) as HD1.
    destruct (IH _ _ _ _ _ _ _ _ E2 (apC s1 G) HG1 HD1 (EvR_ap _ _ Hs1 HR') (EvR_ap _ _ Hs1 HRsl')
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
    destruct (unify_co f D T A n) as [[[[s1 D1] cs] n1]|] eqn:E1; [ | discriminate H ].
    destruct (tie_obj f D1 rest (apR s1 R') (apR s1 Rsl') n1) as [[[[s2 D2] n2] rest']|] eqn:E2; [ | discriminate H ].
    inversion H; subst; clear H.
    inversion Hft as [ | D0 G0 l0 e0 T0 fs0 R0 Hty0 Hrest0 | D0 G0 l0 e0 T0 fs0 R0 Hty0 Hrest0 ]; subst.
    destruct (EvR_ext_inv _ _ _ HR) as [HT HR'].
    destruct (EvR_ext_inv _ _ _ HRsl) as [HA HRsl'].
    destruct (unify_co_sound _ _ _ _ _ _ _ _ _ E1 HT HA) as (Hs1 & Hch & Hgu1).
    pose proof ((proj2 Hgu1) HD) as Gd1.
    pose proof (WfCtx_ap s1 G Hs1 HG) as HG1.
    pose proof (proj1 (proj2 (proj2 Gd1))) as HD1.
    destruct (IH _ _ _ _ _ _ _ _ E2 (apC s1 G) HG1 HD1 (EvR_ap _ _ Hs1 HR') (EvR_ap _ _ Hs1 HRsl')
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
    destruct (teqD_Arrow_inv _ _ _ _ Hteq) as (A1 & B1 & Heq & Ha & Hb).
    injection Heq as <- <-.
    eapply T_Conv; [ | apply teq_arrow; [ exact Hx | apply teq_refl ] ].
    eapply T_ConvD; [ | apply teqD_Arrow; [ exact Ha | apply teqD_refl ] ].
    apply (T_Abs L). intros x Hx0.
    unfold open_exp_wrt_exp. rewrite open_coerce.
    eapply coerce_typing; [ exact Hc | ].
    eapply T_ConvD; [ exact (Hbody x Hx0) | exact Hb ].
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

Lemma unify_mem_sound : forall f D e T A n s D' n' e',
  unify_mem f D e T A n = Some (s, D', n', e') -> EvT T -> EvT A ->
  OkS s /\ mem_co e e' (apT s T) (apT s A) /\ GoodU D n s D' n' /\
  erase e' = erase e /\ (lce 0 e -> lce 0 e') /\ (forall b, e = e_abs b -> exists b', e' = e_abs b').
Proof.
  intros f D e T A n s D' n' e' H HT HA. unfold unify_mem in H.
  destruct (unify_t f D T A n) as [[[s0 D0] n0]|] eqn:Et.
  - inversion H; subst; clear H.
    destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ _ Et HT HA) as (Hs & Ht & Hg).
    refine (conj Hs (conj (mc_same _ _ _ Ht) (conj Hg (conj eq_refl (conj (fun h => h) _))))).
    intros b ->. eexists; reflexivity.
  - destruct e as [ | | | | | | b | | | | | | | | | | | | | | | | ]; try discriminate H.
    destruct T as [ | | | | | X Y | | | | | ]; try discriminate H.
    destruct A as [ | | | | | X' Y' | | | | | ]; try discriminate H.
    destruct (unify_t f D X X' n) as [[[s1 D1] n1]|] eqn:E1; [ | discriminate H ].
    destruct (unify_co f D1 (apT s1 Y) (apT s1 Y') n1) as [[[[s2 D2] cs] n2]|] eqn:E2; [ | discriminate H ].
    inversion H; subst; clear H.
    destruct (EvT_arrow_inv _ _ HT) as [HX HY]. destruct (EvT_arrow_inv _ _ HA) as [HX' HY'].
    destruct ((proj1 (unify_sound f)) _ _ _ _ _ _ _ E1 HX HX') as (Hs1 & Hx & Hg1).
    destruct (unify_co_sound _ _ _ _ _ _ _ _ _ E2 (EvT_ap _ _ Hs1 HY) (EvT_ap _ _ Hs1 HY'))
      as (Hs2 & Hc & Hg2).
    refine (conj (OkS_comp _ _ Hs2 Hs1) (conj _ (conj (GoodU_comp _ _ _ _ _ _ _ _ Hg1 Hg2) (conj _ (conj _ _))))).
    + change (mem_co (e_abs b) (e_abs (coerce cs b))
                (typ_Arrow (apT (scomp s2 s1) X) (apT (scomp s2 s1) Y))
                (typ_Arrow (apT (scomp s2 s1) X') (apT (scomp s2 s1) Y'))).
      rewrite <- !apT_comp. apply mc_abs; [ apply teq_apT; exact Hx | exact Hc ].
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

Lemma unify_grp_sound : forall f D fs R1 R2 n s D' n' fs2,
  unify_grp f D fs R1 R2 n = Some (s, D', n', fs2) -> EvR R1 -> EvR R2 ->
  OkS s /\ pw_co fs (apR s R1) (apR s R2) fs2 /\ GoodU D n s D' n' /\
  erase_fields fs2 = erase_fields fs /\ (lcef 0 fs -> lcef 0 fs2) /\ (fn_group fs -> fn_group fs2).
Proof.
  induction f as [|f IH]; intros D fs R1 R2 n s D' n' fs2 H H1 H2; [ discriminate | ].
  cbn [unify_grp] in H.
  destruct fs as [|l e rest|l e rest]; destruct R1 as [|r|l1 T R1'|lm Pm Tm Rm];
    destruct R2 as [|r2|l2 A R2'|lm2 Pm2 Tm2 Rm2]; try discriminate H.
  - inversion H; subst; clear H.
    refine (conj OkS_id (conj _ (conj (GoodU_id _ _) (conj eq_refl (conj (fun h => h) (fun h => h)))))).
    rewrite apR_id. constructor.
  - destruct (Nat.eqb l l1 && Nat.eqb l l2) eqn:Hl; [ | discriminate H ].
    apply Bool.andb_true_iff in Hl. destruct Hl as [Hl1 Hl2].
    apply Nat.eqb_eq in Hl1. apply Nat.eqb_eq in Hl2. subst l1 l2.
    destruct (unify_mem f D e T A n) as [[[[s1 D1] n1] e']|] eqn:E1; [ | discriminate H ].
    destruct (unify_grp f D1 rest (apR s1 R1') (apR s1 R2') n1) as [[[[s2 D2] n2] rest']|] eqn:E2; [ | discriminate H ].
    inversion H; subst; clear H.
    destruct (EvR_ext_inv _ _ _ H1) as [HT HR1]. destruct (EvR_ext_inv _ _ _ H2) as [HA HR2].
    destruct (unify_mem_sound _ _ _ _ _ _ _ _ _ _ E1 HT HA) as (Hs1 & Hm & Hg1 & Her1 & Hlc1 & Hab1).
    destruct (IH _ _ _ _ _ _ _ _ _ E2 (EvR_ap s1 _ Hs1 HR1) (EvR_ap s1 _ Hs1 HR2))
      as (Hs2 & Hp & Hg2 & Her2 & Hlc2 & Hab2).
    refine (conj (OkS_comp _ _ Hs2 Hs1) (conj _ (conj (GoodU_comp _ _ _ _ _ _ _ _ Hg1 Hg2) (conj _ (conj _ _))))).
    + rewrite !apR_Ext. rewrite <- !apT_comp, <- !apR_comp.
      constructor; [ apply mem_co_ap; assumption | exact Hp ].
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

(* The environment a unifier call runs in is well formed: it is a hypothesis, a
   shorter supply, or the environment a [Good] step returned. *)
Ltac dok :=
  first [ assumption
        | (eapply DOk_mono; [ assumption | lia ])
        | (eapply Good_dok; eassumption)
        | (eapply DOk_mono; [ eapply Good_dok; eassumption | lia ]) ].

