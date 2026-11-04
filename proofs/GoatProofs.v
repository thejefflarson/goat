(* Hand-written metatheory over the Ott-generated definitions (Goat_ott.v).
   B2 (#70) lands two infrastructure lemmas end-to-end to prove the pipeline is
   wired: one over the goat-specific row equivalence, one over the
   locally-nameless term-binder infrastructure. The full soundness development
   is B3 (#71). *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.

(* The row-equivalence relation (Goat_ott.teq/req) states symmetry and
   transitivity but no reflexivity rule; reflexivity is a derived fact, needed
   for canonical forms in B3. It holds by mutual induction on the type/row
   structure. *)
Scheme typ_mut := Induction for typ Sort Prop
with   row_mut := Induction for row Sort Prop.
Combined Scheme typ_row_mutind from typ_mut, row_mut.

Lemma teq_req_refl :
  (forall T : typ, teq T T) /\ (forall R : row, req R R).
Proof.
  apply typ_row_mutind; intros; eauto.
Qed.

Corollary teq_refl : forall T : typ, teq T T.
Proof. apply teq_req_refl. Qed.

Corollary req_refl : forall R : row, req R R.
Proof. apply teq_req_refl. Qed.

(* Mutual structural induction over the term/record-spine block. The record
   literal makes [exp] mutually recursive with [fields] (goat_ln.ott), so the
   locally-nameless infrastructure lemmas need the companion [fields] motive. *)
Scheme exp_mut := Induction for exp Sort Prop
with   fields_mut := Induction for fields Sort Prop.
Combined Scheme exp_fields_mutind from exp_mut, fields_mut.

(* Substituting for a variable not free in a term is the identity. This is the
   LNgen-emitted [subst_exp_fresh_eq]; it is proved by hand here because LNgen
   (a Haskell tool, not packaged on opam) is outside the Ott/Coq pipeline, and
   it is the standard non-trivial exercise of the generated [subst_exp]/[fv_exp]
   locally-nameless infrastructure. *)
Lemma subst_fresh_eq_mut :
  (forall (e : exp) (y : termvar) (u : exp),
      y `notin` fv_exp e -> subst_exp u y e = e) /\
  (forall (fs : fields) (y : termvar) (u : exp),
      y `notin` fv_fields fs -> subst_fields u y fs = fs).
Proof.
  apply exp_fields_mutind; intros; simpl in *;
    try reflexivity;
    try (destruct (eq_var x y); subst; [ exfalso; fsetdec | reflexivity ]);
    solve [ f_equal; auto ].
Qed.

Lemma subst_exp_fresh_eq : forall (e : exp) (y : termvar) (u : exp),
  y `notin` fv_exp e ->
  subst_exp u y e = e.
Proof. apply subst_fresh_eq_mut. Qed.
