(* Algorithm W returns the elaborated term (ADR 0037, decision 3; phase 5,
   stage 4, part 3b).

   [infer_elab fuel e = Some (D, e', T)] says [e'] has type [T] in the empty
   context and erases to [e]: the checker's program, with the [fold] and
   [unfold] its equi-recursive types leave implicit written in.  W writes them
   in where it equates the type of a subterm with the type its context needs
   (GoatInferW.v, GoatCoerce.v), so [e'] is [e] only when no recursive type
   meets its unrolling.

   Two facts the earlier statement of this file leaned on are gone with the
   knot-tying unifier.  W now builds recursive types, so no theorem says its
   types are free of them ([infer_mu_free] held for the unifier that never
   bound a variable to a type containing it); [infer_guarded]
   (GoatInferGuard.v) says instead that every recursive type in them is
   guarded.  And [e'] is no longer the identity, so the
   syntactic fact "W accepts no [fold] or [unfold]" is no longer how [erase]
   is shown to fix it: [infer_closed_sound] proves [erase e' = e] directly. *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatDefs.
Require Import Goat.GoatInfer.
Require Import Goat.GoatInferW.
Require Import Goat.GoatInferSound.
Require Import Goat.GoatElab.
Require Import Stdlib.Lists.List.
Import ListNotations.

Definition infer_elab (fuel : nat) (e : exp) : option (denv * exp * typ) :=
  match infer_closed_elab fuel e with
  | Some (D, T, e') => Some (D, e', T)
  | None => None
  end.

Theorem infer_elab_sound : forall fuel e D e' T,
  infer_elab fuel e = Some (D, e', T) -> typing D nil e' T /\ erase e' = e.
Proof.
  intros fuel e D e' T H. unfold infer_elab in H.
  destruct (infer_closed_elab fuel e) as [[[D0 T0] e0]|] eqn:E; [ | discriminate ].
  injection H as <- <- <-. exact (infer_closed_sound _ _ _ _ _ E).
Qed.
