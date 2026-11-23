(* ======================================================================
   START HERE: what this proof says, and how to read it
   ======================================================================

   WHAT WE ARE PROVING
   -------------------
   The theorem at the bottom of this file is called [soundness].  In plain
   words it says:

       If a goat program passes the type checker, then running it can never
       crash or get stuck.

   That is the entire point of a type system.  The checker looks at a program
   BEFORE it runs and says "this is fine".  Soundness is the promise that the
   checker is not lying: a program it accepts will never reach a state like
   "add a number to a function" or "call something that is not a function",
   where the machine would not know what to do next.  ("Stuck" means: not
   finished, yet no rule says how to continue.)

   A few words you will see everywhere:

   - A TERM (or program, or expression) is a piece of goat code, such as
     [e_app e1 e2], the call of [e1] on [e2].  The Ott/Coq name for the type
     of all terms is [exp].
   - A TYPE says what kind of thing a term produces: a number, a bool, a
     function from one type to another, a record.
   - A TYPING CONTEXT (written [G]) is a list recording the type of every
     variable currently in scope, like a table "x : number, f : number -> bool".
     Whether a term is well typed always depends on this table.
   - The statement [typing G e T] reads "in context [G], term [e] has type
     [T]".  We call a proof of that sentence a TYPING DERIVATION: a little tree
     of rules (T_Var, T_App, ...) showing why [e] has type [T].
   - A VALUE is a finished result that needs no more work: a number, [true],
     [false], a function, or a record whose fields are all values.
   - A STEP, written [step e e'], is one unit of running: [e] turns into [e']
     by one rule, for example calling a function on a value by plugging the
     value into the function body.  [multistep e e'] means zero or more steps.

   THE TWO-PART RECIPE
   -------------------
   Nobody proves soundness in one go.  The standard trick is two smaller
   promises that, together, give the big one.

   1. PROGRESS: a well-typed program that is not finished can always take
      another step.  It is never stuck RIGHT NOW.
         (proved in GoatMeta.v, theorem [progress])

   2. PRESERVATION: if a well-typed program takes a step, the result is still
      well typed, with the SAME type.  A step never breaks the types.
         (proved in this file, theorem [preservation])

   Why do the two together rule out getting stuck?  Picture running a program
   one step at a time.  Start with a well-typed program.  By progress it is
   finished or it can step.  If it steps, preservation says the new program is
   well typed too -- so progress applies AGAIN, and we can step again, and so
   on.  At every moment along the run the program is well typed, so at every
   moment it is either done or able to continue.  Therefore it can never be
   stuck.  Turning "and so on" into a proof is a short induction on the number
   of steps; that is [soundness], at the bottom of this file.

   MAP OF THIS FILE
   ----------------
   The two short theorems at the end ([preservation], [soundness]) are easy to
   read.  The long part in the MIDDLE is machinery that [preservation] needs.
   The reason: when a function is called, [(fun x => body) v], the step plugs
   [v] in for [x] in [body].  To show the result is still well typed we need a
   SUBSTITUTION LEMMA: "plugging a well-typed value into a well-typed body
   keeps it well typed".  That lemma is easy for plain functions, but goat
   (like ML and Haskell) has polymorphic [let], and that makes it hard.  So,
   top to bottom:

     1. small helper lemmas about which type variables a substitution touches
     2. the HARD LEMMA [typing_tsubst_gen_mut]: substituting for TYPE variables
        inside a typing derivation (the polymorphic-[let] story is told just
        above it, read that one slowly)
     3. weakening ([typing_weaken]) and the term-substitution lemmas
        ([typing_subst], [typing_subst_poly]) built from it
     4. [preservation], then [soundness]

   Read the explanation above [typing_tsubst_gen_mut] for the one genuinely
   tricky idea.  Everything else is bookkeeping around it.

   A NOTE ON READING COQ
   ---------------------
   A Coq proof is a conversation with the computer.  [Lemma name : statement.]
   announces a claim; [Proof.] ... [Qed.] is a recipe the computer checks step
   by step; if [Qed] is accepted, the claim is certainly true.  Each line in
   between is a TACTIC, an instruction like "assume this", "split the goal in
   two", or "use that other lemma".  At any moment the computer shows the
   GOAL (what is left to show) above a list of what we already know
   (the hypotheses).  The comments in this file tell you what each move does
   to that goal.  [Print Assumptions soundness.] reporting "Closed under the
   global context" means the proof rests on no unproved assumptions at all.
   ====================================================================== *)

(* The two canonical Hindley-Milner substitution lemmas (issue #151), and the
   term-substitution / preservation / soundness development that rests on them.

   The wall the earlier passes hit was the T-Let case: generalization does not
   commute with a capturing substitution, because the let-generalized variables
   can be captured by the substitution's range.  The fix (approach (a), a
   derivation-level freshness/Barendregt step) is carried out HERE rather than in
   the typing rule: at each T-Let the generalized variables are renamed to atoms
   fresh for the substitution and the target context ([mk_rename]), so that the
   capture-avoiding substituted scheme ([casch], GoatHM) both preserves the
   instances ([casch_inst]) AND lines up with [gen] over the target context
   ([casch_gen_sch_equiv] below).  No typing rule changes; the set of accepted
   programs is unchanged.

   Everything is axiom- and admit-free:

   - Free-variable image of a substitution ([ftv_ap_typ]/[frv_ap_typ] and their
     converses): which atoms survive [ap_typ].
   - [casch_gen_sch_equiv]: capture-avoiding substitution of a generalization,
     with the renamed quantifiers fresh for the target context, is [gen] of the
     substituted body -- the bridge from [casch_inst] back to [gen].
   - [ctx_subst]/[tr_supp]/[tr_compat] and [typing_tsubst_gen_mut]: the general
     type/row substitution lemma.  The context relation allows EXTRA target
     bindings, so the identity instance is weakening.
   - L5 [typing_tsubst_fix] and L4 [typing_weaken] fall out as instances.
   - L6a [typing_subst], L6b [typing_subst_poly], then [preservation] and
     [soundness] (moved here from GoatSubst now that the two lemmas are proved). *)

Require Import Metalib.Metatheory.
Require Import Goat.Goat_ott.
Require Import Goat.GoatProofs.
Require Import Goat.GoatRows.
Require Import Goat.GoatDefs.
Require Import Goat.GoatMu.
Require Import Goat.GoatTags.
Require Import Goat.GoatRecArith.
Require Import Goat.GoatMeta.
Require Import Goat.GoatSpread.
Require Import Goat.GoatConv.
Require Import Goat.GoatSubst.
Require Import Goat.GoatBij.
Require Import Goat.GoatHM.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* ===== free-variable image of a substitution (membership form) ===== *)

Lemma ftv_ap_mut :
  (forall T st sr a,
     a `in` ftv_typ (ap_typ st sr T) ->
     (exists b, b `in` ftv_typ T /\ a `in` ftv_typ (st b)) \/
     (exists p, p `in` frv_typ T /\ a `in` ftv_row (sr p))) /\
  (forall R st sr a,
     a `in` ftv_row (ap_row st sr R) ->
     (exists b, b `in` ftv_row R /\ a `in` ftv_typ (st b)) \/
     (exists p, p `in` frv_row R /\ a `in` ftv_row (sr p))).
Proof.
  apply typ_row_mutind; intros; simpl in *.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - (* Arrow *) rewrite AtomSetFacts.union_iff in H1. destruct H1 as [H1|H1].
    + destruct (H _ _ _ H1) as [[b [Hb Ha]]|[p [Hp Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists p; split; [fsetdec|auto].
    + destruct (H0 _ _ _ H1) as [[b [Hb Ha]]|[p [Hp Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists p; split; [fsetdec|auto].
  - (* Record *) destruct (H _ _ _ H0) as [[b [Hb Ha]]|[p [Hp Ha]]].
    + left; exists b; auto.
    + right; exists p; auto.
  - (* Var *) left. exists a. split; [fsetdec|auto].
  - fsetdec.
  - apply H; assumption.
  - apply H; assumption.
  - fsetdec.
  - (* row_Var *) right. exists r. split; [fsetdec|auto].
  - (* row_Ext *) rewrite AtomSetFacts.union_iff in H1. destruct H1 as [H1|H1].
    + destruct (H _ _ _ H1) as [[b [Hb Ha]]|[p [Hp Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists p; split; [fsetdec|auto].
    + destruct (H0 _ _ _ H1) as [[b [Hb Ha]]|[p [Hp Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists p; split; [fsetdec|auto].
  - (* row_Maybe *) rewrite AtomSetFacts.union_iff in H2. destruct H2 as [H2|H2].
    + destruct (H _ _ _ H2) as [[b [Hb Ha]]|[p [Hp Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists p; split; [fsetdec|auto].
    + rewrite AtomSetFacts.union_iff in H2. destruct H2 as [H2|H2].
      * destruct (H0 _ _ _ H2) as [[b [Hb Ha]]|[p [Hp Ha]]].
        -- left; exists b; split; [fsetdec|auto].
        -- right; exists p; split; [fsetdec|auto].
      * destruct (H1 _ _ _ H2) as [[b [Hb Ha]]|[p [Hp Ha]]].
        -- left; exists b; split; [fsetdec|auto].
        -- right; exists p; split; [fsetdec|auto].
Qed.

Lemma frv_ap_mut :
  (forall T st sr p,
     p `in` frv_typ (ap_typ st sr T) ->
     (exists b, b `in` ftv_typ T /\ p `in` frv_typ (st b)) \/
     (exists q, q `in` frv_typ T /\ p `in` frv_row (sr q))) /\
  (forall R st sr p,
     p `in` frv_row (ap_row st sr R) ->
     (exists b, b `in` ftv_row R /\ p `in` frv_typ (st b)) \/
     (exists q, q `in` frv_row R /\ p `in` frv_row (sr q))).
Proof.
  apply typ_row_mutind; intros; simpl in *.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - fsetdec.
  - rewrite AtomSetFacts.union_iff in H1. destruct H1 as [H1|H1].
    + destruct (H _ _ _ H1) as [[b [Hb Ha]]|[q [Hq Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists q; split; [fsetdec|auto].
    + destruct (H0 _ _ _ H1) as [[b [Hb Ha]]|[q [Hq Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists q; split; [fsetdec|auto].
  - destruct (H _ _ _ H0) as [[b [Hb Ha]]|[q [Hq Ha]]].
    + left; exists b; auto.
    + right; exists q; auto.
  - (* Var *) left. exists a. split; [fsetdec|auto].
  - fsetdec.
  - apply H; assumption.
  - apply H; assumption.
  - fsetdec.
  - (* row_Var *) right. exists r. split; [fsetdec|auto].
  - rewrite AtomSetFacts.union_iff in H1. destruct H1 as [H1|H1].
    + destruct (H _ _ _ H1) as [[b [Hb Ha]]|[q [Hq Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists q; split; [fsetdec|auto].
    + destruct (H0 _ _ _ H1) as [[b [Hb Ha]]|[q [Hq Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists q; split; [fsetdec|auto].
  - (* row_Maybe *) rewrite AtomSetFacts.union_iff in H2. destruct H2 as [H2|H2].
    + destruct (H _ _ _ H2) as [[b [Hb Ha]]|[q [Hq Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists q; split; [fsetdec|auto].
    + rewrite AtomSetFacts.union_iff in H2. destruct H2 as [H2|H2].
      * destruct (H0 _ _ _ H2) as [[b [Hb Ha]]|[q [Hq Ha]]].
        -- left; exists b; split; [fsetdec|auto].
        -- right; exists q; split; [fsetdec|auto].
      * destruct (H1 _ _ _ H2) as [[b [Hb Ha]]|[q [Hq Ha]]].
        -- left; exists b; split; [fsetdec|auto].
        -- right; exists q; split; [fsetdec|auto].
Qed.

Lemma ftv_ap_typ : forall st sr T a,
  a `in` ftv_typ (ap_typ st sr T) ->
  (exists b, b `in` ftv_typ T /\ a `in` ftv_typ (st b)) \/
  (exists p, p `in` frv_typ T /\ a `in` ftv_row (sr p)).
Proof. intros. eapply (proj1 ftv_ap_mut); eauto. Qed.

Lemma frv_ap_typ : forall st sr T p,
  p `in` frv_typ (ap_typ st sr T) ->
  (exists b, b `in` ftv_typ T /\ p `in` frv_typ (st b)) \/
  (exists q, q `in` frv_typ T /\ p `in` frv_row (sr q)).
Proof. intros. eapply (proj1 frv_ap_mut); eauto. Qed.

(* backward direction: a free var of the image is witnessed by a free var of the
   source mapped through the substitution. *)
Lemma ftv_ap_in_mut :
  (forall T st sr a,
     ((exists b, b `in` ftv_typ T /\ a `in` ftv_typ (st b)) \/
      (exists p, p `in` frv_typ T /\ a `in` ftv_row (sr p))) ->
     a `in` ftv_typ (ap_typ st sr T)) /\
  (forall R st sr a,
     ((exists b, b `in` ftv_row R /\ a `in` ftv_typ (st b)) \/
      (exists p, p `in` frv_row R /\ a `in` ftv_row (sr p))) ->
     a `in` ftv_row (ap_row st sr R)).
Proof.
  apply typ_row_mutind; intros; simpl in *.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - rewrite AtomSetFacts.union_iff.
    destruct H1 as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|Hb];
        [left; apply H; left; eauto | right; apply H0; left; eauto].
    + rewrite AtomSetFacts.union_iff in Hp. destruct Hp as [Hp|Hp];
        [left; apply H; right; eauto | right; apply H0; right; eauto].
  - apply H. destruct H0 as [[b [Hb Ha]]|[p [Hp Ha]]]; [left; eauto | right; eauto].
  - destruct H as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.singleton_iff in Hb. subst b. exact Ha.
    + fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - apply H; assumption.
  - apply H; assumption.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp Ha]]]; [fsetdec|].
    rewrite AtomSetFacts.singleton_iff in Hp. subst p. exact Ha.
  - rewrite AtomSetFacts.union_iff.
    destruct H1 as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|Hb];
        [left; apply H; left; eauto | right; apply H0; left; eauto].
    + rewrite AtomSetFacts.union_iff in Hp. destruct Hp as [Hp|Hp];
        [left; apply H; right; eauto | right; apply H0; right; eauto].
  - (* row_Maybe *) rewrite !AtomSetFacts.union_iff.
    destruct H2 as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite !AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|[Hb|Hb]];
        [ left; apply H; left; eauto
        | right; left; apply H0; left; eauto
        | right; right; apply H1; left; eauto ].
    + rewrite !AtomSetFacts.union_iff in Hp. destruct Hp as [Hp|[Hp|Hp]];
        [ left; apply H; right; eauto
        | right; left; apply H0; right; eauto
        | right; right; apply H1; right; eauto ].
Qed.

Lemma ftv_ap_in1 : forall st sr T a b,
  b `in` ftv_typ T -> a `in` ftv_typ (st b) -> a `in` ftv_typ (ap_typ st sr T).
Proof. intros. apply (proj1 ftv_ap_in_mut). left. eauto. Qed.

Lemma ftv_ap_in2 : forall st sr T a p,
  p `in` frv_typ T -> a `in` ftv_row (sr p) -> a `in` ftv_typ (ap_typ st sr T).
Proof. intros. apply (proj1 ftv_ap_in_mut). right. eauto. Qed.

Lemma frv_ap_in_mut :
  (forall T st sr a,
     ((exists b, b `in` ftv_typ T /\ a `in` frv_typ (st b)) \/
      (exists p, p `in` frv_typ T /\ a `in` frv_row (sr p))) ->
     a `in` frv_typ (ap_typ st sr T)) /\
  (forall R st sr a,
     ((exists b, b `in` ftv_row R /\ a `in` frv_typ (st b)) \/
      (exists p, p `in` frv_row R /\ a `in` frv_row (sr p))) ->
     a `in` frv_row (ap_row st sr R)).
Proof.
  apply typ_row_mutind; intros; simpl in *.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - rewrite AtomSetFacts.union_iff.
    destruct H1 as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|Hb];
        [left; apply H; left; eauto | right; apply H0; left; eauto].
    + rewrite AtomSetFacts.union_iff in Hp. destruct Hp as [Hp|Hp];
        [left; apply H; right; eauto | right; apply H0; right; eauto].
  - apply H. destruct H0 as [[b [Hb Ha]]|[p [Hp Ha]]]; [left; eauto | right; eauto].
  - destruct H as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.singleton_iff in Hb. subst b. exact Ha.
    + fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - apply H; assumption.
  - apply H; assumption.
  - destruct H as [[b [Hb _]]|[p [Hp _]]]; fsetdec.
  - destruct H as [[b [Hb _]]|[p [Hp Ha]]]; [fsetdec|].
    rewrite AtomSetFacts.singleton_iff in Hp. subst p. exact Ha.
  - rewrite AtomSetFacts.union_iff.
    destruct H1 as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|Hb];
        [left; apply H; left; eauto | right; apply H0; left; eauto].
    + rewrite AtomSetFacts.union_iff in Hp. destruct Hp as [Hp|Hp];
        [left; apply H; right; eauto | right; apply H0; right; eauto].
  - (* row_Maybe *) rewrite !AtomSetFacts.union_iff.
    destruct H2 as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite !AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|[Hb|Hb]];
        [ left; apply H; left; eauto
        | right; left; apply H0; left; eauto
        | right; right; apply H1; left; eauto ].
    + rewrite !AtomSetFacts.union_iff in Hp. destruct Hp as [Hp|[Hp|Hp]];
        [ left; apply H; right; eauto
        | right; left; apply H0; right; eauto
        | right; right; apply H1; right; eauto ].
Qed.

Lemma frv_ap_in1 : forall st sr T a b,
  b `in` ftv_typ T -> a `in` frv_typ (st b) -> a `in` frv_typ (ap_typ st sr T).
Proof. intros. apply (proj1 frv_ap_in_mut). left. eauto. Qed.

Lemma frv_ap_in2 : forall st sr T a p,
  p `in` frv_typ T -> a `in` frv_row (sr p) -> a `in` frv_typ (ap_typ st sr T).
Proof. intros. apply (proj1 frv_ap_in_mut). right. eauto. Qed.

(* ====================================================================== *)
(* The casch->gen bridge: capture-avoiding scheme substitution of a       *)
(* generalization, with the renamed quantifiers chosen fresh for the      *)
(* target context's free vars (Ct/Cr) and fixed by the substitution, is   *)
(* exactly [gen]-equivalent to generalizing the substituted body over that *)
(* target context.  This is the piece that lets a substituted T-Let be    *)
(* reassembled: casch_inst supplies the instances, this lemma lines the    *)
(* scheme back up with [gen].                                             *)
(* ====================================================================== *)

Lemma casch_gen_sch_equiv : forall st sr g gr s Ct Cr,
  (forall a, g (g a) = a) -> (forall r, gr (gr r) = r) ->
  (forall a, a `in` ftv_sch s -> g a = a) ->
  (forall r, r `in` frv_sch s -> gr r = r) ->
  s_tq s [<=] ftv_typ (s_body s) ->
  s_rq s [<=] frv_typ (s_body s) ->
  (forall a, a `in` amap g (s_tq s) -> st a = typ_Var a) ->
  (forall r, r `in` amap gr (s_rq s) -> sr r = row_Var r) ->
  (forall a, a `in` amap g (s_tq s) -> a `notin` Ct) ->
  (forall r, r `in` amap gr (s_rq s) -> r `notin` Cr) ->
  (forall a, a `in` ftv_sch s -> ftv_typ (st a) [<=] Ct) ->
  (forall r, r `in` frv_sch s -> ftv_row (sr r) [<=] Ct) ->
  (forall a, a `in` ftv_sch s -> frv_typ (st a) [<=] Cr) ->
  (forall r, r `in` frv_sch s -> frv_row (sr r) [<=] Cr) ->
  sch_equiv (casch st sr g gr s)
            (Sch (AtomSetImpl.diff (ftv_typ (ap_typ st sr (ren_typ g gr (s_body s)))) Ct)
                 (AtomSetImpl.diff (frv_typ (ap_typ st sr (ren_typ g gr (s_body s)))) Cr)
                 (ap_typ st sr (ren_typ g gr (s_body s)))
                 (s_sk (casch st sr g gr s)) (s_rk (casch st sr g gr s))).
Proof.
  intros st sr g gr s Ct Cr Hgi Hgri Hgf Hgrf Hsubt Hsubr Hfx1 Hfx2 HfreshT HfreshR
    HcT_t HcT_r HcR_t HcR_r.
  set (B := ap_typ st sr (ren_typ g gr (s_body s))).
  (* ftv of the renamed body: b in ftv(ren body) <-> g b in ftv body *)
  assert (HFren : forall b, b `in` ftv_typ (ren_typ g gr (s_body s)) <-> g b `in` ftv_typ (s_body s)).
  { intro b. unfold ren_typ. apply (proj1 (Ftv_ren_mut g g gr Hgi Hgi)). }
  assert (HRren : forall b, b `in` frv_typ (ren_typ g gr (s_body s)) <-> gr b `in` frv_typ (s_body s)).
  { intro b. unfold ren_typ. apply (proj1 (Frv_ren_mut g gr gr Hgri Hgri)). }
  unfold sch_equiv, casch; simpl. split; [| split; [| split; [| split]]].
  - (* s_tq: amap g (s_tq s) [=] diff (ftv B) Ct *)
    apply AtomSetProperties.subset_antisym; intros a Ha.
    + (* amap g (s_tq s) subset diff (ftv B) Ct *)
      rewrite AtomSetFacts.diff_iff. split.
      * (* a in ftv B *)
        apply amap_in in Ha. destruct Ha as [q [Hq Hgq]].
        assert (Hqb : q `in` ftv_typ (s_body s)) by (apply Hsubt; exact Hq).
        assert (Hain : a `in` ftv_typ (ren_typ g gr (s_body s))).
        { apply HFren. rewrite <- Hgq. rewrite Hgi. exact Hqb. }
        assert (Hsta : st a = typ_Var a).
        { apply Hfx1. apply amap_in. exists q; auto. }
        unfold B. apply (ftv_ap_in1 st sr _ a a); [ exact Hain | rewrite Hsta; simpl; fsetdec ].
      * (* a notin Ct *)
        apply HfreshT. exact Ha.
    + (* diff (ftv B) Ct subset amap g (s_tq s) *)
      rewrite AtomSetFacts.diff_iff in Ha. destruct Ha as [HaB HaC].
      unfold B in HaB. apply ftv_ap_typ in HaB.
      destruct HaB as [[b [Hb Hast]]|[p [Hp Hast]]].
      * (* type-var contribution *)
        apply HFren in Hb. (* g b in ftv body *)
        destruct (AtomSetImpl.mem (g b) (s_tq s)) eqn:Em.
        -- apply AtomSetFacts.mem_iff in Em.
           (* b = g (g b) in amap g (s_tq s); st b = Var b; a in {b} *)
           assert (Hbamap : b `in` amap g (s_tq s)).
           { apply amap_in. exists (g b). split; [exact Em| apply Hgi]. }
           rewrite (Hfx1 b Hbamap) in Hast. simpl in Hast.
           assert (a = b) by fsetdec. subst a. exact Hbamap.
        -- apply AtomSetFacts.not_mem_iff in Em.
           assert (Hbf : g b `in` ftv_sch s)
             by (unfold ftv_sch; apply AtomSetImpl.diff_3; auto).
           (* g fixes ftv_sch s so g (g b) = g b, i.e. b = g b in ftv_sch s *)
           assert (Hgb : g (g b) = g b) by (apply Hgf; exact Hbf).
           rewrite Hgi in Hgb. (* b = g b *)
           assert (Hbf' : b `in` ftv_sch s) by (rewrite Hgb; exact Hbf).
           assert (ftv_typ (st b) [<=] Ct) by (apply HcT_t; exact Hbf').
           exfalso. apply HaC. fsetdec.
      * (* row-var contribution *)
        apply HRren in Hp. (* gr p in frv body *)
        destruct (AtomSetImpl.mem (gr p) (s_rq s)) eqn:Em.
        -- apply AtomSetFacts.mem_iff in Em.
           assert (Hpamap : p `in` amap gr (s_rq s)).
           { apply amap_in. exists (gr p). split; [exact Em| apply Hgri]. }
           rewrite (Hfx2 p Hpamap) in Hast. simpl in Hast. fsetdec.
        -- apply AtomSetFacts.not_mem_iff in Em.
           assert (Hpf : gr p `in` frv_sch s)
             by (unfold frv_sch; apply AtomSetImpl.diff_3; auto).
           assert (Hgp : gr (gr p) = gr p) by (apply Hgrf; exact Hpf).
           rewrite Hgri in Hgp.
           assert (Hpf' : p `in` frv_sch s) by (rewrite Hgp; exact Hpf).
           assert (ftv_row (sr p) [<=] Ct) by (apply HcT_r; exact Hpf').
           exfalso. apply HaC. fsetdec.
  - (* s_rq: amap gr (s_rq s) [=] diff (frv B) Cr *)
    apply AtomSetProperties.subset_antisym; intros a Ha.
    + rewrite AtomSetFacts.diff_iff. split.
      * apply amap_in in Ha. destruct Ha as [q [Hq Hgq]].
        assert (Hqb : q `in` frv_typ (s_body s)) by (apply Hsubr; exact Hq).
        assert (Hain : a `in` frv_typ (ren_typ g gr (s_body s))).
        { apply HRren. rewrite <- Hgq. rewrite Hgri. exact Hqb. }
        assert (Hsra : sr a = row_Var a).
        { apply Hfx2. apply amap_in. exists q; auto. }
        unfold B. apply (frv_ap_in2 st sr _ a a); [ exact Hain | rewrite Hsra; simpl; fsetdec ].
      * apply HfreshR. exact Ha.
    + rewrite AtomSetFacts.diff_iff in Ha. destruct Ha as [HaB HaC].
      unfold B in HaB. apply frv_ap_typ in HaB.
      destruct HaB as [[b [Hb Hast]]|[p [Hp Hast]]].
      * apply HFren in Hb.
        destruct (AtomSetImpl.mem (g b) (s_tq s)) eqn:Em.
        -- apply AtomSetFacts.mem_iff in Em.
           assert (Hbamap : b `in` amap g (s_tq s)).
           { apply amap_in. exists (g b). split; [exact Em| apply Hgi]. }
           rewrite (Hfx1 b Hbamap) in Hast. simpl in Hast. fsetdec.
        -- apply AtomSetFacts.not_mem_iff in Em.
           assert (Hbf : g b `in` ftv_sch s)
             by (unfold ftv_sch; apply AtomSetImpl.diff_3; auto).
           assert (Hgb : g (g b) = g b) by (apply Hgf; exact Hbf).
           rewrite Hgi in Hgb.
           assert (Hbf' : b `in` ftv_sch s) by (rewrite Hgb; exact Hbf).
           assert (frv_typ (st b) [<=] Cr) by (apply HcR_t; exact Hbf').
           exfalso. apply HaC. fsetdec.
      * apply HRren in Hp.
        destruct (AtomSetImpl.mem (gr p) (s_rq s)) eqn:Em.
        -- apply AtomSetFacts.mem_iff in Em.
           assert (Hpamap : p `in` amap gr (s_rq s)).
           { apply amap_in. exists (gr p). split; [exact Em| apply Hgri]. }
           rewrite (Hfx2 p Hpamap) in Hast. simpl in Hast.
           assert (a = p) by fsetdec. subst a. exact Hpamap.
        -- apply AtomSetFacts.not_mem_iff in Em.
           assert (Hpf : gr p `in` frv_sch s)
             by (unfold frv_sch; apply AtomSetImpl.diff_3; auto).
           assert (Hgp : gr (gr p) = gr p) by (apply Hgrf; exact Hpf).
           rewrite Hgri in Hgp.
           assert (Hpf' : p `in` frv_sch s) by (rewrite Hgp; exact Hpf).
           assert (frv_row (sr p) [<=] Cr) by (apply HcR_r; exact Hpf').
           exfalso. apply HaC. fsetdec.
  - reflexivity.
  - intros a Ha. reflexivity.
  - intros r Hr. reflexivity.
Qed.

(* ===================== context substitution relation ==================== *)

(* A scheme absorbs a substitution when, for every pair of kinding
   environments the substitution respects, each instance of the scheme maps to
   an instance of the substituted scheme. *)
Definition sch_subst (st:tsub) (sr:rsub) (s s':scheme) : Prop :=
  forall D D', kres D D' st -> rkres D D' sr -> forall W, inst D W s -> inst D' (ap_typ st sr W) s'.

(* The context-substitution relation: every binding of [G] has a corresponding
   binding in [G'] whose scheme absorbs the substituted instances.  [G'] may
   carry EXTRA bindings (so this relation also expresses weakening, with the
   identity substitution). *)
Definition ctx_subst (st:tsub) (sr:rsub) (G G':ctx) : Prop :=
  forall x s, binds x s G -> exists s', binds x s' G' /\ sch_subst st sr s s'.

Lemma ctx_subst_binds : forall st sr G G' x s,
  ctx_subst st sr G G' -> binds x s G ->
  exists s', binds x s' G' /\ sch_subst st sr s s'.
Proof. intros st sr G G' x s H Hb. apply H; exact Hb. Qed.

Lemma ctx_subst_cons : forall st sr x s0 s0' G G',
  sch_subst st sr s0 s0' -> ctx_subst st sr G G' ->
  ctx_subst st sr ((x ~ s0) ++ G) ((x ~ s0') ++ G').
Proof.
  intros st sr x s0 s0' G G' Hs0 HG y sy Hb.
  apply binds_cons_1 in Hb. destruct Hb as [[Hy Hsy]|Hb].
  - subst. exists s0'. split; [ apply binds_cons_2; reflexivity | exact Hs0 ].
  - destruct (HG y sy Hb) as [s' [Hb' Hss]]. exists s'. split; [ apply binds_cons_3; auto | exact Hss ].
Qed.

Lemma binds_ftv_sch : forall x s G, binds x s G -> ftv_sch s [<=] ftv_ctx G.
Proof.
  induction G as [|[y sy] G IH]; intros Hb; [inversion Hb|].
  apply binds_cons_1 in Hb. simpl. destruct Hb as [[Hy Hs]|Hb].
  - subst. fsetdec.
  - specialize (IH Hb). fsetdec.
Qed.

Lemma binds_frv_sch : forall x s G, binds x s G -> frv_sch s [<=] frv_ctx G.
Proof.
  induction G as [|[y sy] G IH]; intros Hb; [inversion Hb|].
  apply binds_cons_1 in Hb. simpl. destruct Hb as [[Hy Hs]|Hb].
  - subst. fsetdec.
  - specialize (IH Hb). fsetdec.
Qed.

Lemma sch_subst_mono : forall st sr T,
  sch_subst st sr (sch_mono T) (sch_mono (ap_typ st sr T)).
Proof.
  intros st sr T D D' Hk Hr W HW. apply inst_mono_eq in HW. subst W. apply inst_mono_self.
Qed.

(* a substitution fixing a scheme's free vars preserves its instances pointwise:
   this is the [T-Var] "re-chosen instance" with no renaming needed. *)
Lemma sch_subst_fix : forall st sr s,
  (forall a, a `in` ftv_sch s -> st a = typ_Var a) ->
  (forall r, r `in` frv_sch s -> sr r = row_Var r) ->
  lc_sub st sr ->
  sch_subst st sr s s.
Proof.
  intros st sr s Hf Hfr Hl D D' Hk Hkr W [pt [pr [Hpt [Hpr [HW [Hsat [Hrks Hpl]]]]]]].
  exists (fun a => if AtomSetImpl.mem a (s_tq s) then ap_typ st sr (pt a) else typ_Var a),
         (fun r => if AtomSetImpl.mem r (s_rq s) then ap_row st sr (pr r) else row_Var r).
  split; [| split; [| split; [| split; [| split]]]].
  - intros a Ha. destruct (AtomSetImpl.mem a (s_tq s)) eqn:Em;
      [apply AtomSetFacts.mem_iff in Em; contradiction|reflexivity].
  - intros r Hr. destruct (AtomSetImpl.mem r (s_rq s)) eqn:Em;
      [apply AtomSetFacts.mem_iff in Em; contradiction|reflexivity].
  - rewrite HW. rewrite ap_typ_comp. apply ap_typ_ext.
    + intros a Ha. unfold tcomp. destruct (AtomSetImpl.mem a (s_tq s)) eqn:Em.
      * reflexivity.
      * apply AtomSetFacts.not_mem_iff in Em.
        rewrite (Hpt a Em). simpl.
        assert (a `in` ftv_sch s) by (unfold ftv_sch; apply AtomSetImpl.diff_3; auto).
        rewrite (Hf a H). reflexivity.
    + intros r Hr. unfold rcomp. destruct (AtomSetImpl.mem r (s_rq s)) eqn:Em.
      * reflexivity.
      * apply AtomSetFacts.not_mem_iff in Em.
        rewrite (Hpr r Em). simpl.
        assert (r `in` frv_sch s) by (unfold frv_sch; apply AtomSetImpl.diff_3; auto).
        rewrite (Hfr r H). reflexivity.
  - intros a Ha. assert (Hm : AtomSetImpl.mem a (s_tq s) = true)
      by (apply AtomSetFacts.mem_iff; exact Ha).
    rewrite Hm. eapply sat_ap; [ exact Hk | exact Hkr | apply Hsat; exact Ha ].
  - intros r Hr. assert (Hm : AtomSetImpl.mem r (s_rq s) = true)
      by (apply AtomSetFacts.mem_iff; exact Hr).
    rewrite Hm. eapply rkok_ap; [ exact Hk | exact Hkr | apply Hrks; exact Hr ].
  - split.
    + intros a. cbv beta. destruct (AtomSetImpl.mem a (s_tq s));
        [ apply ap_lc; [ exact Hl | apply (proj1 Hpl) ] | exact I ].
    + intros r. cbv beta. destruct (AtomSetImpl.mem r (s_rq s));
        [ apply ap_lcr; [ exact Hl | apply (proj2 Hpl) ] | exact I ].
Qed.

(* A renaming has closed images. *)
Lemma lc_sub_ren : forall g gr, lc_sub (fun a => typ_Var (g a)) (fun r => row_Var (gr r)).
Proof. intros. split; intros; exact I. Qed.

Lemma ren_lc : forall g gr T k, lct k T -> lct k (ren_typ g gr T).
Proof. intros. unfold ren_typ. apply ap_lc; [ apply lc_sub_ren | assumption ]. Qed.

Lemma ren_lcr : forall g gr R k, lcr k R -> lcr k (ren_row g gr R).
Proof. intros. unfold ren_row. apply ap_lcr; [ apply lc_sub_ren | assumption ]. Qed.

(* The environment seen through a renaming of its atoms. *)
Definition dperm (g gr : atom -> atom) (D : denv) : denv :=
  DEnv (fun a => D (g a)) (fun r => drk D (gr r)).

Lemma kres_ren : forall g gr D, (forall a, g (g a) = a) ->
  kres D (dperm g gr D) (fun a => typ_Var (g a)).
Proof.
  intros g gr D Hi a. simpl. unfold dperm. simpl. rewrite Hi. apply finer_refl.
Qed.

Lemma rkres_ren : forall g gr D, (forall r, gr (gr r) = r) ->
  rkres D (dperm g gr D) (fun r => row_Var (gr r)).
Proof.
  intros g gr D Hi r. unfold rkok. simpl. unfold dperm. simpl. rewrite Hi.
  split; [ apply finer_refl | intros l H; exact H ].
Qed.

Lemma sat_ren : forall g gr D k T, (forall a, g (g a) = a) -> (forall r, gr (gr r) = r) ->
  sat D k T -> sat (dperm g gr D) k (ren_typ g gr T).
Proof.
  intros g gr D k T Hi Hri H. unfold ren_typ. eapply sat_ap; [ apply kres_ren; exact Hi | apply rkres_ren; exact Hri | exact H ].
Qed.

(* renaming a scheme's instance along a bijection fixing the scheme's free vars
   lands on another instance of the SAME scheme, in the renamed environment. *)
Lemma inst_ren_same : forall g gr D s W,
  (forall a, a `in` ftv_sch s -> g a = a) ->
  (forall r, r `in` frv_sch s -> gr r = r) ->
  (forall a, g (g a) = a) -> (forall r, gr (gr r) = r) ->
  inst D W s -> inst (dperm g gr D) (ren_typ g gr W) s.
Proof.
  intros g gr D s W Hgf Hgrf Hgi Hgri [pt [pr [Hpt [Hpr [HW [Hsat [Hrks Hpl]]]]]]].
  exists (fun a => if AtomSetImpl.mem a (s_tq s) then ren_typ g gr (pt a) else typ_Var a),
         (fun r => if AtomSetImpl.mem r (s_rq s) then ren_row g gr (pr r) else row_Var r).
  split; [| split; [| split; [| split; [| split]]]].
  - intros a Ha. destruct (AtomSetImpl.mem a (s_tq s)) eqn:Em;
      [apply AtomSetFacts.mem_iff in Em; contradiction|reflexivity].
  - intros r Hr. destruct (AtomSetImpl.mem r (s_rq s)) eqn:Em;
      [apply AtomSetFacts.mem_iff in Em; contradiction|reflexivity].
  - rewrite HW. unfold ren_typ at 1. rewrite ap_typ_comp. apply ap_typ_ext.
    + intros a Ha. unfold tcomp. destruct (AtomSetImpl.mem a (s_tq s)) eqn:Em.
      * unfold ren_typ. reflexivity.
      * apply AtomSetFacts.not_mem_iff in Em.
        rewrite (Hpt a Em). simpl. unfold rt.
        assert (a `in` ftv_sch s) by (unfold ftv_sch; apply AtomSetImpl.diff_3; auto).
        rewrite (Hgf a H). reflexivity.
    + intros r Hr. unfold rcomp. destruct (AtomSetImpl.mem r (s_rq s)) eqn:Em.
      * unfold ren_row. reflexivity.
      * apply AtomSetFacts.not_mem_iff in Em.
        rewrite (Hpr r Em). simpl. unfold rr.
        assert (r `in` frv_sch s) by (unfold frv_sch; apply AtomSetImpl.diff_3; auto).
        rewrite (Hgrf r H). reflexivity.
  - intros a Ha. assert (Hm : AtomSetImpl.mem a (s_tq s) = true)
      by (apply AtomSetFacts.mem_iff; exact Ha).
    rewrite Hm. apply sat_ren; [ exact Hgi | exact Hgri | apply Hsat; exact Ha ].
  - intros r Hr. assert (Hm : AtomSetImpl.mem r (s_rq s) = true)
      by (apply AtomSetFacts.mem_iff; exact Hr).
    rewrite Hm. unfold ren_row.
    eapply rkok_ap; [ apply kres_ren; exact Hgi | apply rkres_ren; exact Hgri | apply Hrks; exact Hr ].
  - split.
    + intros a. cbv beta. destruct (AtomSetImpl.mem a (s_tq s));
        [ apply ren_lc; apply (proj1 Hpl) | exact I ].
    + intros r. cbv beta. destruct (AtomSetImpl.mem r (s_rq s));
        [ apply ren_lcr; apply (proj2 Hpl) | exact I ].
Qed.

(* applying [st,sr] after a renaming equals applying the precomposed subst *)
Lemma ap_precomp : forall st sr g gr X,
  ap_typ (fun a => st (g a)) (fun r => sr (gr r)) X = ap_typ st sr (ren_typ g gr X).
Proof.
  intros. unfold ren_typ. rewrite ap_typ_comp. apply ap_typ_ext; intros.
  - unfold tcomp, rt. simpl. reflexivity.
  - unfold rcomp, rr. simpl. reflexivity.
Qed.

(* the context-substitution relation is stable under precomposing [st,sr] with a
   renaming that fixes the context's free variables. *)
Lemma ctx_subst_precomp : forall st sr g gr G G',
  (forall a, g (g a) = a) -> (forall r, gr (gr r) = r) ->
  ctx_subst st sr G G' ->
  (forall a, a `in` ftv_ctx G -> g a = a) ->
  (forall r, r `in` frv_ctx G -> gr r = r) ->
  ctx_subst (fun a => st (g a)) (fun r => sr (gr r)) G G'.
Proof.
  intros st sr g gr G G' Hgi Hgri HG Hgf Hgrf x s Hb.
  destruct (HG x s Hb) as [s' [Hb' Hss]]. exists s'. split; [exact Hb'|].
  intros D D' Hk Hkr W HW.
  assert (Hk2 : kres (dperm g gr D) D' st).
  { intros a. unfold dperm. unfold kres in Hk. specialize (Hk (g a)). simpl in Hk.
    simpl. rewrite Hgi in Hk. exact Hk. }
  assert (Hkr2 : rkres (dperm g gr D) D' sr).
  { intros r. unfold dperm. unfold rkres in Hkr. specialize (Hkr (gr r)). simpl in Hkr.
    simpl. rewrite Hgri in Hkr. exact Hkr. }
  rewrite ap_precomp. apply (Hss _ _ Hk2 Hkr2). apply inst_ren_same.
  - intros a Ha. apply Hgf.
    assert (ftv_sch s [<=] ftv_ctx G) by (eapply binds_ftv_sch; eauto). fsetdec.
  - intros r Hr. apply Hgrf.
    assert (frv_sch s [<=] frv_ctx G) by (eapply binds_frv_sch; eauto). fsetdec.
  - exact Hgi.
  - exact Hgri.
  - exact HW.
Qed.

(* ================= toward the general type/row substitution lemma ======== *)

Fixpoint lset (l:list atom) : atoms :=
  match l with [] => {} | a :: l' => add a (lset l') end.

Lemma lset_in : forall x l, x `in` lset l <-> List.In x l.
Proof.
  induction l as [|a l IH]; simpl.
  - split; [fsetdec | intros []].
  - rewrite AtomSetFacts.add_iff, IH. split.
    + intros [H|H]; [left; auto | right; auto].
    + intros [H|H]; [left; auto | right; auto].
Qed.

Lemma typing_uniq_mut :
  (forall D G e T, typing D G e T -> uniq G) /\
  (forall D G fs R, field_typing D G fs R -> uniq G).
Proof.
  apply typing_field_mutind; intros; auto;
    (* T_Abs / T_Let: recover uniq G from the cofinite body premise *)
    try (pick fresh x;
         match goal with
         | H : forall y, y `notin` ?L -> uniq _ |- uniq ?G =>
             specialize (H x ltac:(auto)); apply uniq_cons_iff in H; apply H
         end).
Qed.

Lemma typing_uniq : forall D G e T, typing D G e T -> uniq G.
Proof. intros. eapply (proj1 typing_uniq_mut); eauto. Qed.

Lemma ftv_sch_gen_sub : forall G T k rk, ftv_sch (gen G T k rk) [<=] ftv_ctx G.
Proof. intros. unfold ftv_sch, gen; simpl. fsetdec. Qed.

Lemma frv_sch_gen_sub : forall G T k rk, frv_sch (gen G T k rk) [<=] frv_ctx G.
Proof. intros. unfold frv_sch, gen; simpl. fsetdec. Qed.

(* a substitution fixing the context's free vars relates the context to itself *)
Lemma ctx_subst_fix : forall st sr G,
  (forall a, a `in` ftv_ctx G -> st a = typ_Var a) ->
  (forall r, r `in` frv_ctx G -> sr r = row_Var r) ->
  lc_sub st sr ->
  ctx_subst st sr G G.
Proof.
  intros st sr G Hf Hfr Hl x s Hb. exists s. split; [exact Hb|].
  apply sch_subst_fix; [ | | exact Hl ].
  - intros a Ha. apply Hf. assert (ftv_sch s [<=] ftv_ctx G) by (eapply binds_ftv_sch; eauto). fsetdec.
  - intros r Hr. apply Hfr. assert (frv_sch s [<=] frv_ctx G) by (eapply binds_frv_sch; eauto). fsetdec.
Qed.

(* identity-substitution instance of [ctx_subst] with extra target bindings:
   this is exactly what weakening needs. *)
Lemma ctx_subst_weaken : forall G G',
  (forall x s, binds x s G -> binds x s G') ->
  ctx_subst idt idr G G'.
Proof.
  intros G G' Hsub x s Hb. exists s. split; [ apply Hsub; exact Hb |].
  apply sch_subst_fix; [ intros; reflexivity | intros; reflexivity | apply lc_sub_id ].
Qed.

Lemma ftv_sch_mono : forall T, ftv_sch (sch_mono T) [=] ftv_typ T.
Proof. intro T. unfold ftv_sch, sch_mono; simpl. fsetdec. Qed.
Lemma frv_sch_mono : forall T, frv_sch (sch_mono T) [=] frv_typ T.
Proof. intro T. unfold frv_sch, sch_mono; simpl. fsetdec. Qed.

Definition tr_supp (st:tsub) (sr:rsub) (A:atoms) : Prop :=
  (forall a, a `notin` A -> st a = typ_Var a) /\
  (forall r, r `notin` A -> sr r = row_Var r) /\
  lc_sub st sr.

Definition tr_compat (st:tsub) (sr:rsub) (G G':ctx) : Prop :=
  (forall a, a `in` ftv_ctx G -> ftv_typ (st a) [<=] ftv_ctx G') /\
  (forall a, a `in` ftv_ctx G -> frv_typ (st a) [<=] frv_ctx G') /\
  (forall r, r `in` frv_ctx G -> ftv_row (sr r) [<=] ftv_ctx G') /\
  (forall r, r `in` frv_ctx G -> frv_row (sr r) [<=] frv_ctx G').

(* ======================================================================
   THE HARD IDEA: why polymorphic [let] makes substitution tricky
   ======================================================================

   Polymorphism.  In goat you can write
       let id = fun x => x in ... id 1 ... id true ...
   The same [id] is used at type "number -> number" and at "bool -> bool".
   That works because [let] gives its name a TYPE SCHEME, not a single type.
   A scheme is a type with some of its type variables marked "for any".  The
   scheme of [id] is "for any a, a -> a", and every use picks its own [a].
   Picking a concrete type for each "for any" variable is called INSTANTIATING
   the scheme ([inst]); the variables you are free to pick are the
   QUANTIFIED ones.

   Sorts.  A quantified variable also has a SORT: [Any] (any type), [Numeric]
   or [Literal] (Int or Float).  The scheme of [fun x => x + x] is
   "for any a of sort Numeric, a -> a", and an instance must pick a type of
   that sort.  A kinding environment [D] gives the sort of every free
   variable; the bound term of a [let] is typed under [D] extended with the
   sorts the scheme records ([ext]), so the variables it generalizes carry
   exactly those sorts while it is checked.  A substitution has to respect
   sorts: it must send a variable of sort [k] to a type of sort [k]
   ([kres]).

   Where do the quantified variables come from?  At [let x = e1 in e2], goat
   finds the type [T1] of [e1] and GENERALIZES it ([gen G T1 k]): every type
   variable in [T1] that does not also appear in the context [G] becomes
   "for any".  (Variables that do appear in [G] are pinned down by the rest
   of the program, so they may not be freely chosen.)

   Substitution.  Our big lemma is about SUBSTITUTION: plugging a type in for a
   type variable everywhere, say "replace a by number".  We want:
       if [e] has type [T] in context [G], then after substituting, [e] has
       the substituted type in the substituted context.
   Every typing rule is routine to push the substitution through, EXCEPT [T_Let],
   because of VARIABLE CAPTURE.

   Capture, with a small example.  Suppose a let-bound scheme is
   "for any b, b -> c" (here [c] is pinned, [b] is quantified).  Now substitute
   "replace c by b" (some type that happens to mention a variable named [b]).
   The naive result is "for any b, b -> b".  That is WRONG: the [b] we
   inserted was a different, ordinary variable, but the existing "for any b"
   grabbed it and turned "a function from b to the pinned c" into "the
   identity function type, usable at every type".  The quantifier CAPTURED
   a variable it should not own.

   The cure is a standard trick from logic (it is the same as renaming a
   loop variable, [for i] to [for j], when [i] clashes).  Before substituting
   we RENAME the quantified variables of each [let] to FRESH ones: names that
   do not occur anywhere in the substitution, the context, or the context we
   are moving to.  Once the quantified variables are fresh, the substitution
   cannot hit them and cannot capture anything.  The fresh names carry the
   sorts of the names they replace, in the extended environment the bound
   term is typed under; outside the finite support of the environment every
   name is [Any], so a name moved onto a fresh one never loses a constraint.

   How the proof carries this out.  Inside the [T_Let] case below we:
     (1) pick the renamings [g] (for type variables) and [gr] (for row
         variables, which stand for "the rest of a record's fields"), via
         [mk_rename], avoiding a set [Bav] of all names to stay away from;
     (2) show the renamed quantifiers really are fresh (the [HgF], [Hnc*]
         facts), so no capture;
     (3) show the substituted scheme [casch] still has all the instances the
         original had ([casch_inst]) -- uses of the let-bound name keep
         working;
     (4) show that scheme equals what [gen] would produce in the new context
         ([casch_gen_sch_equiv]) -- so the result is again a legal [T_Let].
   ====================================================================== *)

(* Adding a monomorphic binding keeps the substitution's image compatible. *)
Lemma tr_compat_cons_mono : forall st sr G G' x T,
  tr_compat st sr G G' ->
  tr_compat st sr ((x ~ sch_mono T) ++ G) ((x ~ sch_mono (ap_typ st sr T)) ++ G').
Proof.
  intros st sr G G' x T [HcT [HcFr [HcRt HcRfr]]].
  unfold tr_compat; simpl. repeat split.
  - intros a Ha. rewrite AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha].
    + rewrite ftv_sch_mono in Ha. intros z Hz. apply AtomSetFacts.union_iff. left.
      rewrite ftv_sch_mono. apply (ftv_ap_in1 st sr T z a); [ exact Ha | exact Hz ].
    + intros z Hz. apply AtomSetFacts.union_iff. right. apply (HcT a Ha). exact Hz.
  - intros a Ha. rewrite AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha].
    + rewrite ftv_sch_mono in Ha. intros z Hz. apply AtomSetFacts.union_iff. left.
      rewrite frv_sch_mono. apply (frv_ap_in1 st sr T z a); [ exact Ha | exact Hz ].
    + intros z Hz. apply AtomSetFacts.union_iff. right. apply (HcFr a Ha). exact Hz.
  - intros r Hr. rewrite AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr].
    + rewrite frv_sch_mono in Hr. intros z Hz. apply AtomSetFacts.union_iff. left.
      rewrite ftv_sch_mono. apply (ftv_ap_in2 st sr T z r); [ exact Hr | exact Hz ].
    + intros z Hz. apply AtomSetFacts.union_iff. right. apply (HcRt r Hr). exact Hz.
  - intros r Hr. rewrite AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr].
    + rewrite frv_sch_mono in Hr. intros z Hz. apply AtomSetFacts.union_iff. left.
      rewrite frv_sch_mono. apply (frv_ap_in2 st sr T z r); [ exact Hr | exact Hz ].
    + intros z Hz. apply AtomSetFacts.union_iff. right. apply (HcRfr r Hr). exact Hz.
Qed.

(* An environment that is [Any] outside [S] stays so, outside [S] and the
   extension's atoms, once extended; and a type that satisfies a sort keeps
   satisfying it when the extension only touches atoms outside [S]. *)
Lemma supp_ok_ext : forall D S V k, supp_ok D S -> supp_ok (ext D V k) (S `union` V).
Proof.
  intros D S V k Hs a Ha. unfold ext. simpl.
  destruct (AtomSetImpl.mem a V) eqn:Em.
  - apply AtomSetFacts.mem_iff in Em. exfalso. apply Ha. fsetdec.
  - apply Hs. fsetdec.
Qed.

Lemma supp_ok_extr : forall D S V rk, supp_ok D S -> supp_ok (extr D V rk) (S `union` V).
Proof.
  intros D S V rk Hs a Ha. unfold extr. simpl.
  destruct (AtomSetImpl.mem a V) eqn:Em.
  - apply AtomSetFacts.mem_iff in Em. exfalso. apply Ha. fsetdec.
  - apply Hs. fsetdec.
Qed.

Lemma supp_ok_sub : forall D S S2, supp_ok D S -> S [<=] S2 -> supp_ok D S2.
Proof. intros D S S2 H Hs a Ha. apply H. intro Hc. apply Ha. apply Hs. exact Hc. Qed.

Lemma supp_ok_ext2 : forall D S V k Vr rk, supp_ok D S ->
  supp_ok (extr (ext D V k) Vr rk) (S `union` V `union` Vr).
Proof.
  intros D S V k Vr rk H. eapply supp_ok_sub; [ apply supp_ok_extr; apply supp_ok_ext; exact H | ].
  intros a Ha. fsetdec.
Qed.

(* An environment that gives variables outside a finite support their
   unconstrained kind and then adds constraints on atoms of that support only
   keeps every satisfied sort and every lacked label: an atom it changes was
   unconstrained before. *)
Definition env_mono (D D2 : denv) : Prop :=
  (forall a, D2 a = D a \/ D a = k_Any) /\
  (forall r, drk D2 r = drk D r \/ drk D r = rk_any).

Lemma env_mono_trans : forall D1 D2 D3, env_mono D1 D2 -> env_mono D2 D3 -> env_mono D1 D3.
Proof.
  intros D1 D2 D3 [A1 B1] [A2 B2]. split.
  - intros a. destruct (A2 a) as [E2|E2]; destruct (A1 a) as [E1|E1];
      first [ (left; congruence) | (right; exact E1) | (right; congruence) ].
  - intros r. destruct (B2 r) as [E2|E2]; destruct (B1 r) as [E1|E1];
      first [ (left; congruence) | (right; exact E1) | (right; congruence) ].
Qed.

Lemma env_mono_ext_d : forall (D : denv) V (k : sort_fn), (forall a, a `in` V -> D a = k_Any) -> env_mono D (ext D V k).
Proof.
  intros D V k H. split.
  - intros a. unfold ext. simpl. destruct (AtomSetImpl.mem a V) eqn:Em.
    + apply AtomSetFacts.mem_iff in Em. right. apply H. exact Em.
    + left. reflexivity.
  - intros r. left. reflexivity.
Qed.

Lemma env_mono_extr_d : forall (D : denv) V (rk : rkind_fn), (forall r, r `in` V -> drk D r = rk_any) -> env_mono D (extr D V rk).
Proof.
  intros D V rk H. split.
  - intros a. left. reflexivity.
  - intros r. unfold extr. simpl. destruct (AtomSetImpl.mem r V) eqn:Em.
    + apply AtomSetFacts.mem_iff in Em. right. apply H. exact Em.
    + left. reflexivity.
Qed.

Lemma sat_mono_mut : forall D D2, env_mono D D2 ->
  (forall T, (forall k0, sat D k0 T -> sat D2 k0 T) /\
             (forall w j, spine_sat D w j T -> spine_sat D2 w j T)) /\
  (forall R k1, rsat D k1 R -> rsat D2 k1 R).
Proof.
  intros D D2 [Hd Hr]. apply typ_row_mutind; simpl.
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - split; intros; first [ assumption | exact I | contradiction ].
  - intros T1 [IH1 _] T2 [_ IH2]. split; [ intros; assumption | ].
    intros w j [Hu Hs']. split; [ intros Hc; exact (IH1 k_Eq (Hu Hc)) | exact (IH2 w (Datatypes.S j) Hs') ].
  - intros R IH. split; [ | intros; contradiction ]. intros k0. destruct k0; simpl;
      first [ (intros _; exact I) | (intros HH; contradiction) | exact (IH _) ].
  - intros a. split; [ | intros; contradiction ]. intros k0 H.
    destruct (Hd a) as [E|E]; [ rewrite E; exact H | rewrite E in H; inversion H; subst; apply finer_any ].
  - intros i. split; intros; first [ assumption | contradiction ].
  - intros B IH. split; [ | intros; contradiction ]. intros k0 Hs'. destruct k0; try exact I; try contradiction.
    exact (proj1 IH k_Eq Hs').
  - intros w A IH. split; [ | intros; contradiction ]. intros k0 Hs'. destruct k0; try exact I; try contradiction.
    exact (proj2 IH w 0 Hs').
  - intros k1 _. exact I.
  - intros r k1 Hs'. destruct (Hr r) as [E|E]; [ rewrite E; exact Hs' | rewrite E in Hs'; simpl in Hs'; inversion Hs'; subst; apply finer_any ].
  - intros l T [IHT _] R IHR k1 [Hs1 Hs2]. split; [ exact (IHT k1 Hs1) | exact (IHR k1 Hs2) ].
  - intros l P _ T [IHT _] R IHR k1 [Hs1 Hs2]. split;
      [ destruct Hs1 as [Hp | Hs1]; [ left; exact Hp | right; exact (IHT k1 Hs1) ]
      | exact (IHR k1 Hs2) ].
Qed.

Lemma sat_mono : forall D D2 k0 T, env_mono D D2 -> sat D k0 T -> sat D2 k0 T.
Proof. intros D D2 k0 T Hm H. exact (proj1 (proj1 (sat_mono_mut D D2 Hm) T) k0 H). Qed.

Lemma rsat_mono : forall D D2 k0 R, env_mono D D2 -> rsat D k0 R -> rsat D2 k0 R.
Proof. intros D D2 k0 R Hm H. exact (proj2 (sat_mono_mut D D2 Hm) R k0 H). Qed.

Lemma rlacksD_mono : forall D D2 l R, env_mono D D2 ->
  rlacksD D l R = true -> rlacksD D2 l R = true.
Proof.
  intros D D2 l R [_ Hr]. induction R as [|r|l' T R IH|l' P T R IH]; simpl; auto.
  - destruct (Hr r) as [E|E]; [ rewrite E; auto | rewrite E; simpl; intros H; discriminate H ].
  - intros H. apply Bool.andb_true_iff in H as [H1 H2]. rewrite H1. apply IH. exact H2.
  - destruct (Nat.eqb l l'); [ | exact IH ].
    intros H. apply Bool.andb_true_iff in H as [H1 H2]. rewrite H1. apply IH. exact H2.
Qed.

Lemma rkok_mono : forall D D2 K R, env_mono D D2 -> rkok D K R -> rkok D2 K R.
Proof.
  intros D D2 K R Hm [H1 H2]. split; [ eapply rsat_mono; eauto | ].
  intros l Hl. eapply rlacksD_mono; [ exact Hm | apply H2; exact Hl ].
Qed.

(* The renaming step shared by every binder that generalizes ([let] and a
   recursive group): rename the quantified variables of [gen G T1 k] to fresh
   names so the substitution cannot capture them (see the story above).  It
   returns the composed substitution under which the bound term is typed, the
   sorts that term is typed under, the substituted scheme, and the facts the
   body needs about it. *)
Lemma tsubst_gen_core : forall G T1 k rk st sr G' A D D' S S',
  supp_ok D S -> supp_ok D' S' -> kres D D' st -> rkres D D' sr ->
  ctx_subst st sr G G' -> tr_supp st sr A -> tr_compat st sr G G' ->
  exists (s' : scheme) (st1 : tsub) (sr1 : rsub) (A1 N Nr : atoms) (k' : sort_fn) (rk' : rkind_fn),
    kres (extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx G)) k)
              (AtomSetImpl.diff (frv_typ T1) (frv_ctx G)) rk)
         (extr (ext D' N k') Nr rk') st1 /\
    rkres (extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx G)) k)
                (AtomSetImpl.diff (frv_typ T1) (frv_ctx G)) rk)
          (extr (ext D' N k') Nr rk') sr1 /\
    ctx_subst st1 sr1 G G' /\ tr_supp st1 sr1 A1 /\ tr_compat st1 sr1 G G' /\
    N [=] AtomSetImpl.diff (ftv_typ (ap_typ st1 sr1 T1)) (ftv_ctx G') /\
    Nr [=] AtomSetImpl.diff (frv_typ (ap_typ st1 sr1 T1)) (frv_ctx G') /\
    supp_ok (extr (ext D' N k') Nr rk') (S' `union` N `union` Nr) /\
    sch_subst st sr (gen G T1 k rk) s' /\
    sch_equiv s' (gen G' (ap_typ st1 sr1 T1) k' rk') /\
    (forall x, tr_compat st sr ((x ~ gen G T1 k rk) ++ G) ((x ~ s') ++ G')) /\
    (forall H H', ctx_subst st sr H H' ->
       ftv_ctx H [<=] ftv_ctx G -> frv_ctx H [<=] frv_ctx G ->
       ctx_subst st1 sr1 H H') /\
    (forall a, a `in` ftv_ctx G -> st1 a = st a) /\
    (forall r, r `in` frv_ctx G -> sr1 r = sr r) /\
    (forall a, a `in` N -> exists b, b `in` AtomSetImpl.diff (ftv_typ T1) (ftv_ctx G) /\ k' a = k b).
Proof.
  intros G T1 k rk st sr G' A D D' S S' HS HS' Hk Hkr Hcs Hsupp Hcompat.
  destruct Hsupp as [HsuppT [HsuppR HlcS]].
  destruct Hcompat as [HcT [HcFr [HcRt HcRfr]]].
  set (s := gen G T1 k rk).
  set (V := AtomSetImpl.diff (ftv_typ T1) (ftv_ctx G)).
  assert (HsTQ : s_tq s = V) by reflexivity.
  (* [Bav] is the set of names to AVOID: everything mentioned by the
     substitution's support, by either context, or by either environment's
     support.  Anything outside it is fresh. *)
  set (Bav := A `union` ftv_ctx G `union` frv_ctx G `union` ftv_ctx G' `union` frv_ctx G'
              `union` S `union` S').
  destruct (mk_rename (s_tq s) Bav) as [g [Ng [Hginv [HgNB [HgNV [HgVN Hgfix]]]]]].
  destruct (mk_rename (s_rq s) Bav) as [gr [Ngr [Hgrinv [HgrNB [HgrNV [HgrVN Hgrfix]]]]]].
  assert (HgF : forall a, a `in` amap g (s_tq s) -> a `notin` Bav).
  { intros a Ha. apply amap_in in Ha. destruct Ha as [v [Hv Hgv]]. subst a.
    apply HgNB. apply HgVN. exact Hv. }
  assert (HgrF : forall p, p `in` amap gr (s_rq s) -> p `notin` Bav).
  { intros p Hp. apply amap_in in Hp. destruct Hp as [v [Hv Hgv]]. subst p.
    apply HgrNB. apply HgrVN. exact Hv. }
  assert (Hgfix' : forall C, C [<=] Bav -> (forall x, x `in` C -> x `notin` s_tq s) ->
                   forall c, c `in` C -> g c = c).
  { intros C Hsub Hdisj c Hc. apply Hgfix; [ apply Hdisj; exact Hc |].
    intro HInc. apply (HgNB c HInc). apply Hsub. exact Hc. }
  assert (Hgrfix' : forall C, C [<=] Bav -> (forall x, x `in` C -> x `notin` s_rq s) ->
                    forall c, c `in` C -> gr c = c).
  { intros C Hsub Hdisj c Hc. apply Hgrfix; [ apply Hdisj; exact Hc |].
    intro HInc. apply (HgrNB c HInc). apply Hsub. exact Hc. }
  assert (HQtdisj : forall x, x `in` ftv_ctx G -> x `notin` s_tq s).
  { intros x Hx. unfold s, gen, s_tq; simpl. fsetdec. }
  assert (HQrdisj : forall x, x `in` frv_ctx G -> x `notin` s_rq s).
  { intros x Hx. unfold s, gen, s_rq; simpl. fsetdec. }
  assert (HgfixG : forall c, c `in` ftv_ctx G -> g c = c).
  { apply Hgfix'; [ unfold Bav; fsetdec | exact HQtdisj ]. }
  assert (HgrfixG : forall c, c `in` frv_ctx G -> gr c = c).
  { apply Hgrfix'; [ unfold Bav; fsetdec | exact HQrdisj ]. }
  assert (HsubST : ftv_sch s [<=] ftv_ctx G) by (unfold s; apply ftv_sch_gen_sub).
  assert (HsubSR : frv_sch s [<=] frv_ctx G) by (unfold s; apply frv_sch_gen_sub).
  assert (HgfixS : forall a, a `in` ftv_sch s -> g a = a).
  { apply Hgfix'; [ unfold Bav; fsetdec | intros x Hx; apply HQtdisj; fsetdec ]. }
  assert (HgrfixS : forall r, r `in` frv_sch s -> gr r = r).
  { apply Hgrfix'; [ unfold Bav; fsetdec | intros x Hx; apply HQrdisj; fsetdec ]. }
  assert (HstQ : forall a, a `in` amap g (s_tq s) -> st a = typ_Var a).
  { intros a Ha. apply HsuppT. assert (a `notin` Bav) by (apply HgF; exact Ha).
    unfold Bav in H. fsetdec. }
  assert (HsrQ : forall r, r `in` amap gr (s_rq s) -> sr r = row_Var r).
  { intros r Hr. apply HsuppR. assert (r `notin` Bav) by (apply HgrF; exact Hr).
    unfold Bav in H. fsetdec. }
  assert (Hnc1 : forall a b, b `in` ftv_sch s -> a `in` amap g (s_tq s) -> a `notin` ftv_typ (st b)).
  { intros a b Hb Ha. assert (ftv_typ (st b) [<=] ftv_ctx G') by (apply HcT; fsetdec).
    assert (a `notin` Bav) by (apply HgF; exact Ha). unfold Bav in *. fsetdec. }
  assert (Hnc2 : forall a r, r `in` frv_sch s -> a `in` amap g (s_tq s) -> a `notin` ftv_row (sr r)).
  { intros a r Hr Ha. assert (ftv_row (sr r) [<=] ftv_ctx G') by (apply HcRt; fsetdec).
    assert (a `notin` Bav) by (apply HgF; exact Ha). unfold Bav in *. fsetdec. }
  assert (Hnc3 : forall p b, b `in` ftv_sch s -> p `in` amap gr (s_rq s) -> p `notin` frv_typ (st b)).
  { intros p b Hb Hp. assert (frv_typ (st b) [<=] frv_ctx G') by (apply HcFr; fsetdec).
    assert (p `notin` Bav) by (apply HgrF; exact Hp). unfold Bav in *. fsetdec. }
  assert (Hnc4 : forall p r, r `in` frv_sch s -> p `in` amap gr (s_rq s) -> p `notin` frv_row (sr r)).
  { intros p r Hr Hp. assert (frv_row (sr r) [<=] frv_ctx G') by (apply HcRfr; fsetdec).
    assert (p `notin` Bav) by (apply HgrF; exact Hp). unfold Bav in *. fsetdec. }
  assert (Hcaschinst : sch_subst st sr s (casch st sr g gr s)).
  { intros D1 D1' Hk1 Hkr1 W HW.
    exact (casch_inst st sr g gr s Hginv Hgrinv HgfixS HgrfixS HstQ HsrQ Hnc1 Hnc2 Hnc3 Hnc4 HlcS
             D1 D1' Hk1 Hkr1 W HW). }
  assert (Hbridge : sch_equiv (casch st sr g gr s)
                      (gen G' (ap_typ st sr (ren_typ g gr (s_body s))) (fun a => s_sk s (g a))
                              (fun r => s_rk s (gr r)))).
  { unfold gen. apply casch_gen_sch_equiv.
    - exact Hginv.
    - exact Hgrinv.
    - exact HgfixS.
    - exact HgrfixS.
    - unfold s, gen; simpl. fsetdec.
    - unfold s, gen; simpl. fsetdec.
    - exact HstQ.
    - exact HsrQ.
    - intros a Ha. assert (a `notin` Bav) by (apply HgF; exact Ha). unfold Bav in *. fsetdec.
    - intros r Hr. assert (r `notin` Bav) by (apply HgrF; exact Hr). unfold Bav in *. fsetdec.
    - intros a Ha. apply HcT. fsetdec.
    - intros r Hr. apply HcRt. fsetdec.
    - intros a Ha. apply HcFr. fsetdec.
    - intros r Hr. apply HcRfr. fsetdec. }
  set (A2 := A `union` s_tq s `union` lset Ng `union` s_rq s `union` lset Ngr).
  assert (HbodyT1 : s_body s = T1) by (unfold s, gen; reflexivity).
  set (NS := amap g V).
  set (NR := amap gr (s_rq s)).
  set (k' := fun a => k (g a)).
  set (rk' := fun r => rk (gr r)).
  assert (Hmono : env_mono D' (extr (ext D' NS k') NR rk')).
  { eapply env_mono_trans.
    - apply env_mono_ext_d. intros a Ha.
      assert (HaQ : a `in` amap g (s_tq s)) by (rewrite HsTQ; exact Ha).
      assert (Hb : a `notin` Bav) by (apply HgF; exact HaQ).
      assert (Hn : a `notin` S') by (unfold Bav in Hb; fsetdec). exact (proj1 (HS' a Hn)).
    - apply env_mono_extr_d. intros r Hr. rewrite ext_drk.
      assert (Hb : r `notin` Bav) by (apply HgrF; exact Hr).
      assert (Hn : r `notin` S') by (unfold Bav in Hb; fsetdec). exact (proj2 (HS' r Hn)). }
  assert (Hap1 : ap_typ (fun a : Atom.atom => st (g a)) (fun r : Atom.atom => sr (gr r)) T1
                 = ap_typ st sr (ren_typ g gr T1))
    by apply ap_precomp.
  assert (HEq : NS [=] AtomSetImpl.diff (ftv_typ (ap_typ (fun a : Atom.atom => st (g a)) (fun r : Atom.atom => sr (gr r)) T1))
                                        (ftv_ctx G')).
  { rewrite Hap1. exact (proj1 Hbridge). }
  exists (casch st sr g gr s), (fun a => st (g a)), (fun r => sr (gr r)), A2, NS, NR, k', rk'.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))).
  - (* the bound term's substitution respects the sorts *)
    intros a. rewrite extr_dsort.
    destruct (AtomSetImpl.mem a V) eqn:EV.
    + apply AtomSetFacts.mem_iff in EV.
      assert (HgaNS : g a `in` NS) by (apply amap_in; exists a; auto).
      assert (HgaQ : g a `in` amap g (s_tq s)) by (rewrite HsTQ; exact HgaNS).
      rewrite (ext_in D V k a EV). cbv beta. rewrite (HstQ (g a) HgaQ). cbn [sat].
      rewrite extr_dsort. rewrite (ext_in D' NS k' (g a) HgaNS). unfold k'. rewrite Hginv. apply finer_refl.
    + apply AtomSetFacts.not_mem_iff in EV.
      rewrite (ext_out D V k a EV).
      destruct (List.in_dec Atom.eq_dec a Ng) as [HIn|HNIn].
      * assert (a `notin` S) by (pose proof (HgNB a HIn); unfold Bav in H; fsetdec).
        rewrite (proj1 (HS a H)). apply sat_any.
      * assert (Hga : g a = a) by (apply Hgfix; [ rewrite HsTQ; exact EV | exact HNIn ]).
        cbv beta. rewrite Hga. eapply sat_mono; [ exact Hmono | apply Hk ].
  - (* the bound term's row substitution respects the kinds *)
    intros r. cbv beta.
    destruct (AtomSetImpl.mem r (s_rq s)) eqn:EV.
    + apply AtomSetFacts.mem_iff in EV.
      assert (HgrNR : gr r `in` NR) by (apply amap_in; exists r; auto).
      assert (HgrQ : gr r `in` amap gr (s_rq s)) by exact HgrNR.
      rewrite (extr_in _ _ _ r) by (unfold s, gen in EV; simpl in EV; exact EV).
      rewrite (HsrQ (gr r) HgrQ).
      pose proof (rkok_self (extr (ext D' NS k') NR rk') (gr r)) as Hself.
      rewrite (extr_in (ext D' NS k') NR rk' (gr r) HgrNR) in Hself. unfold rk' in Hself.
      rewrite Hgrinv in Hself. exact Hself.
    + apply AtomSetFacts.not_mem_iff in EV.
      rewrite (extr_out _ _ _ r) by (unfold s, gen in EV; simpl in EV; exact EV).
      rewrite ext_drk.
      destruct (List.in_dec Atom.eq_dec r Ngr) as [HIn|HNIn].
      * assert (r `notin` S) by (pose proof (HgrNB r HIn); unfold Bav in H; fsetdec).
        rewrite (proj2 (HS r H)). apply rkok_any.
      * assert (Hgr : gr r = r) by (apply Hgrfix; [ exact EV | exact HNIn ]).
        rewrite Hgr. eapply rkok_mono; [ exact Hmono | apply Hkr ].
  - (* the bound term is typed under the substitution run after the renaming *)
    apply ctx_subst_precomp; [ exact Hginv | exact Hgrinv | exact Hcs | exact HgfixG | exact HgrfixG ].
  - (* tr_supp *)
    split; [ | split ].
    + intros a Ha. unfold A2 in Ha.
      assert (g a = a).
      { apply Hgfix; [ fsetdec | ]. intro Hc. apply lset_in in Hc. fsetdec. }
      cbv beta. rewrite H. apply HsuppT. fsetdec.
    + intros r Hr. unfold A2 in Hr.
      assert (gr r = r).
      { apply Hgrfix; [ fsetdec | ]. intro Hc. apply lset_in in Hc. fsetdec. }
      cbv beta. rewrite H. apply HsuppR. fsetdec.
    + destruct HlcS as [Hl1 Hl2]. split; intros; [ apply Hl1 | apply Hl2 ].
  - (* tr_compat *)
    unfold tr_compat. repeat split.
    + intros a Ha. cbv beta. rewrite (HgfixG a Ha). apply HcT; exact Ha.
    + intros a Ha. cbv beta. rewrite (HgfixG a Ha). apply HcFr; exact Ha.
    + intros r Hr. cbv beta. rewrite (HgrfixG r Hr). apply HcRt; exact Hr.
    + intros r Hr. cbv beta. rewrite (HgrfixG r Hr). apply HcRfr; exact Hr.
  - exact HEq.
  - rewrite Hap1. exact (proj1 (proj2 Hbridge)).
  - exact (supp_ok_ext2 _ _ _ _ _ _ HS').
  - exact Hcaschinst.
  - (* the substituted scheme is the generalization over the target context *)
    rewrite Hap1. exact Hbridge.
  - (* tr_compat for the context extended with the substituted scheme *)
    intros x. unfold tr_compat; simpl. repeat split.
    + intros a Ha. intros z Hz. apply AtomSetFacts.union_iff. right.
      apply (HcT a); [ fold s; fsetdec | exact Hz ].
    + intros a Ha. intros z Hz. apply AtomSetFacts.union_iff. right.
      apply (HcFr a); [ fold s; fsetdec | exact Hz ].
    + intros r Hr. intros z Hz. apply AtomSetFacts.union_iff. right.
      apply (HcRt r); [ fold s; fsetdec | exact Hz ].
    + intros r Hr. intros z Hz. apply AtomSetFacts.union_iff. right.
      apply (HcRfr r); [ fold s; fsetdec | exact Hz ].
  - (* any context the substitution relates, inside [G], is related under the
       renamed substitution too *)
    intros H H' Hs HHt HHr.
    apply ctx_subst_precomp; [ exact Hginv | exact Hgrinv | exact Hs | | ].
    + intros a Ha. apply HgfixG. apply HHt. exact Ha.
    + intros r Hr. apply HgrfixG. apply HHr. exact Hr.
  - intros a Ha. cbv beta. rewrite (HgfixG a Ha). reflexivity.
  - intros r Hr. cbv beta. rewrite (HgrfixG r Hr). reflexivity.
  - (* a generalized variable of the target has the sort of the one it renames *)
    intros a Ha. apply amap_in in Ha. destruct Ha as [b [Hb Hab]].
    exists b. split; [ exact Hb | ]. subst a. unfold k'. rewrite Hginv. reflexivity.
Qed.

(* [tsubst_gen_core] for a [let] that keeps the variables of [Tm] monomorphic:
   the generalization is over the context extended with a binding of [Tm], and
   the bound term and the body are still typed over [G] alone, so the facts
   about [G] come from [tsubst_gen_core]'s agreement outputs. *)
Lemma tsubst_gen_pin : forall G Tm T1 k rk st sr G' A D D' S S',
  supp_ok D S -> supp_ok D' S' -> kres D D' st -> rkres D D' sr ->
  ctx_subst st sr G G' -> tr_supp st sr A -> tr_compat st sr G G' ->
  exists (s' : scheme) (st1 : tsub) (sr1 : rsub) (A1 N Nr : atoms) (k' : sort_fn) (rk' : rkind_fn),
    kres (extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G))) k)
              (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G))) rk)
         (extr (ext D' N k') Nr rk') st1 /\
    rkres (extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G))) k)
                (AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G))) rk)
          (extr (ext D' N k') Nr rk') sr1 /\
    ctx_subst st1 sr1 G G' /\ tr_supp st1 sr1 A1 /\ tr_compat st1 sr1 G G' /\
    N [=] AtomSetImpl.diff (ftv_typ (ap_typ st1 sr1 T1))
                           (ftv_ctx (pin_ctx (ap_typ st sr Tm) G')) /\
    Nr [=] AtomSetImpl.diff (frv_typ (ap_typ st1 sr1 T1))
                            (frv_ctx (pin_ctx (ap_typ st sr Tm) G')) /\
    supp_ok (extr (ext D' N k') Nr rk') (S' `union` N `union` Nr) /\
    sch_subst st sr (gen (pin_ctx Tm G) T1 k rk) s' /\
    sch_equiv s' (gen (pin_ctx (ap_typ st sr Tm) G') (ap_typ st1 sr1 T1) k' rk') /\
    (forall x, tr_compat st sr ((x ~ gen (pin_ctx Tm G) T1 k rk) ++ G) ((x ~ s') ++ G')) /\
    (forall a, a `in` N -> exists b, b `in` AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G)) /\ k' a = k b).
Proof.
  intros G Tm T1 k rk st sr G' A D D' S S' HS HS' Hk Hkr Hcs Hsupp Hcompat.
  pose proof (ctx_subst_cons st sr pin_name (sch_mono Tm) (sch_mono (ap_typ st sr Tm)) G G'
                (sch_subst_mono st sr Tm) Hcs) as Hcsp.
  pose proof (tr_compat_cons_mono st sr G G' pin_name Tm Hcompat) as Hcp.
  destruct (tsubst_gen_core (pin_ctx Tm G) T1 k rk st sr (pin_ctx (ap_typ st sr Tm) G') A D D' S S'
              HS HS' Hk Hkr Hcsp Hsupp Hcp)
    as [s' [st1 [sr1 [A1 [N [Nr [k' [rk' [Hk1 [Hkr1 [Hcs1 [Hsupp1 [Hcompat1 [HN [HNr [HS1 [Hsi [Hbr [Hcx [Hctx [Hagt [Hagr Hlk]]]]]]]]]]]]]]]]]]]]]].
  assert (HGp : ftv_ctx G [<=] ftv_ctx (pin_ctx Tm G)) by (rewrite ftv_pin_ctx; fsetdec).
  assert (HGpr : frv_ctx G [<=] frv_ctx (pin_ctx Tm G)) by (rewrite frv_pin_ctx; fsetdec).
  exists s', st1, sr1, A1, N, Nr, k', rk'.
  refine (conj Hk1 (conj Hkr1 (conj (Hctx G G' Hcs HGp HGpr) (conj Hsupp1 (conj _ (conj HN (conj HNr (conj HS1
            (conj Hsi (conj Hbr (conj _ Hlk))))))))))).
  - destruct Hcompat as [c1 [c2 [c3 c4]]].
    refine (conj _ (conj _ (conj _ _))).
    + intros a Ha. rewrite (Hagt a (HGp a Ha)). apply c1. exact Ha.
    + intros a Ha. rewrite (Hagt a (HGp a Ha)). apply c2. exact Ha.
    + intros r Hr. rewrite (Hagr r (HGpr r Hr)). apply c3. exact Hr.
    + intros r Hr. rewrite (Hagr r (HGpr r Hr)). apply c4. exact Hr.
  - intros x.
    destruct Hcompat as [c1 [c2 [c3 c4]]].
    destruct (Hcp) as [d1 [d2 [d3 d4]]].
    pose proof (ftv_sch_gen_sub (pin_ctx Tm G) T1 k rk) as Hsubt.
    pose proof (frv_sch_gen_sub (pin_ctx Tm G) T1 k rk) as Hsubr.
    set (T1' := ap_typ st1 sr1 T1).
    assert (Hs't : forall z, z `in` ftv_typ T1' -> z `in` ftv_ctx (pin_ctx (ap_typ st sr Tm) G') ->
                     z `in` ftv_sch s').
    { intros z Hz1 Hz2. apply (proj2 (Ftv_sch_equiv _ _ z Hbr)).
      unfold Ftv_sch, ftv_sch, gen; simpl. apply AtomSetFacts.diff_iff. split; [ exact Hz1 | ].
      intro Hq. apply AtomSetFacts.diff_iff in Hq. tauto. }
    assert (Hs'r : forall z, z `in` frv_typ T1' -> z `in` frv_ctx (pin_ctx (ap_typ st sr Tm) G') ->
                     z `in` frv_sch s').
    { intros z Hz1 Hz2. apply (proj2 (Frv_sch_equiv _ _ z Hbr)).
      unfold Frv_sch, frv_sch, gen; simpl. apply AtomSetFacts.diff_iff. split; [ exact Hz1 | ].
      intro Hq. apply AtomSetFacts.diff_iff in Hq. tauto. }
    unfold tr_compat; simpl. repeat split.
    + intros a Ha z Hz. apply AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha].
      * assert (HaT1 : a `in` ftv_typ T1)
          by (unfold ftv_sch, gen in Ha; simpl in Ha; apply AtomSetFacts.diff_iff in Ha; tauto).
        apply AtomSetFacts.union_iff. left. apply Hs't.
        -- unfold T1'. apply (ftv_ap_in1 st1 sr1 T1 z a HaT1). rewrite (Hagt a (Hsubt a Ha)). exact Hz.
        -- apply (d1 a (Hsubt a Ha) z Hz).
      * apply AtomSetFacts.union_iff. right. apply (c1 a Ha z Hz).
    + intros a Ha z Hz. apply AtomSetFacts.union_iff in Ha. destruct Ha as [Ha|Ha].
      * assert (HaT1 : a `in` ftv_typ T1)
          by (unfold ftv_sch, gen in Ha; simpl in Ha; apply AtomSetFacts.diff_iff in Ha; tauto).
        apply AtomSetFacts.union_iff. left. apply Hs'r.
        -- unfold T1'. apply (frv_ap_in1 st1 sr1 T1 z a HaT1). rewrite (Hagt a (Hsubt a Ha)). exact Hz.
        -- apply (d2 a (Hsubt a Ha) z Hz).
      * apply AtomSetFacts.union_iff. right. apply (c2 a Ha z Hz).
    + intros r Hr z Hz. apply AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr].
      * assert (HrT1 : r `in` frv_typ T1)
          by (unfold frv_sch, gen in Hr; simpl in Hr; apply AtomSetFacts.diff_iff in Hr; tauto).
        apply AtomSetFacts.union_iff. left. apply Hs't.
        -- unfold T1'. apply (ftv_ap_in2 st1 sr1 T1 z r HrT1). rewrite (Hagr r (Hsubr r Hr)). exact Hz.
        -- apply (d3 r (Hsubr r Hr) z Hz).
      * apply AtomSetFacts.union_iff. right. apply (c3 r Hr z Hz).
    + intros r Hr z Hz. apply AtomSetFacts.union_iff in Hr. destruct Hr as [Hr|Hr].
      * assert (HrT1 : r `in` frv_typ T1)
          by (unfold frv_sch, gen in Hr; simpl in Hr; apply AtomSetFacts.diff_iff in Hr; tauto).
        apply AtomSetFacts.union_iff. left. apply Hs'r.
        -- unfold T1'. apply (frv_ap_in2 st1 sr1 T1 z r HrT1). rewrite (Hagr r (Hsubr r Hr)). exact Hz.
        -- apply (d4 r (Hsubr r Hr) z Hz).
      * apply AtomSetFacts.union_iff. right. apply (c4 r Hr z Hz).
Qed.

(* The general type/row substitution lemma: a kind-respecting substitution
   applied to a derivation, with the context substituted capture-avoidingly
   ([ctx_subst]), finite support ([tr_supp]) and image-compatibility
   ([tr_compat]).  Every case is structural except T-Let, which freshens the
   let-generalized variables (via [mk_rename]) so that [casch_inst] supplies the
   instances and [casch_gen_sch_equiv] lines the scheme back up with [gen].

   What it says, in everyday terms: take any typing derivation, and a
   substitution [st]/[sr] ([st] replaces type variables, [sr] replaces row
   variables).  If the new context [G'] is what you get from [G] by applying
   the substitution (that is [ctx_subst]), and the substitution only changes
   a bounded set [A] of names ([tr_supp]) and does not smuggle in names that
   [G'] lacks ([tr_compat]), then the same term still type checks, at the
   substituted type.  [G'] may have extra variables; that slack is what lets
   the identity substitution double as WEAKENING (adding unused variables).

   The kinding environments [D] (source) and [D'] (target) enter in two
   places: the substitution must respect sorts ([kres D D' st]), and each
   environment is [Any] outside a finite set ([supp_ok]), which is what lets
   the fresh names a [let] is renamed onto carry any sort the original names
   had.

   How the proof goes: we prove it for every typing derivation by taking each
   typing rule in turn.  When the rule has sub-derivations, we may assume the
   lemma already holds for them: that assumption is the induction hypothesis,
   named [IH], [IH1], [IH2] below. *)
Lemma typing_tsubst_gen_mut :
  (forall D G e T, typing D G e T -> forall st sr G' D' A S S',
      uniq G' -> supp_ok D S -> supp_ok D' S' -> kres D D' st -> rkres D D' sr ->
      ctx_subst st sr G G' -> tr_supp st sr A -> tr_compat st sr G G' ->
      typing D' G' e (ap_typ st sr T)) /\
  (forall D G fs R, field_typing D G fs R -> forall st sr G' D' A S S',
      uniq G' -> supp_ok D S -> supp_ok D' S' -> kres D D' st -> rkres D D' sr ->
      ctx_subst st sr G G' -> tr_supp st sr A -> tr_compat st sr G G' ->
      field_typing D' G' fs (ap_row st sr R)).
Proof.
  apply typing_field_mutind.
  - (* T_Var: the scheme in [G] has a matching scheme in [G'], and any instance
       of the first becomes an instance of the second. *)
    intros D G x s T Hu Hb Hi st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat.
    destruct (ctx_subst_binds _ _ _ _ _ _ Hcs Hb) as [s' [Hb' Hss]].
    apply T_Var with (s := s'); auto. apply (Hss D D' Hk Hkr). exact Hi.
  - intros D G n T Hu Hs st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat.
    apply T_Num; auto. eapply sat_ap; eauto.
  - intros D G d Hu st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. apply T_Dec; auto.
  - intros D G Hu st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. apply T_True; auto.
  - intros D G Hu st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. apply T_False; auto.
  - (* T_Abs: the body is typed with the parameter added at [T1]. *)
    intros L D G e T1 T2 Ht IH st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl.
    apply T_Abs with (L := L `union` dom G'). intros x Hx.
    apply (IH x ltac:(fsetdec) st sr ((x ~ sch_mono (ap_typ st sr T1)) ++ G') D' A S S').
    + constructor; [ assumption | fsetdec ].
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + apply ctx_subst_cons; [ apply sch_subst_mono | assumption ].
    + assumption.
    + apply tr_compat_cons_mono; assumption.
  - (* T_App: nothing is bound. *)
    intros D G e1 e2 T1 T2 Ht1 IH1 Ht2 IH2 st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat.
    simpl in *. eapply T_App; [ eapply IH1 | eapply IH2 ]; eauto.
  - (* T_Let: the renaming of the generalized variables is [tsubst_gen_core];
       here we rebuild the [let] around it. *)
    intros L0 D G e1 e2 T1 T2 k rk Tm Hgv Hlp Ht1 IH1 Ht2 IH2 st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat.
    destruct (tsubst_gen_pin G Tm T1 k rk st sr G' A D D' S S' HS HS' Hk Hkr Hcs Hsupp Hcompat)
      as [s' [st1 [sr1 [A1 [N [Nr [k' [rk' [Hk1 [Hkr1 [Hcs1 [Hsupp1 [Hcompat1 [HN [HNr [HS1 [Hsi [Hbr [Hcx Hlk]]]]]]]]]]]]]]]]]]].
    apply T_Let with (L := L0 `union` dom G') (T1 := ap_typ st1 sr1 T1) (k := k') (rk := rk')
      (Tm := ap_typ st sr Tm);
      [ assumption | | | ].
    + intros Hc a Ha. apply (proj2 (HN a)) in Ha.
      destruct (Hlk a Ha) as [b [Hb Hkb]]. rewrite Hkb. apply Hlp; assumption.
    + eapply typing_pw.
      * apply (IH1 st1 sr1 G' (extr (ext D' N k') Nr rk') A1
                 (S `union` AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm G))
                    `union` AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm G)))
                 (S' `union` N `union` Nr)
                 Hu' (supp_ok_ext2 _ _ _ _ _ _ HS) HS1 Hk1 Hkr1 Hcs1 Hsupp1 Hcompat1).
      * apply denv_eq_trans with (D2 := extr (ext D' (AtomSetImpl.diff (ftv_typ (ap_typ st1 sr1 T1))
                                         (ftv_ctx (pin_ctx (ap_typ st sr Tm) G'))) k') Nr rk').
        -- apply extr_pw. apply ext_set_eq_d. exact HN.
        -- apply extr_set_eq. exact HNr.
    + intros x Hx.
      apply typing_sch_equiv_ctx with (G := (x ~ s') ++ G').
      * apply (IH2 x ltac:(fsetdec) st sr ((x ~ s') ++ G') D' A S S').
        -- constructor; [ assumption | fsetdec ].
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- apply ctx_subst_cons; [ exact Hsi | exact Hcs ].
        -- exact Hsupp.
        -- apply Hcx.
      * apply ctx_equiv_cons; [ exact Hbr | apply ctx_equiv_refl ].
  - (* T_LetMono: the binding is monomorphic, so it is the function case. *)
    intros L0 D G e1 e2 T1 T2 Ht1 IH1 Ht2 IH2 st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat.
    apply T_LetMono with (L := L0 `union` dom G') (T1 := ap_typ st sr T1);
      [ eapply IH1; eauto | ].
    intros x Hx.
    apply (IH2 x ltac:(fsetdec) st sr ((x ~ sch_mono (ap_typ st sr T1)) ++ G') D' A S S').
    + constructor; [ assumption | fsetdec ].
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + apply ctx_subst_cons; [ apply sch_subst_mono | assumption ].
    + assumption.
    + apply tr_compat_cons_mono; assumption.
  - (* T_Letrec: the members are typed with the group's record type [R]
       monomorphic, and the body with the group generalized like a [let]. *)
    intros L0 D G fs e2 R T k rk Hfg Hfs IHfs Ht2 IH2 st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat.
    destruct (tsubst_gen_core G (typ_Record R) k rk st sr G' A D D' S S' HS HS' Hk Hkr Hcs Hsupp Hcompat)
      as [s' [st1 [sr1 [A1 [N [Nr [k' [rk' [Hk1 [Hkr1 [Hcs1 [Hsupp1 [Hcompat1 [HN [HNr [HS1 [Hsi [Hbr [Hcx _]]]]]]]]]]]]]]]]]]].
    apply T_Letrec with (L := L0 `union` dom G') (R := ap_row st1 sr1 R) (k := k') (rk := rk');
      [ assumption | | ].
    + intros p Hp.
      eapply field_typing_pw.
      * apply (IHfs p ltac:(fsetdec) st1 sr1
                 ((p ~ sch_mono (ap_typ st1 sr1 (typ_Record R))) ++ G') (extr (ext D' N k') Nr rk') A1
                 (S `union` AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G)
                    `union` AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G))
                 (S' `union` N `union` Nr)).
        -- constructor; [ assumption | fsetdec ].
        -- apply supp_ok_ext2. exact HS.
        -- exact HS1.
        -- exact Hk1.
        -- exact Hkr1.
        -- apply ctx_subst_cons; [ apply sch_subst_mono | assumption ].
        -- assumption.
        -- apply tr_compat_cons_mono; assumption.
      * apply denv_eq_trans with (D2 := extr (ext D' (AtomSetImpl.diff (ftv_typ (ap_typ st1 sr1 (typ_Record R)))
                                         (ftv_ctx G')) k') Nr rk').
        -- apply extr_pw. apply ext_set_eq_d. exact HN.
        -- apply extr_set_eq. exact HNr.
    + intros p Hp.
      apply typing_sch_equiv_ctx with (G := (p ~ s') ++ G').
      * apply (IH2 p ltac:(fsetdec) st sr ((p ~ s') ++ G') D' A S S').
        -- constructor; [ assumption | fsetdec ].
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- apply ctx_subst_cons; [ exact Hsi | exact Hcs ].
        -- exact Hsupp.
        -- apply Hcx.
      * apply ctx_equiv_cons; [ exact Hbr | apply ctx_equiv_refl ].
  - (* T_Record *) intros D G fs R Ht IH Hnm st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl.
    apply T_Record; [ eapply IH; eauto | exact Hnm ].
  - (* T_Obj: the receiver row, the literal's row and every method's type are substituted alike *)
    intros D G fs R Rt Ht IH Hms st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl.
    pose proof (proj2 (proj2 Hsupp)) as Hl.
    apply T_Obj with (Rt := ap_row st sr Rt); [ eapply IH; eauto | ].
    rewrite <- (ap_row_tail_with st sr R Rt (field_typing_plain_spine _ _ _ _ Ht)).
    apply meths_shared_ap; assumption.
  - (* T_Proj *) intros D G e l T R Ht IH st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat.
    eapply T_Proj. simpl in IH. eapply IH; eauto.
  - (* T_Conv *) intros D G e T T' Ht IH Hte st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat.
    eapply T_ConvD; [ eapply IH; eauto | eapply teqD_ap; eauto ].
  - (* T_Unit *) intros D G Hu st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl. apply T_Unit; auto.
  - (* T_Str *) intros D G q Hu st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl. apply T_Str; auto.
  - (* T_If *)
    intros D G e1 e2 e3 T Ht1 IH1 Ht2 IH2 Ht3 IH3 st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat.
    simpl in *. eapply T_If; [ eapply IH1 | eapply IH2 | eapply IH3 ]; eauto.
  - (* T_ToFloat: the operand's sort carries over; [Float] is closed. *)
    intros D G e A0 Ht IH Hs st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl.
    eapply T_ToFloat; [ eapply IH; eauto | eapply sat_ap; eauto ].
  - (* T_Bin: the signature is stable under a kind-respecting substitution. *)
    intros D G e1 o e2 A0 B0 R0 Ht1 IH1 Ht2 IH2 Hs st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat.
    eapply T_Bin; [ eapply IH1; eauto | eapply IH2; eauto | eapply bin_sig_ap; eauto ].
  - (* T_Spread: the entry's types are substituted, its label is not. *)
    intros D G e1 l e2 P T R Ht1 IH1 Ht2 IH2 st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl.
    eapply T_Spread; [ eapply IH1; eauto | eapply IH2; eauto ].
  - (* T_SpreadL: a row that lacks the label by its kind still lacks it after a
       substitution that respects the kinds. *)
    intros D G e1 l e2 T R Ht1 IH1 Hl Ht2 IH2 st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl.
    eapply T_SpreadL; [ eapply IH1; eauto | eapply rlacksD_ap; eassumption | eapply IH2; eauto ].
  - (* T_Restrict: [rm] is stable under substitution. *)
    intros D G e l R0 T R Ht IH Hrm st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl.
    eapply T_Restrict; [ eapply IH; eauto | eapply rm_ap; eauto ].
  - (* T_Fold: the substitution commutes with unrolling because its images are closed *)
    intros D G e B Hlc Hg Ht IH st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl.
    pose proof (proj2 (proj2 Hsupp)) as Hl.
    apply T_Fold; [ apply ap_lc; assumption | apply guarded_ap; assumption | ].
    pose proof (ap_open st sr B 0 (typ_Mu B) Hl) as E. simpl in E. rewrite <- E.
    eapply IH; eauto.
  - (* T_Unfold *)
    intros D G e B Hlc Hg Ht IH st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat.
    pose proof (proj2 (proj2 Hsupp)) as Hl.
    rewrite (ap_open st sr B 0 (typ_Mu B) Hl).
    apply T_Unfold; [ apply ap_lc; assumption | apply guarded_ap; assumption | ].
    eapply IH; eauto.
  - (* T_Con: the payload type depends on the parameters alone, and a
       substitution acts on the parameters. *)
    intros D G w tg e Ts Hlt Ht IH st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl.
    rewrite ap_spine. apply T_Con; [ exact Hlt | ].
    rewrite <- ap_tag_payload. eapply IH; eauto.
  - (* T_Match: the arms bind the payload at its substituted type, as a
       function binds its parameter. *)
    intros L D G w Ts e ars T Ht IHe Hwf Harm IHarm Hdef IHdef
      st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat.
    apply T_Match with (L := L `union` dom G') (w := w) (Ts := map (ap_typ st sr) Ts).
    + rewrite <- ap_spine.
      change (typing D' G' e (ap_typ st sr (typ_Grp w (spine Ts)))).
      eapply IHe; eauto.
    + exact Hwf.
    + intros tg b Hf x Hx. rewrite <- ap_tag_payload.
      apply (IHarm tg b Hf x ltac:(fsetdec) st sr
               ((x ~ sch_mono (ap_typ st sr (tag_payload w Ts tg))) ++ G') D' A S S').
      * constructor; [ assumption | fsetdec ].
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * apply ctx_subst_cons; [ apply sch_subst_mono | assumption ].
      * assumption.
      * apply tr_compat_cons_mono; assumption.
    + intros e0 Hd. eapply IHdef; eauto.
  - intros D G Hu st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl. apply FT_nil; auto.
  - intros D G l e T fs R Ht1 IH1 Ht2 IH2 st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl.
    eapply FT_cons; [ eapply IH1 | eapply IH2 ]; eauto.
  - intros D G l e T fs R Ht1 IH1 Ht2 IH2 st sr G' D' A S S' Hu' HS HS' Hk Hkr Hcs Hsupp Hcompat. simpl.
    eapply FT_meth; [ eapply IH1 | eapply IH2 ]; eauto.
Qed.

Lemma kres_id : forall D, kres D D idt.
Proof. intros D a. unfold idt. simpl. apply finer_refl. Qed.

Lemma rkres_id : forall D, rkres D D idr.
Proof. intros D r. unfold idr. apply rkok_self. Qed.

(* L4 (weakening): inserting a middle block preserves typing -- the identity
   substitution into a larger context, via the general lemma.

   What it says: if a term is well typed in a context, it is still well typed
   when we add more (unrelated) variables to the context.  Extra information
   in the table can never make a term ill typed. *)
Lemma typing_weaken : forall D S E F G e T,
  supp_ok D S ->
  typing D (E ++ G) e T ->
  uniq (E ++ F ++ G) ->
  typing D (E ++ F ++ G) e T.
Proof.
  intros D S E F G e T HS Hty Hu.
  assert (Heq : ap_typ idt idr T = T) by (apply ap_typ_pointwise_id; reflexivity).
  rewrite <- Heq.
  apply (proj1 typing_tsubst_gen_mut D (E ++ G) e T Hty idt idr (E ++ F ++ G) D {} S S).
  - exact Hu.
  - exact HS.
  - exact HS.
  - apply kres_id.
  - apply rkres_id.
  - apply ctx_subst_weaken. intros x s Hb. apply binds_weaken; exact Hb.
  - split; [ intros a Ha; reflexivity | split; [ intros r Hr; reflexivity | apply lc_sub_id ] ].
  - unfold tr_compat. repeat split; intros a Ha.
    + unfold idt; simpl.
      assert (a `in` ftv_ctx (E ++ F ++ G)).
      { rewrite !ftv_ctx_app. rewrite ftv_ctx_app in Ha. fsetdec. }
      fsetdec.
    + unfold idt; simpl. fsetdec.
    + unfold idr; simpl. fsetdec.
    + unfold idr; simpl.
      assert (a `in` frv_ctx (E ++ F ++ G)).
      { rewrite !frv_ctx_app. rewrite frv_ctx_app in Ha. fsetdec. }
      fsetdec.
Qed.

(* A derivation moves between two kinding environments that agree on the
   variables the context and the type mention.  Any other variable the
   derivation uses internally is replaced by [Float] (a type variable) or by the
   empty row (a row variable): [Float] satisfies every sort and the empty row
   every kind.  Only variables in the finite support of the source environment
   can carry a constraint, so only those need replacing. *)
Lemma typing_denv_agree : forall D0 D Sd0 Sd ST SR G e T,
  typing D0 G e T -> supp_ok D0 Sd0 -> supp_ok D Sd ->
  ftv_ctx G [<=] ST -> ftv_typ T [<=] ST ->
  frv_ctx G [<=] SR -> frv_typ T [<=] SR ->
  (forall a, a `in` ST -> D a = D0 a) ->
  (forall r, r `in` SR -> drk D r = drk D0 r) ->
  typing D G e T.
Proof.
  intros D0 D Sd0 Sd ST SR G e T Hty HS0 HS HG HT HGr HTr Hag Hagr.
  set (A := AtomSetImpl.diff Sd0 ST).
  set (AR := AtomSetImpl.diff Sd0 SR).
  set (st := fun a : typvar => if AtomSetImpl.mem a A then typ_Float else typ_Var a).
  set (sr := fun r : rowvar => if AtomSetImpl.mem r AR then row_Empty else row_Var r).
  assert (Hst : forall a, a `in` ST -> st a = typ_Var a).
  { intros a Ha. unfold st. destruct (AtomSetImpl.mem a A) eqn:Em; [ | reflexivity ].
    apply AtomSetFacts.mem_iff in Em. unfold A in Em. apply AtomSetFacts.diff_iff in Em. tauto. }
  assert (Hsr : forall r, r `in` SR -> sr r = row_Var r).
  { intros r Hr. unfold sr. destruct (AtomSetImpl.mem r AR) eqn:Em; [ | reflexivity ].
    apply AtomSetFacts.mem_iff in Em. unfold AR in Em. apply AtomSetFacts.diff_iff in Em. tauto. }
  assert (Heq : ap_typ st sr T = T).
  { apply ap_typ_fix.
    - intros a Ha. apply Hst. apply HT. exact Ha.
    - intros r Hr. apply Hsr. apply HTr. exact Hr. }
  assert (Hlcst : lc_sub st sr).
  { split.
    - intros a. unfold st. destruct (AtomSetImpl.mem a A); exact I.
    - intros r. unfold sr. destruct (AtomSetImpl.mem r AR); exact I. }
  rewrite <- Heq.
  apply (proj1 typing_tsubst_gen_mut D0 G e T Hty st sr G D (A `union` AR) Sd0 Sd).
  - eapply typing_uniq; exact Hty.
  - exact HS0.
  - exact HS.
  - intros a. unfold st. destruct (AtomSetImpl.mem a A) eqn:Em.
    + simpl. exact I.
    + apply AtomSetFacts.not_mem_iff in Em. simpl.
      destruct (AtomSetImpl.mem a ST) eqn:Em2.
      * apply AtomSetFacts.mem_iff in Em2. rewrite (Hag a Em2). apply finer_refl.
      * assert (Hnot : a `notin` Sd0).
        { intro Hc. apply Em. unfold A. apply AtomSetFacts.diff_iff. split; [ exact Hc | ].
          apply AtomSetFacts.not_mem_iff in Em2. exact Em2. }
        rewrite (proj1 (HS0 a Hnot)). apply finer_any.
  - intros r. unfold sr. destruct (AtomSetImpl.mem r AR) eqn:Em.
    + split; [ simpl; exact I | intros l _; reflexivity ].
    + apply AtomSetFacts.not_mem_iff in Em.
      destruct (AtomSetImpl.mem r SR) eqn:Em2.
      * apply AtomSetFacts.mem_iff in Em2. rewrite <- (Hagr r Em2). apply rkok_self.
      * assert (Hnot : r `notin` Sd0).
        { intro Hc. apply Em. unfold AR. apply AtomSetFacts.diff_iff. split; [ exact Hc | ].
          apply AtomSetFacts.not_mem_iff in Em2. exact Em2. }
        rewrite (proj2 (HS0 r Hnot)). apply rkok_any.
  - apply ctx_subst_fix; [ | | exact Hlcst ].
    + intros a Ha. apply Hst. apply HG. exact Ha.
    + intros r Hr. apply Hsr. apply HGr. exact Hr.
  - split; [ | split ].
    + intros a Ha. unfold st. destruct (AtomSetImpl.mem a A) eqn:Em; [ | reflexivity ].
      apply AtomSetFacts.mem_iff in Em. exfalso. apply Ha. fsetdec.
    + intros r Hr. unfold sr. destruct (AtomSetImpl.mem r AR) eqn:Em; [ | reflexivity ].
      apply AtomSetFacts.mem_iff in Em. exfalso. apply Hr. fsetdec.
    + exact Hlcst.
  - unfold tr_compat. repeat split; intros a Ha.
    + rewrite (Hst a (HG a Ha)). simpl. fsetdec.
    + rewrite (Hst a (HG a Ha)). simpl. fsetdec.
    + rewrite (Hsr a (HGr a Ha)). simpl. fsetdec.
    + rewrite (Hsr a (HGr a Ha)). simpl. fsetdec.
Qed.

(* Every variable is [Any] in [d_any], so a substitution that fixes the
   context's variables and has finite support preserves typing there. *)
Lemma typing_tsubst_fix : forall G e T st sr A,
  typing d_any G e T -> tr_supp st sr A ->
  (forall a, a `in` ftv_ctx G -> st a = typ_Var a) ->
  (forall r, r `in` frv_ctx G -> sr r = row_Var r) ->
  typing d_any G e (ap_typ st sr T).
Proof.
  intros G e T st sr A Hty Hsupp Hfa Hfr.
  apply (proj1 typing_tsubst_gen_mut d_any G e T Hty st sr G d_any A {} {}).
  - eapply typing_uniq; exact Hty.
  - intros a _. split; reflexivity.
  - intros a _. split; reflexivity.
  - intros a. apply sat_any.
  - intros r. apply rkok_any.
  - apply ctx_subst_fix; [ assumption | assumption | exact (proj2 (proj2 Hsupp)) ].
  - exact Hsupp.
  - unfold tr_compat. repeat split.
    + intros a Ha. rewrite (Hfa a Ha). simpl. fsetdec.
    + intros a Ha. rewrite (Hfa a Ha). simpl. fsetdec.
    + intros r Hr. rewrite (Hfr r Hr). simpl. fsetdec.
    + intros r Hr. rewrite (Hfr r Hr). simpl. fsetdec.
Qed.

(* A value typed at the body of a generalization has every instance of the
   generalization.  The bound term is typed under the environment extended
   with the sorts and kinds the scheme records; the instance is typed in an
   environment that agrees with the ambient one on the context. *)
Lemma typing_inst_gen : forall D0 D Sd0 Sd G P v T1 k rk W,
  ftv_ctx G [<=] ftv_ctx P -> frv_ctx G [<=] frv_ctx P ->
  typing (extr (ext D0 (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx P)) k)
               (AtomSetImpl.diff (frv_typ T1) (frv_ctx P)) rk) G v T1 ->
  inst D W (gen P T1 k rk) ->
  supp_ok D0 Sd0 -> supp_ok D Sd ->
  (forall a, a `in` ftv_ctx G `union` ftv_sch (gen P T1 k rk) -> D a = D0 a) ->
  (forall r, r `in` frv_ctx G `union` frv_sch (gen P T1 k rk) -> drk D r = drk D0 r) ->
  typing D G v W.
Proof.
  intros D0 D Sd0 Sd G P v T1 k rk W HGP HGPr Hv [st [sr [Hst [Hsr [HW [Hsat [Hrks Hlcs]]]]]]] HS0 HS Hag Hagr.
  cbn [gen s_tq s_rq s_body s_sk s_rk] in Hst, Hsr, HW, Hsat, Hrks.
  set (V := AtomSetImpl.diff (ftv_typ T1) (ftv_ctx P)) in *.
  set (Vr := AtomSetImpl.diff (frv_typ T1) (frv_ctx P)) in *.
  set (A := AtomSetImpl.diff Sd0 (ftv_ctx G `union` ftv_sch (gen P T1 k rk))).
  set (AR := AtomSetImpl.diff Sd0 (frv_ctx G `union` frv_sch (gen P T1 k rk))).
  set (st' := fun a : typvar =>
        if AtomSetImpl.mem a V then st a
        else if AtomSetImpl.mem a A then typ_Float else typ_Var a).
  set (sr' := fun r : rowvar =>
        if AtomSetImpl.mem r Vr then sr r
        else if AtomSetImpl.mem r AR then row_Empty else row_Var r).
  assert (Hst'G : forall a, a `in` ftv_ctx G -> st' a = typ_Var a).
  { intros a Ha. unfold st'.
    destruct (AtomSetImpl.mem a V) eqn:E1.
    - apply AtomSetFacts.mem_iff in E1. unfold V in E1. apply AtomSetFacts.diff_iff in E1.
      exfalso. apply (proj2 E1). apply HGP. exact Ha.
    - destruct (AtomSetImpl.mem a A) eqn:E2; [ | reflexivity ].
      apply AtomSetFacts.mem_iff in E2. unfold A in E2. apply AtomSetFacts.diff_iff in E2.
      exfalso. apply (proj2 E2). apply AtomSetFacts.union_iff. left. exact Ha. }
  assert (Hsr'G : forall r, r `in` frv_ctx G -> sr' r = row_Var r).
  { intros r Hr. unfold sr'.
    destruct (AtomSetImpl.mem r Vr) eqn:E1.
    - apply AtomSetFacts.mem_iff in E1. unfold Vr in E1. apply AtomSetFacts.diff_iff in E1.
      exfalso. apply (proj2 E1). apply HGPr. exact Hr.
    - destruct (AtomSetImpl.mem r AR) eqn:E2; [ | reflexivity ].
      apply AtomSetFacts.mem_iff in E2. unfold AR in E2. apply AtomSetFacts.diff_iff in E2.
      exfalso. apply (proj2 E2). apply AtomSetFacts.union_iff. left. exact Hr. }
  assert (Hlc' : lc_sub st' sr').
  { split.
    - intros a. unfold st'.
      destruct (AtomSetImpl.mem a V); [ exact (proj1 Hlcs a) | ].
      destruct (AtomSetImpl.mem a A); exact I.
    - intros r. unfold sr'.
      destruct (AtomSetImpl.mem r Vr); [ exact (proj2 Hlcs r) | ].
      destruct (AtomSetImpl.mem r AR); exact I. }
  assert (HW' : W = ap_typ st' sr' T1).
  { rewrite HW. apply ap_typ_ext.
    - intros a Ha. unfold st'. destruct (AtomSetImpl.mem a V) eqn:E1; [ reflexivity | ].
      apply AtomSetFacts.not_mem_iff in E1.
      assert (HaS : a `in` ftv_ctx G `union` ftv_sch (gen P T1 k rk)).
      { apply AtomSetFacts.union_iff. right. unfold ftv_sch, gen; simpl.
        apply AtomSetFacts.diff_iff. split; [ exact Ha | exact E1 ]. }
      rewrite (Hst a ltac:(intro Hc; apply E1; exact Hc)).
      destruct (AtomSetImpl.mem a A) eqn:E2; [ | reflexivity ].
      apply AtomSetFacts.mem_iff in E2. unfold A in E2. apply AtomSetFacts.diff_iff in E2.
      exfalso. exact (proj2 E2 HaS).
    - intros r Hr. unfold sr'. destruct (AtomSetImpl.mem r Vr) eqn:E1; [ reflexivity | ].
      apply AtomSetFacts.not_mem_iff in E1.
      assert (HrS : r `in` frv_ctx G `union` frv_sch (gen P T1 k rk)).
      { apply AtomSetFacts.union_iff. right. unfold frv_sch, gen; simpl.
        apply AtomSetFacts.diff_iff. split; [ exact Hr | exact E1 ]. }
      rewrite (Hsr r ltac:(intro Hc; apply E1; exact Hc)).
      destruct (AtomSetImpl.mem r AR) eqn:E2; [ | reflexivity ].
      apply AtomSetFacts.mem_iff in E2. unfold AR in E2. apply AtomSetFacts.diff_iff in E2.
      exfalso. exact (proj2 E2 HrS). }
  rewrite HW'.
  apply (proj1 typing_tsubst_gen_mut _ G v T1 Hv st' sr' G D (V `union` A `union` Vr `union` AR)
           (Sd0 `union` V `union` Vr) Sd).
  - eapply typing_uniq; exact Hv.
  - exact (supp_ok_ext2 _ _ _ _ _ _ HS0).
  - exact HS.
  - intros a. rewrite extr_dsort. unfold st'. destruct (AtomSetImpl.mem a V) eqn:E1.
    + apply AtomSetFacts.mem_iff in E1. rewrite (ext_in D0 V k a E1). apply Hsat. exact E1.
    + apply AtomSetFacts.not_mem_iff in E1. rewrite (ext_out D0 V k a E1).
      destruct (AtomSetImpl.mem a A) eqn:E2.
      * simpl. exact I.
      * apply AtomSetFacts.not_mem_iff in E2. simpl.
        destruct (AtomSetProperties.In_dec a (ftv_ctx G `union` ftv_sch (gen P T1 k rk))) as [H|H].
        -- rewrite (Hag a H). apply finer_refl.
        -- assert (Hnot : a `notin` Sd0).
           { intro Hc. apply E2. unfold A. apply AtomSetFacts.diff_iff. split; assumption. }
           rewrite (proj1 (HS0 a Hnot)). apply finer_any.
  - intros r. unfold sr'. destruct (AtomSetImpl.mem r Vr) eqn:E1.
    + apply AtomSetFacts.mem_iff in E1. rewrite (extr_in _ _ _ r E1). apply Hrks. exact E1.
    + apply AtomSetFacts.not_mem_iff in E1. rewrite (extr_out _ _ _ r E1). rewrite ext_drk.
      destruct (AtomSetImpl.mem r AR) eqn:E2.
      * split; [ simpl; exact I | intros l _; reflexivity ].
      * apply AtomSetFacts.not_mem_iff in E2.
        destruct (AtomSetProperties.In_dec r (frv_ctx G `union` frv_sch (gen P T1 k rk))) as [H|H].
        -- rewrite <- (Hagr r H). apply rkok_self.
        -- assert (Hnot : r `notin` Sd0).
           { intro Hc. apply E2. unfold AR. apply AtomSetFacts.diff_iff. split; assumption. }
           rewrite (proj2 (HS0 r Hnot)). apply rkok_any.
  - apply ctx_subst_fix; [ | | exact Hlc' ].
    + intros a Ha. apply Hst'G. exact Ha.
    + intros r Hr. apply Hsr'G. exact Hr.
  - split; [ | split; [ | exact Hlc' ] ].
    + intros a Ha. unfold st'.
      destruct (AtomSetImpl.mem a V) eqn:E1.
      * apply AtomSetFacts.mem_iff in E1. exfalso. apply Ha. fsetdec.
      * destruct (AtomSetImpl.mem a A) eqn:E2; [ | reflexivity ].
        apply AtomSetFacts.mem_iff in E2. exfalso. apply Ha. fsetdec.
    + intros r Hr. unfold sr'.
      destruct (AtomSetImpl.mem r Vr) eqn:E1.
      * apply AtomSetFacts.mem_iff in E1. exfalso. apply Hr. fsetdec.
      * destruct (AtomSetImpl.mem r AR) eqn:E2; [ | reflexivity ].
        apply AtomSetFacts.mem_iff in E2. exfalso. apply Hr. fsetdec.
  - unfold tr_compat. repeat split; intros a Ha.
    + rewrite (Hst'G a Ha). simpl. fsetdec.
    + rewrite (Hst'G a Ha). simpl. fsetdec.
    + rewrite (Hsr'G a Ha). simpl. fsetdec.
    + rewrite (Hsr'G a Ha). simpl. fsetdec.
Qed.

(* ================================================================== *)
(* Term substitution (L6a/L6b).                                          *)
(*                                                                        *)
(* Now we switch from substituting TYPES for type variables to            *)
(* substituting a TERM for a term variable.  Calling a function           *)
(* [(fun x => body) v] steps to [body] with [v] plugged in for [x].       *)
(* The lemma says: if [body] is well typed assuming [x : s], and [v] has  *)
(* every instance of [s], then [body] with [v] in place of [x] is still   *)
(* well typed with the same type.  One lemma covers both uses: [s] is the *)
(* monomorphic scheme of a function parameter (L6a, for ST-Beta), or the  *)
(* generalization of a [let] (L6b, for ST-LetV and ST-Letrec).            *)
(*                                                                        *)
(* The kinding environment changes as the induction goes under a [let]    *)
(* (its bound term is typed under an extension), so the lemma speaks of   *)
(* every environment [D] that satisfies [Agree]; the extensions a [let]   *)
(* adds are on variables the context does not mention, and [Agree] must   *)
(* survive them.                                                          *)
(* ================================================================== *)

Lemma ftv_ctx_mid : forall G2 x s G1,
  ftv_ctx (G2 ++ G1) [<=] ftv_ctx (G2 ++ (x ~ s) ++ G1).
Proof. intros. rewrite !ftv_ctx_app. simpl. fsetdec. Qed.

Lemma frv_ctx_mid : forall G2 x s G1,
  frv_ctx (G2 ++ G1) [<=] frv_ctx (G2 ++ (x ~ s) ++ G1).
Proof. intros. rewrite !frv_ctx_app. simpl. fsetdec. Qed.

Lemma ftv_ctx_mid_pin : forall Tm G2 x s G1,
  ftv_ctx (pin_ctx Tm (G2 ++ G1)) [<=] ftv_ctx (pin_ctx Tm (G2 ++ (x ~ s) ++ G1)).
Proof. intros. rewrite !ftv_pin_ctx, !ftv_ctx_app. simpl. fsetdec. Qed.

Lemma frv_ctx_mid_pin : forall Tm G2 x s G1,
  frv_ctx (pin_ctx Tm (G2 ++ G1)) [<=] frv_ctx (pin_ctx Tm (G2 ++ (x ~ s) ++ G1)).
Proof. intros. rewrite !frv_pin_ctx, !frv_ctx_app. simpl. fsetdec. Qed.

Lemma typing_subst_gen_mut : forall x s u G1 (Agree : denv -> Prop),
  is_gen_value u = true -> lc u ->
  (forall D V k, (forall a, a `in` V -> a `notin` ftv_ctx G1 `union` ftv_sch s) ->
     Agree D -> Agree (ext D V k)) ->
  (forall D V rk, (forall r, r `in` V -> r `notin` frv_ctx G1 `union` frv_sch s) ->
     Agree D -> Agree (extr D V rk)) ->
  (forall D Sd T, supp_ok D Sd -> Agree D -> inst D T s -> typing D G1 u T) ->
  (forall D Gm e T, typing D Gm e T -> forall Sd, supp_ok D Sd -> Agree D ->
     forall G2, Gm = G2 ++ (x ~ s) ++ G1 ->
     typing D (G2 ++ G1) (subst_exp u x e) T) /\
  (forall D Gm fs R, field_typing D Gm fs R -> forall Sd, supp_ok D Sd -> Agree D ->
     forall G2, Gm = G2 ++ (x ~ s) ++ G1 ->
     field_typing D (G2 ++ G1) (subst_fields u x fs) R).
Proof.
  intros x s u G1 Agree Hgu Hlc Hext Hextr Hinst.
  (* the generalizing binders only see variables the whole context mentions *)
  assert (HV : forall G2 T V, V = AtomSetImpl.diff (ftv_typ T) (ftv_ctx (G2 ++ (x ~ s) ++ G1)) ->
                forall a, a `in` V -> a `notin` ftv_ctx G1 `union` ftv_sch s).
  { intros G2 T V HVe a Ha. subst V. apply AtomSetFacts.diff_iff in Ha as [_ Hn].
    rewrite ftv_ctx_app in Hn. simpl in Hn. fsetdec. }
  assert (HVp : forall Tm G2 T V,
            V = AtomSetImpl.diff (ftv_typ T) (ftv_ctx (pin_ctx Tm (G2 ++ (x ~ s) ++ G1))) ->
            forall a, a `in` V -> a `notin` ftv_ctx G1 `union` ftv_sch s).
  { intros Tm G2 T V HVe a Ha. subst V. apply AtomSetFacts.diff_iff in Ha as [_ Hn].
    rewrite ftv_pin_ctx, ftv_ctx_app in Hn. simpl in Hn. fsetdec. }
  assert (HVr : forall G2 T V, V = AtomSetImpl.diff (frv_typ T) (frv_ctx (G2 ++ (x ~ s) ++ G1)) ->
                forall r, r `in` V -> r `notin` frv_ctx G1 `union` frv_sch s).
  { intros G2 T V HVe r Hr. subst V. apply AtomSetFacts.diff_iff in Hr as [_ Hn].
    rewrite frv_ctx_app in Hn. simpl in Hn. fsetdec. }
  assert (HVrp : forall Tm G2 T V,
            V = AtomSetImpl.diff (frv_typ T) (frv_ctx (pin_ctx Tm (G2 ++ (x ~ s) ++ G1))) ->
            forall r, r `in` V -> r `notin` frv_ctx G1 `union` frv_sch s).
  { intros Tm G2 T V HVe r Hr. subst V. apply AtomSetFacts.diff_iff in Hr as [_ Hn].
    rewrite frv_pin_ctx, frv_ctx_app in Hn. simpl in Hn. fsetdec. }
  apply typing_field_mutind.
  - (* T_Var *) intros D G y s0 T Huq Hb Hi Sd HSd Hag G2 Heq; subst.
    destruct (y == x) as [Hx|Hx].
    + subst y.
      assert (s0 = s) as Hs by (eapply binds_mid_eq; [ exact Hb | exact Huq ]).
      subst s0. rewrite subst_self.
      apply (typing_weaken D Sd nil G2 G1 u T HSd).
      * simpl. exact (Hinst D Sd T HSd Hag Hi).
      * simpl_alist. solve_uniq.
    + rewrite subst_neq by congruence.
      apply T_Var with (s := s0);
        [ solve_uniq | eapply binds_remove_mid; [ exact Hb | congruence ] | exact Hi ].
  - (* T_Num *) intros D G n T Huq Hs Sd HSd Hag G2 Heq; subst. simpl. apply T_Num; [ solve_uniq | exact Hs ].
  - (* T_Dec *) intros D G d Huq Sd HSd Hag G2 Heq; subst. simpl. apply T_Dec. solve_uniq.
  - (* T_True *) intros D G Huq Sd HSd Hag G2 Heq; subst. simpl. apply T_True. solve_uniq.
  - (* T_False *) intros D G Huq Sd HSd Hag G2 Heq; subst. simpl. apply T_False. solve_uniq.
  - (* T_Abs *) intros L D G e T1 T2 Hr IH Sd HSd Hag G2 Heq; subst. simpl.
    apply T_Abs with (L := L `union` dom (G2 ++ G1) `union` {{x}} `union` fv_exp u).
    intros x0 Hx0.
    rewrite <- (subst_open_var e u x x0) by (first [ fsetdec | exact Hlc ]).
    rewrite_env (((x0 ~ sch_mono T1) ++ G2) ++ G1).
    apply (IH x0 ltac:(fsetdec) Sd HSd Hag ((x0 ~ sch_mono T1) ++ G2)). simpl_alist. reflexivity.
  - (* T_App *) intros D G e1 e2 T1 T2 Hr1 IH1 Hr2 IH2 Sd HSd Hag G2 Heq; subst. simpl. eapply T_App.
    + apply (IH1 Sd HSd Hag G2); reflexivity.
    + apply (IH2 Sd HSd Hag G2); reflexivity.
  - (* T_Let: removing [x] from the context shrinks it, so a type [Tm'] keeps
       the old context's variables pinned and the [let] quantifies what it did. *)
    intros L D G e1 e2 T1 T2 k rk Tm Hgv Hlp Hr1 IH1 Hr2 IH2 Sd HSd Hag G2 Heq; subst. simpl.
    destruct (repin Tm (G2 ++ (x ~ s) ++ G1) (G2 ++ G1)
                (ftv_ctx_mid G2 x s G1) (frv_ctx_mid G2 x s G1)) as [Tm' [HFe HRe]].
    set (V := AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm (G2 ++ (x ~ s) ++ G1)))).
    assert (HVe : forall a, a `in` AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm' (G2 ++ G1))) <-> a `in` V)
      by (intro a; unfold V; rewrite HFe; reflexivity).
    set (Vr := AtomSetImpl.diff (frv_typ T1) (frv_ctx (pin_ctx Tm (G2 ++ (x ~ s) ++ G1)))).
    apply T_Let with (L := L `union` dom (G2 ++ G1) `union` {{x}} `union` fv_exp u) (T1 := T1)
      (k := kup D V k) (rk := rkup D Vr rk) (Tm := Tm').
    + apply is_gen_subst; assumption.
    + apply lit_pinned_kup with (V := V); [ | intros a Ha; apply HVe; exact Ha ].
      intros Hc a Ha. apply (Hlp (let_open_subst u x e1 Hc) a Ha).
    + eapply typing_pw.
      * apply (IH1 (Sd `union` V `union` Vr) (supp_ok_ext2 _ _ _ _ _ _ HSd)
                 (Hextr _ Vr rk (HVrp Tm G2 T1 Vr eq_refl) (Hext D V k (HVp Tm G2 T1 V eq_refl) Hag)) G2);
          reflexivity.
      * apply denv_eq_trans with (D2 := extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx (pin_ctx Tm' (G2 ++ G1))))
                                         (kup D V k)) Vr rk).
        -- apply extr_pw. apply ext_kup_d. intros b Hb. apply HVe. exact Hb.
        -- apply extr_rkup; [ intros; reflexivity | ].
           intros b Hb. apply AtomSetFacts.diff_iff in Hb as [Hb Hc].
           apply AtomSetFacts.diff_iff. split; [ exact Hb | ].
           intro Hd. apply Hc. apply HRe. exact Hd.
    + intros x0 Hx0.
      rewrite <- (subst_open_var e2 u x x0) by (first [ fsetdec | exact Hlc ]).
      eapply typing_ftv_mono.
      * rewrite_env (((x0 ~ gen (pin_ctx Tm (G2 ++ (x ~ s) ++ G1)) T1 k rk) ++ G2) ++ G1).
        apply (IH2 x0 ltac:(fsetdec) Sd HSd Hag
                 ((x0 ~ gen (pin_ctx Tm (G2 ++ (x ~ s) ++ G1)) T1 k rk) ++ G2)).
        simpl_alist. reflexivity.
      * simpl_alist. apply ctx_more_gen_cons; [ | apply ctx_more_gen_refl ].
        apply gen_more_gen; [ rewrite HFe; fsetdec | exact HRe ].
  - (* T_LetMono *) intros L D G e1 e2 T1 T2 Hr1 IH1 Hr2 IH2 Sd HSd Hag G2 Heq; subst. simpl.
    apply T_LetMono with (L := L `union` dom (G2 ++ G1) `union` {{x}} `union` fv_exp u) (T1 := T1).
    + apply (IH1 Sd HSd Hag G2); reflexivity.
    + intros x0 Hx0.
      rewrite <- (subst_open_var e2 u x x0) by (first [ fsetdec | exact Hlc ]).
      rewrite_env (((x0 ~ sch_mono T1) ++ G2) ++ G1).
      apply (IH2 x0 ltac:(fsetdec) Sd HSd Hag ((x0 ~ sch_mono T1) ++ G2)). simpl_alist. reflexivity.
  - (* T_Letrec *) intros L D G fs e2 R T k rk Hfg Hfs IHfs Hr2 IH2 Sd HSd Hag G2 Heq; subst. simpl.
    set (V := AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx (G2 ++ (x ~ s) ++ G1))).
    set (Vr := AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx (G2 ++ (x ~ s) ++ G1))).
    apply T_Letrec with (L := L `union` dom (G2 ++ G1) `union` {{x}} `union` fv_exp u) (R := R)
      (k := kup D V k) (rk := rkup D Vr rk).
    + apply fn_group_subst; assumption.
    + intros p Hp.
      rewrite <- (subst_open_fields_var fs u x p) by (first [ fsetdec | exact Hlc ]).
      eapply field_typing_pw.
      * rewrite_env (((p ~ sch_mono (typ_Record R)) ++ G2) ++ G1).
        apply (IHfs p ltac:(fsetdec) (Sd `union` V `union` Vr) (supp_ok_ext2 _ _ _ _ _ _ HSd)
                 (Hextr _ Vr rk (HVr G2 (typ_Record R) Vr eq_refl)
                    (Hext D V k (HV G2 (typ_Record R) V eq_refl) Hag))
                 ((p ~ sch_mono (typ_Record R)) ++ G2)). simpl_alist. reflexivity.
      * apply denv_eq_trans with (D2 := extr (ext D (AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx (G2 ++ G1)))
                                         (kup D V k)) Vr rk).
        -- apply extr_pw. apply ext_kup_d. intros b Hb. apply AtomSetFacts.diff_iff in Hb as [Hb Hc].
           apply AtomSetFacts.diff_iff. split; [ exact Hb | ].
           intro Hd. apply Hc. apply ftv_ctx_mid. exact Hd.
        -- apply extr_rkup; [ intros; reflexivity | ].
           intros b Hb. apply AtomSetFacts.diff_iff in Hb as [Hb Hc].
           apply AtomSetFacts.diff_iff. split; [ exact Hb | ].
           intro Hd. apply Hc. apply frv_ctx_mid. exact Hd.
    + intros p Hp.
      rewrite <- (subst_open_var e2 u x p) by (first [ fsetdec | exact Hlc ]).
      eapply typing_ftv_mono.
      * rewrite_env (((p ~ gen (G2 ++ (x ~ s) ++ G1) (typ_Record R) k rk) ++ G2) ++ G1).
        apply (IH2 p ltac:(fsetdec) Sd HSd Hag
                 ((p ~ gen (G2 ++ (x ~ s) ++ G1) (typ_Record R) k rk) ++ G2)).
        simpl_alist. reflexivity.
      * simpl_alist. apply ctx_more_gen_cons; [ | apply ctx_more_gen_refl ].
        apply gen_more_gen; rewrite ?ftv_ctx_app, ?frv_ctx_app; simpl; fsetdec.
  - (* T_Record *) intros D G fs R Hr IH Hnm Sd HSd Hag G2 Heq; subst. simpl. apply T_Record; [ | rewrite (no_meth_marks _ _ (marks_subst_fields fs u x)); exact Hnm ].
    apply (IH Sd HSd Hag G2); reflexivity.
  - (* T_Obj *) intros D G fs R Rt Hr IH Hms Sd HSd Hag G2 Heq; subst. simpl. apply T_Obj with (Rt := Rt); [ | eapply meths_shared_marks; [ exact Hms | symmetry; apply marks_subst_fields ] ].
    apply (IH Sd HSd Hag G2); reflexivity.
  - (* T_Proj *) intros D G e l T R Hr IH Sd HSd Hag G2 Heq; subst. simpl. eapply T_Proj.
    apply (IH Sd HSd Hag G2); reflexivity.
  - (* T_ConvD *) intros D G e T T' Hr IH Hteq Sd HSd Hag G2 Heq; subst.
    eapply T_ConvD; [ apply (IH Sd HSd Hag G2); reflexivity | exact Hteq ].
  - (* T_Unit *) intros D G Huq Sd HSd Hag G2 Heq; subst. simpl. apply T_Unit. solve_uniq.
  - (* T_Str *) intros D G q Huq Sd HSd Hag G2 Heq; subst. simpl. apply T_Str. solve_uniq.
  - (* T_If *) intros D G e1 e2 e3 T Hr1 IH1 Hr2 IH2 Hr3 IH3 Sd HSd Hag G2 Heq; subst. simpl.
    eapply T_If; [ apply (IH1 Sd HSd Hag G2) | apply (IH2 Sd HSd Hag G2) | apply (IH3 Sd HSd Hag G2) ];
      reflexivity.
  - (* T_ToFloat *) intros D G e A0 Hr IH Hs Sd HSd Hag G2 Heq; subst. simpl.
    eapply T_ToFloat; [ apply (IH Sd HSd Hag G2); reflexivity | exact Hs ].
  - (* T_Bin *) intros D G e1 o e2 A0 B0 R0 Hr1 IH1 Hr2 IH2 Hs Sd HSd Hag G2 Heq; subst. simpl.
    eapply T_Bin; [ apply (IH1 Sd HSd Hag G2) | apply (IH2 Sd HSd Hag G2) | exact Hs ]; reflexivity.
  - (* T_Spread *) intros D G e1 l e2 P T R Hr1 IH1 Hr2 IH2 Sd HSd Hag G2 Heq; subst. simpl.
    eapply T_Spread; [ apply (IH1 Sd HSd Hag G2) | apply (IH2 Sd HSd Hag G2) ]; reflexivity.
  - (* T_SpreadL *) intros D G e1 l e2 T R Hr1 IH1 Hl Hr2 IH2 Sd HSd Hag G2 Heq; subst. simpl.
    eapply T_SpreadL; [ apply (IH1 Sd HSd Hag G2) | exact Hl | apply (IH2 Sd HSd Hag G2) ]; reflexivity.
  - (* T_Restrict *) intros D G e l R0 T R Hr IH Hrm Sd HSd Hag G2 Heq; subst. simpl.
    eapply T_Restrict; [ apply (IH Sd HSd Hag G2); reflexivity | exact Hrm ].
  - (* T_Fold *) intros D G e B Hlc0 Hg Hr IH Sd HSd Hag G2 Heq; subst. simpl.
    eapply T_Fold; [ exact Hlc0 | exact Hg | apply (IH Sd HSd Hag G2); reflexivity ].
  - (* T_Unfold *) intros D G e B Hlc0 Hg Hr IH Sd HSd Hag G2 Heq; subst. simpl.
    eapply T_Unfold; [ exact Hlc0 | exact Hg | apply (IH Sd HSd Hag G2); reflexivity ].
  - (* T_Con *) intros D G w tg e Ts Hlt Hr IH Sd HSd Hag G2 Heq; subst. simpl.
    eapply T_Con; [ exact Hlt | apply (IH Sd HSd Hag G2); reflexivity ].
  - (* T_Match: each arm is substituted under its binder, as a function body
       is; the arms of the result are the substituted arms, with the same
       tags, so the exhaustiveness premise carries over. *)
    intros L D G w Ts e ars T Ht IHe Hwf Harm IHarm Hdef IHdef Sd HSd Hag G2 Heq; subst. simpl.
    apply T_Match with (L := L `union` dom (G2 ++ G1) `union` {{x}} `union` fv_exp u)
      (w := w) (Ts := Ts).
    + apply (IHe Sd HSd Hag G2); reflexivity.
    + apply arms_wf_subst. exact Hwf.
    + intros tg b Hf x0 Hx0.
      destruct (arms_find_subst_inv _ _ _ _ _ Hf) as [b0 [-> Hf0]].
      rewrite <- (subst_open_var b0 u x x0) by (first [ fsetdec | exact Hlc ]).
      rewrite_env (((x0 ~ sch_mono (tag_payload w Ts tg)) ++ G2) ++ G1).
      apply (IHarm tg b0 Hf0 x0 ltac:(fsetdec) Sd HSd Hag
               ((x0 ~ sch_mono (tag_payload w Ts tg)) ++ G2)).
      simpl_alist. reflexivity.
    + intros e0 Hd.
      destruct (arms_default_subst_inv _ _ _ _ Hd) as [e1 [-> Hd0]].
      apply (IHdef e1 Hd0 Sd HSd Hag G2); reflexivity.
  - (* FT_nil *) intros D G Huq Sd HSd Hag G2 Heq; subst. simpl. apply FT_nil. solve_uniq.
  - (* FT_cons *) intros D G l e T fs R Hr1 IH1 Hr2 IH2 Sd HSd Hag G2 Heq; subst. simpl. eapply FT_cons.
    + apply (IH1 Sd HSd Hag G2); reflexivity.
    + apply (IH2 Sd HSd Hag G2); reflexivity.
  - (* FT_meth *) intros D G l e T fs R Hr1 IH1 Hr2 IH2 Sd HSd Hag G2 Heq; subst. simpl. eapply FT_meth.
    + apply (IH1 Sd HSd Hag G2); reflexivity.
    + apply (IH2 Sd HSd Hag G2); reflexivity.
Qed.

(* L6a: the parameter of a function is replaced by a value of its type. *)
Lemma typing_subst : forall D Sd G x U e T u,
  supp_ok D Sd ->
  typing D ((x ~ sch_mono U) ++ G) e T ->
  is_gen_value u = true ->
  typing D G u U ->
  typing D G (subst_exp u x e) T.
Proof.
  intros D Sd G x U e T u HS Hty Hgu Hu.
  set (S0 := ftv_ctx G `union` ftv_sch (sch_mono U)).
  set (SR := frv_ctx G `union` frv_sch (sch_mono U)).
  refine (proj1 (typing_subst_gen_mut x (sch_mono U) u G
                   (fun D' => (forall a, a `in` S0 -> D' a = D a) /\ (forall r, r `in` SR -> drk D' r = drk D r))
                   Hgu (typing_regular _ _ _ _ Hu) _ _ _) D _ e T Hty Sd HS _ nil eq_refl).
  - intros D' V k Hv [Hag Hagr]. split.
    + intros a Ha. rewrite ext_out; [ apply Hag; exact Ha | intro Hav; exact (Hv a Hav Ha) ].
    + intros r Hr. rewrite ext_drk. apply Hagr. exact Hr.
  - intros D' V rk Hv [Hag Hagr]. split.
    + intros a Ha. rewrite extr_dsort. apply Hag. exact Ha.
    + intros r Hr. rewrite extr_out; [ apply Hagr; exact Hr | intro Hrv; exact (Hv r Hrv Hr) ].
  - intros D' Sd' T' HS' [Hag Hagr] Hi. apply inst_mono_eq in Hi. subst T'.
    eapply typing_denv_agree with (D0 := D) (Sd0 := Sd) (ST := S0) (SR := SR);
      [ exact Hu | exact HS | exact HS' | | | | | exact Hag | exact Hagr ].
    + unfold S0. fsetdec.
    + unfold S0. rewrite ftv_sch_mono. fsetdec.
    + unfold SR. fsetdec.
    + unfold SR. rewrite frv_sch_mono. fsetdec.
  - split; intros; reflexivity.
Qed.

Lemma field_typing_subst : forall D Sd G x U fs R u,
  supp_ok D Sd ->
  field_typing D ((x ~ sch_mono U) ++ G) fs R ->
  is_gen_value u = true ->
  typing D G u U ->
  field_typing D G (subst_fields u x fs) R.
Proof.
  intros D Sd G x U fs R u HS Hty Hgu Hu.
  set (S0 := ftv_ctx G `union` ftv_sch (sch_mono U)).
  set (SR := frv_ctx G `union` frv_sch (sch_mono U)).
  refine (proj2 (typing_subst_gen_mut x (sch_mono U) u G
                   (fun D' => (forall a, a `in` S0 -> D' a = D a) /\ (forall r, r `in` SR -> drk D' r = drk D r))
                   Hgu (typing_regular _ _ _ _ Hu) _ _ _) D _ fs R Hty Sd HS _ nil eq_refl).
  - intros D' V k Hv [Hag Hagr]. split.
    + intros a Ha. rewrite ext_out; [ apply Hag; exact Ha | intro Hav; exact (Hv a Hav Ha) ].
    + intros r Hr. rewrite ext_drk. apply Hagr. exact Hr.
  - intros D' V rk Hv [Hag Hagr]. split.
    + intros a Ha. rewrite extr_dsort. apply Hag. exact Ha.
    + intros r Hr. rewrite extr_out; [ apply Hagr; exact Hr | intro Hrv; exact (Hv r Hrv Hr) ].
  - intros D' Sd' T' HS' [Hag Hagr] Hi. apply inst_mono_eq in Hi. subst T'.
    eapply typing_denv_agree with (D0 := D) (Sd0 := Sd) (ST := S0) (SR := SR);
      [ exact Hu | exact HS | exact HS' | | | | | exact Hag | exact Hagr ].
    + unfold S0. fsetdec.
    + unfold S0. rewrite ftv_sch_mono. fsetdec.
    + unfold SR. fsetdec.
    + unfold SR. rewrite frv_sch_mono. fsetdec.
  - split; intros; reflexivity.
Qed.

(* L6b: a [let]-bound name is replaced by its value.  The bound term was typed
   under the environment extended with the sorts and kinds the scheme records,
   and every instance of the scheme is typed through [typing_inst_gen]. *)
Lemma typing_subst_poly : forall D Sd G P x T1 k rk e T2 v,
  ftv_ctx G [<=] ftv_ctx P -> frv_ctx G [<=] frv_ctx P ->
  supp_ok D Sd ->
  typing D ((x ~ gen P T1 k rk) ++ G) e T2 ->
  is_gen_value v = true ->
  typing (extr (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx P)) k)
               (AtomSetImpl.diff (frv_typ T1) (frv_ctx P)) rk) G v T1 ->
  typing D G (subst_exp v x e) T2.
Proof.
  intros D Sd G P x T1 k rk e T2 v HGP HGPr HS Hty Hgv Hv.
  set (S0 := ftv_ctx G `union` ftv_sch (gen P T1 k rk)).
  set (SR := frv_ctx G `union` frv_sch (gen P T1 k rk)).
  refine (proj1 (typing_subst_gen_mut x (gen P T1 k rk) v G
                   (fun D' => (forall a, a `in` S0 -> D' a = D a) /\ (forall r, r `in` SR -> drk D' r = drk D r))
                   Hgv (typing_regular _ _ _ _ Hv) _ _ _) D _ e T2 Hty Sd HS _ nil eq_refl).
  - intros D' V k' Hvv [Hag Hagr]. split.
    + intros a Ha. rewrite ext_out; [ apply Hag; exact Ha | intro Hav; exact (Hvv a Hav Ha) ].
    + intros r Hr. rewrite ext_drk. apply Hagr. exact Hr.
  - intros D' V rk' Hvv [Hag Hagr]. split.
    + intros a Ha. rewrite extr_dsort. apply Hag. exact Ha.
    + intros r Hr. rewrite extr_out; [ apply Hagr; exact Hr | intro Hrv; exact (Hvv r Hrv Hr) ].
  - intros D' Sd' T' HS' [Hag Hagr] Hi.
    eapply typing_inst_gen with (D0 := D) (Sd0 := Sd) (P := P);
      [ exact HGP | exact HGPr | exact Hv | exact Hi | exact HS | exact HS' | | ].
    + intros a Ha. apply Hag. unfold S0. fsetdec.
    + intros r Hr. apply Hagr. unfold SR. fsetdec.
  - split; intros; reflexivity.
Qed.

(* The result of a comparison of two literals of one base type is a boolean. *)
Lemma typing_of_bool : forall D G b, uniq G -> typing D G (of_bool b) typ_Bool.
Proof. intros D G b Hu. destruct b; [ apply T_True | apply T_False ]; exact Hu. Qed.

(* A decimal literal has type [Float], through any conversion. *)
Lemma dec_inv : forall D G d T, typing D G (e_dec d) T -> teqD D typ_Float T.
Proof.
  intros D G d T H. remember (e_dec d) as e0 eqn:He.
  induction H; try discriminate He.
  - apply teqD_refl.
  - eapply teqD_trans; [ apply IHtyping; exact He | assumption ].
Qed.

Lemma ext_idem_d : forall D V k Vr rk,
  denv_eq (extr (ext (extr (ext D V k) Vr rk) V k) Vr rk) (extr (ext D V k) Vr rk).
Proof.
  intros D V k Vr rk. split.
  - intros a. unfold ext, extr. simpl. destruct (AtomSetImpl.mem a V); reflexivity.
  - intros r. unfold ext, extr. simpl. destruct (AtomSetImpl.mem r Vr); reflexivity.
Qed.

(* An operator's result has the type its signature gives.  Pairing each way
   the operator can compute ([bin_step]) with each signature, almost every pair
   is ruled out by the operator's class.  What is left: a ring operation on two
   numerals gives a numeral at the operand type (a [Literal] type, by the
   numeral's own typing); a Float operation has a decimal operand, which fixes
   the operand type to [Float]. *)
Lemma quot_literal_float : forall D A,
  sat D k_Quot A -> sat D k_Literal A -> A = typ_Float.
Proof.
  intros D A H1 H2. destruct A as [ | | | | | T1 T2 | R | a | i | B | w A ]; simpl in H1, H2; try contradiction; try reflexivity;
    try (destruct H1 as [H1 | H1]; discriminate H1); try discriminate H1.
  - exfalso. destruct (D a) eqn:E; inversion H1; subst; try (inversion H2; fail); try congruence.
Qed.

Lemma bin_step_typing : forall D G o v1 v2 v A B R,
  bin_sig D o A B R -> value v1 -> value v2 ->
  typing D G v1 A -> typing D G v2 B -> bin_step o v1 v2 v -> typing D G v R.
Proof.
  intros D G o v1 v2 v A B R Hs Hv1 Hv2 H1 H2 Hb.
  assert (Hu : uniq G) by (eapply typing_uniq; exact H1).
  destruct (kind_cmp_dec o) as [Hc | Hnc].
  { (* a comparison is a Bool whatever its operands are *)
    inversion Hs; subst; try (exfalso; first [ congruence | (simpl in Hc; discriminate) ]).
    inversion Hb; subst;
      try (exfalso; first [ congruence
        | (match goal with Hd : kind _ = _ \/ kind _ = _ |- _ => destruct Hd; congruence end) ]).
    all: apply typing_of_bool; exact Hu. }
  assert (HnR : forall R0, A <> typ_Record R0).
  { intros R0 HA. subst A.
    destruct (canon_record _ _ _ _ Hv1 H1) as [fs [Rf [-> _]]].
    inversion Hb; subst; try congruence; try (simpl in *; discriminate);
      try (match goal with Hf : fl_pair _ _ |- _ => inversion Hf end). }
  destruct Hb; inversion Hs; subst;
    try (exfalso; eapply HnR; reflexivity);
    try (exfalso; first [ congruence | (simpl in *; discriminate)
      | (match goal with Hd : kind _ = _ \/ kind _ = _ |- _ => destruct Hd; congruence end) ]);
    try (apply T_Dec; exact Hu);
    try (apply typing_of_bool; exact Hu);
    try (apply T_Num; [ exact Hu | first [ exact I | exact (num_inv _ _ _ _ H1) ] ]).
  all: try (match goal with Hq : sat ?D0 k_Quot ?A |- typing _ _ (e_dec _) ?A =>
              rewrite (quot_literal_float _ A Hq (num_inv _ _ _ _ H1)); apply T_Dec; exact Hu end).
  all: try (match goal with Hf : fl_pair _ _ |- _ => destruct Hf end).
  all: first
    [ (eapply T_ConvD; [ apply T_Dec; exact Hu | exact (dec_inv _ _ _ _ H1) ])
    | (eapply T_ConvD; [ apply T_Dec; exact Hu | exact (dec_inv _ _ _ _ H2) ]) ].
Qed.


(* The record of operator applications that [st_binrec] steps to has the type
   of the operands. *)
Lemma binrec_typing : forall D G o fs1 fs2 fs A B R, kind o <> k_cmp ->
  bin_sig D o A B R -> typing D G (e_rec fs1) A -> typing D G (e_rec fs2) B ->
  rec_zip o (fs_plain fs1) (fs_plain fs2) fs -> typing D G (e_rec fs) R.
Proof.
  intros D G o fs1 fs2 fs A B R Hnc Hs H1 H2 Hz.
  destruct (rec_inv _ _ _ _ H1) as [Rf1 [Hf1 Hq1]].
  destruct (rec_inv _ _ _ _ H2) as [Rf2 [Hf2 Hq2]].
  destruct (teqD_Record_inv _ _ _ Hq1) as [R1 [-> Hr1]].
  destruct (bin_sig_record _ _ _ _ _ Hnc Hs) as [-> [-> Hrow]].
  destruct (teqD_Record_inv _ _ _ Hq2) as [R2 [Heq Hr2]]. inversion Heq; subst R2.
  destruct (zip_typing _ _ o _ _ (field_typing_fs_plain _ _ _ _ (field_typing_nf _ _ _ _ Hf1))
              (no_meth_plain fs1) _ _ _
              (field_typing_fs_plain _ _ _ _ (field_typing_nf _ _ _ _ Hf2)) Hr1 Hr2
              (row_sig_nf _ _ _ Hrow)) as [fs' [Ro [Hz' [Hf Hq]]]].
  rewrite (rec_zip_det _ _ _ _ Hz _ Hz').
  eapply T_ConvD; [ apply T_Record; [ exact Hf | eapply rec_zip_no_meth; exact Hz' ] | ].
  apply teqD_Record. pose proof (req_reqD D _ _ Hq) as H3. unfold reqD in H3.
  rewrite nfR_idem in H3. exact H3.
Qed.

Scheme step_mut := Induction for step Sort Prop
with   step_fields_mut := Induction for step_fields Sort Prop.
Combined Scheme step_step_fields_mutind from step_mut, step_fields_mut.

Lemma is_gen_fs_replace : forall l v fs,
  is_gen_value v = true -> is_gen_fields fs = true ->
  is_gen_fields (fs_replace l v fs) = true.
Proof.
  intros l v. induction fs as [|l' e fs IH|l' e fs IH]; intros Hv Hfs; simpl in *; [ exact Hfs | | ].
  - apply andb_prop in Hfs. destruct Hfs as [He Hfs].
    destruct (Nat.eqb l l'); simpl; [ rewrite Hv | rewrite He ]; [ exact Hfs | ].
    rewrite (IH Hv Hfs). reflexivity.
  - apply andb_prop in Hfs. destruct Hfs as [He Hfs].
    destruct (Nat.eqb l l'); simpl; [ rewrite Hv | rewrite He ]; [ exact Hfs | ].
    rewrite (IH Hv Hfs). reflexivity.
Qed.

Lemma is_gen_fs_plain : forall fs, is_gen_fields fs = true -> is_gen_fields (fs_plain fs) = true.
Proof.
  induction fs as [|l e fs IH|l e fs IH]; intros H; simpl in *; auto;
    apply andb_prop in H; destruct H as [He Hfs]; rewrite He, (IH Hfs); reflexivity.
Qed.

Lemma is_gen_fs_set : forall l v fs,
  is_gen_value v = true -> is_gen_fields fs = true ->
  is_gen_fields (fs_set l v fs) = true.
Proof.
  intros l v fs Hv Hfs. unfold fs_set.
  destruct (lookup_first l fs); [ apply is_gen_fs_replace; assumption | simpl; rewrite Hv; exact Hfs ].
Qed.

(* A syntactic value stays one when it steps (a record of syntactic values
   steps only inside a field that is a recursive group around a value). *)
Lemma step_gen_mut :
  (forall e e', step e e' -> is_gen_value e = true -> is_gen_value e' = true) /\
  (forall fs fs', step_fields fs fs' -> is_gen_fields fs = true -> is_gen_fields fs' = true).
Proof.
  apply step_step_fields_mutind; try (intros; discriminate).
  - (* st_letrec *) intros fs e2 Hfg Hgen. simpl in Hgen |- *.
    apply andb_prop in Hgen. destruct Hgen as [Hfs He2].
    apply is_gen_open; [ | exact He2 ].
    simpl. apply is_gen_open_fields; [ simpl; rewrite Hfs; reflexivity | exact Hfs ].
  - (* st_rec *) intros fs fs' Hstep IH Hgen. simpl in Hgen |- *. exact (IH Hgen).
  - (* st_tofloat1 *) intros e e' Hstep IH Hgen. simpl in Hgen |- *. exact (IH Hgen).
  - (* st_tofloat *) intros z d Hgen. reflexivity.
  - (* st_tofloat_dec *) intros d Hgen. reflexivity.
  - (* st_spread1 *) intros e1 e1' l e2 Hstep IH Hgen. simpl in Hgen |- *.
    apply andb_prop in Hgen. destruct Hgen as [H1 H2]. rewrite (IH H1), H2. reflexivity.
  - (* st_spread2 *) intros v1 l e2 e2' Hv Hstep IH Hgen. simpl in Hgen |- *.
    apply andb_prop in Hgen. destruct Hgen as [H1 H2]. rewrite H1, (IH H2). reflexivity.
  - (* st_spread *) intros fs l v Hrv Hv Hgen. simpl in Hgen |- *.
    apply andb_prop in Hgen. destruct Hgen as [H1 H2].
    apply is_gen_fs_plain. apply is_gen_fs_set; [ exact H2 | exact H1 ].
  - (* st_fold1 *) intros e e' Hstep IH Hgen. simpl in Hgen |- *. exact (IH Hgen).
  - (* st_con1 *) intros w tg e e' Hstep IH Hgen. simpl in Hgen |- *. exact (IH Hgen).
  - (* stf_here *) intros l e e' fs Hstep IH Hgen. simpl in Hgen |- *.
    apply andb_prop in Hgen. destruct Hgen as [He Hfs].
    rewrite (IH He), Hfs. reflexivity.
  - (* stf_cons *) intros l v fs fs' Hv Hstep IH Hgen. simpl in Hgen |- *.
    apply andb_prop in Hgen. destruct Hgen as [Hv0 Hfs].
    rewrite Hv0, (IH Hfs). reflexivity.
  - (* stf_meth_here *) intros l e e' fs Hstep IH Hgen. simpl in Hgen |- *.
    apply andb_prop in Hgen. destruct Hgen as [He Hfs].
    rewrite (IH He), Hfs. reflexivity.
  - (* stf_meth_cons *) intros l v fs fs' Hv Hstep IH Hgen. simpl in Hgen |- *.
    apply andb_prop in Hgen. destruct Hgen as [Hv0 Hfs].
    rewrite Hv0, (IH Hfs). reflexivity.
Qed.

Lemma step_gen : forall e e',
  step e e' -> is_gen_value e = true -> is_gen_value e' = true.
Proof. apply step_gen_mut. Qed.

(* A function and a numeral are values, so a [let] that pins its literals
   keeps pinning them when its binding steps. *)
Lemma step_let_open : forall e e', step e e' -> let_open e' = false -> let_open e = false.
Proof. intros e e' H Hc. destruct e; simpl; auto; inversion H. Qed.



(* Do induction on the step relation: one case per step rule.  Each case
   begins by assuming the term before the step is typed at [T] in context
   [G] under a kinding environment [D] that is [Any] outside the finite set
   [S] (that is the [Hty] below) and must show the stepped term is too. *)
Lemma preservation_mut :
  (forall e e', step e e' -> forall D S G T, supp_ok D S -> typing D G e T -> typing D G e' T) /\
  (forall fs fs', step_fields fs fs' ->
     forall D S G R, supp_ok D S -> field_typing D G fs R -> field_typing D G fs' R).
Proof.
  apply step_step_fields_mutind.
  - (* Case: a function call on a value, [(fun x => e) v] steps to [e] with
       [v] plugged in (st_beta).  The real work.  Plan: read off from [Hty]
       that the function has type [A -> B] and [v] has type [A]; then the
       substitution lemma [typing_subst] says plugging [v] into the body keeps
       the type [B]. *)
    intros e v Hv D S G T HS Hty.
    apply app_inv in Hty. destruct Hty as [A [B [Habs [Harg Hbt]]]].
    apply abs_inv in Habs. destruct Habs as [L [A' [B' [Hbody Harr]]]].
    apply teq_Arrow_inv in Harr. destruct Harr as [A2 [B2 [Heq [HA HB]]]].
    inversion Heq; subst.
    pick fresh x for (L \u fv_exp e).
    assert (HxL : x `notin` L) by fsetdec.
    assert (Hxe : x `notin` fv_exp e) by fsetdec.
    assert (Hv' : typing D G v A') by (eapply T_ConvD; [ exact Harg | apply teq_sym; exact HA ]).
    assert (Hopen : typing D G (subst_exp v x (open_exp_wrt_exp e (e_fvar_f x))) B')
      by (eapply typing_subst; [ exact HS | apply Hbody; exact HxL | apply value_gen; exact Hv | exact Hv' ]).
    rewrite <- subst_intro in Hopen by exact Hxe.
    eapply T_ConvD; [ exact Hopen | ].
    eapply teq_trans; [ exact HB | exact Hbt ].
  - (* st_app1: the function part of a call stepped.  Congruence. *)
    intros e1 e1' e2 Hstep IH D S G T HS Hty.
    apply app_inv in Hty. destruct Hty as [A [B [Hty1 [Hty2 Hbt]]]].
    eapply T_ConvD; [ eapply T_App; [ eapply IH; [ exact HS | exact Hty1 ] | exact Hty2 ] | exact Hbt ].
  - (* st_app2: the argument of a call stepped. *)
    intros v e2 e2' Hv Hstep IH D S G T HS Hty.
    apply app_inv in Hty. destruct Hty as [A [B [Hty1 [Hty2 Hbt]]]].
    eapply T_ConvD; [ eapply T_App; [ exact Hty1 | eapply IH; [ exact HS | exact Hty2 ] ] | exact Hbt ].
  - (* Case: [let x = v in e2] with [v] a value steps to [e2] with [v] plugged
       in for [x] (st_letv).  [x] may be used at several types in [e2], so a
       generalized binding uses the POLYMORPHIC substitution lemma. *)
    intros v e2 Hv D S G T HS Hty.
    apply let_inv in Hty. destruct Hty as [L [T1 [T2 [Hty1 Hteq]]]].
    pick fresh x for (L \u fv_exp e2).
    assert (HxL : x `notin` L) by fsetdec.
    assert (Hxe : x `notin` fv_exp e2) by fsetdec.
    assert (Hopen : typing D G (subst_exp v x (open_exp_wrt_exp e2 (e_fvar_f x))) T2).
    { destruct Hty1 as [[_ [k [rk [Tm [_ [Hty1 Hbody]]]]]] | [Hty1 Hbody]].
      - eapply typing_subst_poly with (P := pin_ctx Tm G);
          [ rewrite ftv_pin_ctx; fsetdec | rewrite frv_pin_ctx; fsetdec | exact HS
          | apply Hbody; exact HxL | apply value_gen; exact Hv | exact Hty1 ].
      - eapply typing_subst; [ exact HS | apply Hbody; exact HxL | apply value_gen; exact Hv | exact Hty1 ]. }
    rewrite <- subst_intro in Hopen by exact Hxe.
    eapply T_ConvD; [ exact Hopen | exact Hteq ].
  - (* st_let1: the bound expression of a [let] stepped.  Congruence.  The
       bound term of a generalized binding is typed under the extended
       environment, which is still [Any] outside a finite set. *)
    intros e1 e1' e2 Hstep IH D S G T HS Hty.
    apply let_inv in Hty. destruct Hty as [L [T1 [T2 [Hty1 Hteq]]]].
    destruct Hty1 as [[Hgv [k [rk [Tm [Hlp [Hty1 Hbody]]]]]] | [Hty1 Hbody]].
    + eapply T_ConvD; [ eapply T_Let with (L := L) (T1 := T1) (k := k) (rk := rk) (Tm := Tm);
                       [ eapply step_gen; eassumption
                       | intros Hc a Ha; apply (Hlp (step_let_open _ _ Hstep Hc) a Ha)
                       | eapply IH; [ apply supp_ok_ext2; exact HS | exact Hty1 ]
                       | exact Hbody ]
                     | exact Hteq ].
    + eapply T_ConvD; [ eapply T_LetMono with (L := L) (T1 := T1);
                       [ eapply IH; [ exact HS | exact Hty1 ] | exact Hbody ] | exact Hteq ].
  - (* Case: a recursive group unrolls (st_letrec).  Name the group's
       record type [R].  The group itself, [letrec fs in p], has type [R]
       under the environment its members are typed in (the body is the group
       name, typed by an instance of its scheme).  Substituting that group for
       the name inside the members, which were typed with the name at [R],
       types the unrolled members at [R]; those members form a record value,
       and substituting it for the name in the body is the polymorphic
       substitution lemma. *)
    intros fs e2 Hfg D S G T HS Hty.
    destruct (letrec_inv _ _ _ _ _ Hty) as [L [R [T2 [k [rk [Hfg' [Hfs [Hbody Hteq]]]]]]]].
    set (V := AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G)).
    set (Vr := AtomSetImpl.diff (frv_typ (typ_Record R)) (frv_ctx G)).
    pick fresh p for (L \u fv_exp e2 \u fv_fields fs).
    assert (HpL : p `notin` L) by fsetdec.
    assert (Hpe : p `notin` fv_exp e2) by fsetdec.
    assert (Hpf : p `notin` fv_fields fs) by fsetdec.
    assert (Hu : uniq G).
    { pose proof (proj2 typing_uniq_mut _ _ _ _ (Hfs p HpL)) as Hup.
      eapply uniq_cons_1; exact Hup. }
    assert (HSV : supp_ok (extr (ext D V k) Vr rk) (S `union` V `union` Vr))
      by (apply supp_ok_ext2; exact HS).
    assert (Hgrp : typing (extr (ext D V k) Vr rk) G (e_letrec fs (e_fvar_b 0)) (typ_Record R)).
    { apply T_Letrec with (L := L) (R := R) (k := k) (rk := rk); [ exact Hfg' | | ].
      - intros q Hq. eapply field_typing_pw; [ exact (Hfs q Hq) | ].
        apply denv_eq_sym. apply ext_idem_d.
      - intros q Hq. unfold open_exp_wrt_exp. cbn [open_exp_wrt_exp_rec].
        apply T_Var with (s := gen G (typ_Record R) k rk).
        + pose proof (proj2 typing_uniq_mut _ _ _ _ (Hfs q Hq)) as Huq.
          apply uniq_cons_3; [ eapply uniq_cons_1; exact Huq | eapply uniq_cons_2; exact Huq ].
        + apply binds_cons_2; reflexivity.
        + exists idt, idr. split; [ | split; [ | split; [ | split; [ | split ] ] ] ].
          * intros a _. reflexivity.
          * intros r _. reflexivity.
          * symmetry. apply ap_typ_pointwise_id; reflexivity.
          * intros a Ha. cbn [gen s_tq s_sk] in Ha |- *. unfold idt. cbn [sat].
            rewrite extr_dsort. rewrite (ext_in D V k a Ha). apply finer_refl.
          * intros r Hr. cbn [gen s_rq s_rk] in Hr |- *. unfold idr.
            pose proof (rkok_self (extr (ext D V k) Vr rk) r) as Hself.
            rewrite (extr_in _ _ _ r Hr) in Hself. exact Hself.
          * apply lc_sub_id. }
    assert (Hgengrp : is_gen_value (e_letrec fs (e_fvar_b 0)) = true).
    { simpl. rewrite (fn_group_gen _ Hfg). reflexivity. }
    assert (Hmem : field_typing (extr (ext D V k) Vr rk) G
              (subst_fields (e_letrec fs (e_fvar_b 0)) p (open_fields_wrt_exp fs (e_fvar_f p))) R)
      by (eapply field_typing_subst; [ exact HSV | apply Hfs; exact HpL | exact Hgengrp | exact Hgrp ]).
    rewrite <- subst_intro_fields in Hmem by exact Hpf.
    assert (Hrec : typing (extr (ext D V k) Vr rk) G
              (e_rec (open_fields_wrt_exp fs (e_letrec fs (e_fvar_b 0)))) (typ_Record R))
      by (apply T_Record; [ exact Hmem | ];
          rewrite (no_meth_marks _ fs); [ apply fn_group_no_meth; exact Hfg | ];
          unfold open_fields_wrt_exp; apply marks_open_fields).
    assert (Hrecgen : is_gen_value
              (e_rec (open_fields_wrt_exp fs (e_letrec fs (e_fvar_b 0)))) = true).
    { simpl. apply is_gen_open_fields; [ exact Hgengrp | apply fn_group_gen; exact Hfg ]. }
    assert (Hopen : typing D G
              (subst_exp (e_rec (open_fields_wrt_exp fs (e_letrec fs (e_fvar_b 0)))) p
                 (open_exp_wrt_exp e2 (e_fvar_f p))) T2)
      by (eapply typing_subst_poly with (P := G);
            [ fsetdec | fsetdec | exact HS | apply Hbody; exact HpL | exact Hrecgen | exact Hrec ]).
    rewrite <- subst_intro in Hopen by exact Hpe.
    eapply T_ConvD; [ exact Hopen | exact Hteq ].
  - (* st_proj: the record in a field access stepped.  Congruence. *)
    intros e e' l Hstep IH D S G T HS Hty.
    apply proj_inv in Hty. destruct Hty as [T0 [R [Hty0 Hteq]]].
    eapply T_ConvD; [ eapply T_Proj; eapply IH; [ exact HS | exact Hty0 ] | exact Hteq ].
  - (* st_projrec: field access on a finished record steps to the field. *)
    intros fs l v Hrv Hlook D S G T HS Hty.
    apply proj_inv in Hty. destruct Hty as [T0 [R [Hrec Hteq]]].
    apply rec_inv in Hrec. destruct Hrec as [R' [Hft Hreq]].
    apply teqD_Record_inv in Hreq. destruct Hreq as [R2 [Heq Hreq]].
    inversion Heq; subst.
    rewrite nfR_ext in Hreq.
    apply req_surface in Hreq. destruct Hreq as [T1 [rest [Hpi Hteq1]]].
    rewrite pi_nf in Hpi. destruct (map_cons_inv _ _ _ _ _ _ Hpi) as [T2 [rest2 [Hpi2 [E1 _]]]].
    destruct (field_lookup_some _ _ _ _ _ _ _ Hft Hpi2) as [v0 [Hlook0 Hty0]].
    assert (v0 = v) by congruence. subst v0.
    eapply T_ConvD; [ exact Hty0 | ].
    eapply teqD_trans; [ | exact Hteq ]. unfold teqD. rewrite E1. exact Hteq1.
  - (* st_rec: a field inside a record stepped.  Congruence. *)
    intros fs fs' Hstep IHf D S G T HS Hty.
    apply rec_inv_ok in Hty. destruct Hty as [R [Hft [Hok Hteq]]].
    eapply T_ConvD; [ apply T_rec_ok; [ eapply IHf; [ exact HS | exact Hft ] | eapply rec_ok_marks; [ exact Hok | symmetry; eapply marks_step_fields; exact Hstep ] ] | exact Hteq ].
  - (* st_ite1: the condition of an [if] stepped. *)
    intros e1 e1' e2 e3 Hstep IH D S G T HS Hty.
    apply ite_inv in Hty. destruct Hty as [T' [H1 [H2 [H3 Hteq]]]].
    eapply T_ConvD; [ eapply T_If; [ eapply IH; [ exact HS | exact H1 ] | exact H2 | exact H3 ] | exact Hteq ].
  - (* st_ite_true *)
    intros e2 e3 D S G T HS Hty.
    apply ite_inv in Hty. destruct Hty as [T' [H1 [H2 [H3 Hteq]]]].
    eapply T_ConvD; [ exact H2 | exact Hteq ].
  - (* st_ite_false *)
    intros e2 e3 D S G T HS Hty.
    apply ite_inv in Hty. destruct Hty as [T' [H1 [H2 [H3 Hteq]]]].
    eapply T_ConvD; [ exact H3 | exact Hteq ].
  - (* st_bin1: the left operand stepped. *)
    intros e1 e1' o e2 Hstep IH D S G T HS Hty.
    destruct (bin_inv _ _ _ _ _ _ Hty) as [A [B [R [H1 [H2 [Hs Hteq]]]]]].
    eapply T_ConvD; [ eapply T_Bin; [ eapply IH; [ exact HS | exact H1 ] | exact H2 | exact Hs ] | exact Hteq ].
  - (* st_bin2: the right operand stepped. *)
    intros v o e2 e2' Hv Hstep IH D S G T HS Hty.
    destruct (bin_inv _ _ _ _ _ _ Hty) as [A [B [R [H1 [H2 [Hs Hteq]]]]]].
    eapply T_ConvD; [ eapply T_Bin; [ exact H1 | eapply IH; [ exact HS | exact H2 ] | exact Hs ] | exact Hteq ].
  - (* st_bin: an operator on two values.  [bin_step_typing] shows the result
       has the type the operator's signature gives. *)
    intros v1 o v2 v Hv1 Hv2 Hb D S G T HS Hty.
    destruct (bin_inv _ _ _ _ _ _ Hty) as [A [B [R [H1 [H2 [Hs Hteq]]]]]].
    eapply T_ConvD;
      [ exact (bin_step_typing _ _ _ _ _ _ _ _ _ Hs Hv1 Hv2 H1 H2 Hb) | exact Hteq ].
  - (* st_binrec: an operator on two records.  The record of operator
       applications, field by field, has the row the operands have
       ([binrec_typing]). *)
    intros fs1 o fs2 fs Hnc Hv1 Hv2 Hz D S G T HS Hty.
    destruct (bin_inv _ _ _ _ _ _ Hty) as [A [B [R [H1 [H2 [Hs Hteq]]]]]].
    eapply T_ConvD;
      [ exact (binrec_typing _ _ _ _ _ _ _ _ _ Hnc Hs H1 H2 Hz) | exact Hteq ].
  - (* st_tofloat1: the operand of a coercion stepped. *)
    intros e e' Hstep IH D S G T HS Hty.
    destruct (tofloat_inv _ _ _ _ Hty) as [A [H1 [Hsat Hteq]]].
    eapply T_ConvD; [ eapply T_ToFloat; [ eapply IH; [ exact HS | exact H1 ] | exact Hsat ] | exact Hteq ].
  - (* st_tofloat: [float(n)] steps to a Float.  A Float value has type
       [Float] whatever its payload. *)
    intros z d D S G T HS Hty.
    destruct (tofloat_inv _ _ _ _ Hty) as [A [H1 [Hsat Hteq]]].
    assert (Hu : uniq G) by (eapply typing_uniq; exact H1).
    eapply T_ConvD; [ apply T_Dec; exact Hu | exact Hteq ].
  - (* st_tofloat_dec: [float(d)] of a decimal is the decimal. *)
    intros d D S G T HS Hty.
    destruct (tofloat_inv _ _ _ _ Hty) as [A [H1 [Hsat Hteq]]].
    assert (Hu : uniq G) by (eapply typing_uniq; exact H1).
    eapply T_ConvD; [ apply T_Dec; exact Hu | exact Hteq ].
  - (* st_spread1: the base of a spread stepped. *)
    intros e1 e1' l e2 Hstep IH D S G T HS Hty.
    destruct (spread_inv _ _ _ _ _ _ Hty) as [T0 [R [H2 [Hteq [[P H1] | [H1 Hl]]]]]].
    + eapply T_ConvD;
        [ eapply T_Spread; [ eapply IH; [ exact HS | exact H1 ] | exact H2 ] | exact Hteq ].
    + eapply T_ConvD;
        [ eapply T_SpreadL; [ eapply IH; [ exact HS | exact H1 ] | exact Hl | exact H2 ] | exact Hteq ].
  - (* st_spread2: the new value of a spread stepped. *)
    intros v1 l e2 e2' Hv Hstep IH D S G T HS Hty.
    destruct (spread_inv _ _ _ _ _ _ Hty) as [T0 [R [H2 [Hteq [[P H1] | [H1 Hl]]]]]].
    + eapply T_ConvD;
        [ eapply T_Spread; [ exact H1 | eapply IH; [ exact HS | exact H2 ] ] | exact Hteq ].
    + eapply T_ConvD;
        [ eapply T_SpreadL; [ exact H1 | exact Hl | eapply IH; [ exact HS | exact H2 ] ] | exact Hteq ].
  - (* st_spread: a spread of a finished record sets or adds the field.  The
       base's type says which, and [spread_step_typing] shows either way the
       result has the type the rule gives. *)
    intros fs l v Hrv Hv D S G T HS Hty.
    destruct (spread_inv _ _ _ _ _ _ Hty) as [T0 [R [H2 [Hteq [[P H1] | [H1 Hl]]]]]].
    + eapply T_ConvD; [ eapply spread_step_typing; eassumption | exact Hteq ].
    + eapply T_ConvD; [ eapply spread_step_typing_L; eassumption | exact Hteq ].
  - (* st_restrict1: the operand of a restrict stepped. *)
    intros e e' l Hstep IH D S G T HS Hty.
    destruct (restrict_inv _ _ _ _ _ Hty) as [R0 [T0 [R [H1 [H2 Hteq]]]]].
    eapply T_ConvD;
      [ eapply T_Restrict; [ eapply IH; [ exact HS | exact H1 ] | exact H2 ] | exact Hteq ].
  - (* st_restrict: a restrict of a finished record takes out its first field. *)
    intros fs l Hrv D S G T HS Hty.
    destruct (restrict_inv _ _ _ _ _ Hty) as [R0 [T0 [R [H1 [H2 Hteq]]]]].
    eapply T_ConvD; [ eapply restrict_step_typing; eassumption | exact Hteq ].
  - (* st_fold1: the operand of a fold stepped. *)
    intros e e' Hstep IH D S G T HS Hty.
    destruct (fold_inv _ _ _ _ Hty) as [B [Hteq [Hlc0 [Hg Hb]]]].
    eapply T_ConvD; [ eapply T_Fold; [ exact Hlc0 | exact Hg | eapply IH; [ exact HS | exact Hb ] ] | exact Hteq ].
  - (* st_unfold1: the operand of an unfold stepped. *)
    intros e e' Hstep IH D S G T HS Hty.
    destruct (unfold_inv _ _ _ _ Hty) as [B [Hlc0 [Hg [Hb Hteq]]]].
    eapply T_ConvD; [ eapply T_Unfold; [ exact Hlc0 | exact Hg | eapply IH; [ exact HS | exact Hb ] ] | exact Hteq ].
  - (* st_unfold_fold: an unfold cancels the fold of a value.  The fold was
       typed at a recursive type equal to the one the unfold opens, and
       equal recursive types have equal unrollings. *)
    intros v Hv D S G T HS Hty.
    destruct (unfold_inv _ _ _ _ Hty) as [B [Hlc0 [Hg [Hb Hteq]]]].
    destruct (fold_inv _ _ _ _ Hb) as [B0 [Hmu [Hlc1 [Hg1 Hv0]]]].
    eapply T_ConvD; [ exact Hv0 | ].
    eapply teqD_trans; [ apply teq_teqD; apply teq_unroll; exact (teqD_Mu_teq _ _ _ Hmu) | exact Hteq ].
  - (* st_con1: the payload of a construction stepped. *)
    intros w tg e e' Hstep IH D S G T HS Hty.
    destruct (con_inv _ _ _ _ _ _ Hty) as [Ts [Hlt [Hp Hteq]]].
    eapply T_ConvD;
      [ eapply T_Con; [ exact Hlt | eapply IH; [ exact HS | exact Hp ] ] | exact Hteq ].
  - (* st_match1: the scrutinee of a match stepped. *)
    intros w e e' ars Hstep IH D S G T HS Hty.
    destruct (match_inv _ _ _ _ _ _ Hty) as [L [Ts [T0 [Hs [Hwf [Harm [Hdef Hteq]]]]]]].
    eapply T_ConvD;
      [ eapply T_Match with (L := L);
          [ eapply IH; [ exact HS | exact Hs ] | exact Hwf | exact Harm | exact Hdef ]
      | exact Hteq ].
  - (* st_match_arm: a match on a finished construction runs the arm for its
       tag, with the payload in place of the arm's variable.  The scrutinee's
       type names the group, so the construction is of the same group, and
       its payload has the payload type the arm's variable was given: the
       arguments of the two group types are equal, and equal arguments give
       equal payloads.  Then the substitution lemma plugs the payload in,
       as it does for a function call. *)
    intros w w' tg v ars body Hv Hf D S G T HS Hty.
    destruct (match_inv _ _ _ _ _ _ Hty) as [L [Ts [T0 [Hs [Hwf [Harm [Hdef Hteq]]]]]]].
    destruct (con_inv _ _ _ _ _ _ Hs) as [Ts' [Hlt [Hp Hgrp]]].
    apply teqD_Grp_inv in Hgrp. destruct Hgrp as [A [Eg Hsp]].
    injection Eg as Ew EA. subst w' A.
    apply teq_spine_inv in Hsp.
    assert (Hv' : typing D G v (tag_payload w Ts tg))
      by (eapply T_Conv; [ exact Hp | apply teq_tag_payload; exact Hsp ]).
    pick fresh x for (L \u fv_exp body).
    assert (HxL : x `notin` L) by fsetdec.
    assert (Hxe : x `notin` fv_exp body) by fsetdec.
    assert (Hopen : typing D G (subst_exp v x (open_exp_wrt_exp body (e_fvar_f x))) T0)
      by (eapply typing_subst;
            [ exact HS | exact (Harm tg body Hf x HxL) | apply value_gen; exact Hv | exact Hv' ]).
    rewrite <- subst_intro in Hopen by exact Hxe.
    eapply T_ConvD; [ exact Hopen | exact Hteq ].
  - (* st_match_else: no arm names the tag, so the else runs. *)
    intros w w' tg v ars e0 Hv Hf Hd D S G T HS Hty.
    destruct (match_inv _ _ _ _ _ _ Hty) as [L [Ts [T0 [Hs [Hwf [Harm [Hdef Hteq]]]]]]].
    eapply T_ConvD; [ exact (Hdef e0 Hd) | exact Hteq ].
  - (* stf_here: the FIRST field of a record stepped.  Congruence. *)
    intros l e e' fs Hstep IH D S G R HS Hft.
    inversion Hft; subst.
    eapply FT_cons; [ eapply IH; [ exact HS | eassumption ] | eassumption ].
  - (* stf_cons: the first field is a value and a LATER field stepped. *)
    intros l v fs fs' Hv Hstep IHf D S G R HS Hft.
    inversion Hft; subst.
    eapply FT_cons; [ eassumption | eapply IHf; [ exact HS | eassumption ] ].
  - (* stf_meth_here *)
    intros l e e' fs Hstep IH D S G R HS Hft.
    inversion Hft; subst.
    eapply FT_meth; [ eapply IH; [ exact HS | eassumption ] | eassumption ].
  - (* stf_meth_cons *)
    intros l v fs fs' Hv Hstep IHf D S G R HS Hft.
    inversion Hft; subst.
    eapply FT_meth; [ eassumption | eapply IHf; [ exact HS | eassumption ] ].
Qed.

(* The headline form of the induction above: with just the first half of the
   combined statement. *)
Theorem preservation : forall D S G e e' T,
  supp_ok D S -> typing D G e T -> step e e' -> typing D G e' T.
Proof. intros D S G e e' T HS Hty Hstep. eapply (proj1 preservation_mut); eauto. Qed.


(* ================================================================== *)
(* Soundness (docs/semantics.md section 7): a well-typed closed term     *)
(* never reaches a stuck state.                                           *)
(*                                                                        *)
(* WHAT THIS SAYS: take a program [e] that type checks in the empty       *)
(* context ([nil], a closed program: no free variables, nothing from      *)
(* outside).  Run it for any number of steps ([multistep e e']).  Then    *)
(* wherever it has got to, [e'] is either finished (a value) or can take  *)
(* another step.  It is never stuck.                                      *)
(*                                                                        *)
(* WHY: progress says one program is not stuck; preservation says each    *)
(* step keeps the type.  We chain them over the steps of the run.         *)
(* ================================================================== *)

Theorem soundness : forall e T e',
  typing d_any nil e T -> multistep e e' ->
  value e' \/ (exists e'', step e' e'') \/ (exists k, traps e' k).
Proof.
  (* Assume the program is well typed ([Hty]) and that it ran from [e] to [e']
     ([Hms]).  Goal: [e'] is a value, can step, or traps.  We prove it by
     induction on HOW the run went, which is a list of steps: either zero
     steps, or one step followed by a shorter run.  ([revert T Hty] just makes
     the typing assumption part of what the induction proves, so it can change
     as the program changes.) *)
  intros e T e' Hty Hms. revert T Hty.
  induction Hms as [ e | e1 e2 e3 Hstep Hms IH ]; intros T Hty.
  - (* Case: zero steps, so [e'] is [e] itself.  It is well typed, so
       [progress] says it is a value, can step, or traps.  Done. *)
    eapply progress; exact Hty.
  - (* Case: one step [e1 -> e2], then a shorter run [e2 ->* e3].  By
       [preservation], [e2] is well typed at the same [T] as [e1] was; so the
       induction hypothesis (the claim for the shorter run) applies to [e2].
       That gives exactly what we need about [e3]. *)
    apply IH with (T := T).
    apply (preservation d_any {} nil e1 e2 T); [ | exact Hty | exact Hstep ].
    intros a _. split; reflexivity.
Qed.

(* The same fact phrased with the name [stuck] (not a value, no step possible,
   and no error raised): a reachable state is never stuck. *)
Corollary soundness_not_stuck : forall e T e',
  typing d_any nil e T -> multistep e e' -> ~ stuck e'.
Proof.
  intros e T e' Hty Hms [Hnv [Hns Hnt]].
  destruct (soundness e T e' Hty Hms) as [Hv | [[e'' Hs] | [k Hk]]].
  - exact (Hnv Hv).
  - exact (Hns e'' Hs).
  - exact (Hnt k Hk).
Qed.
