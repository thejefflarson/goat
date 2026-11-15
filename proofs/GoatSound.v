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
Require Import Goat.GoatMeta.
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
  - (* row_Var *) right. exists r. split; [fsetdec|auto].
  - (* row_Ext *) rewrite AtomSetFacts.union_iff in H1. destruct H1 as [H1|H1].
    + destruct (H _ _ _ H1) as [[b [Hb Ha]]|[p [Hp Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists p; split; [fsetdec|auto].
    + destruct (H0 _ _ _ H1) as [[b [Hb Ha]]|[p [Hp Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists p; split; [fsetdec|auto].
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
  - (* row_Var *) right. exists r. split; [fsetdec|auto].
  - rewrite AtomSetFacts.union_iff in H1. destruct H1 as [H1|H1].
    + destruct (H _ _ _ H1) as [[b [Hb Ha]]|[q [Hq Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists q; split; [fsetdec|auto].
    + destruct (H0 _ _ _ H1) as [[b [Hb Ha]]|[q [Hq Ha]]].
      * left; exists b; split; [fsetdec|auto].
      * right; exists q; split; [fsetdec|auto].
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
  - destruct H as [[b [Hb _]]|[p [Hp Ha]]]; [fsetdec|].
    rewrite AtomSetFacts.singleton_iff in Hp. subst p. exact Ha.
  - rewrite AtomSetFacts.union_iff.
    destruct H1 as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|Hb];
        [left; apply H; left; eauto | right; apply H0; left; eauto].
    + rewrite AtomSetFacts.union_iff in Hp. destruct Hp as [Hp|Hp];
        [left; apply H; right; eauto | right; apply H0; right; eauto].
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
  - destruct H as [[b [Hb _]]|[p [Hp Ha]]]; [fsetdec|].
    rewrite AtomSetFacts.singleton_iff in Hp. subst p. exact Ha.
  - rewrite AtomSetFacts.union_iff.
    destruct H1 as [[b [Hb Ha]]|[p [Hp Ha]]].
    + rewrite AtomSetFacts.union_iff in Hb. destruct Hb as [Hb|Hb];
        [left; apply H; left; eauto | right; apply H0; left; eauto].
    + rewrite AtomSetFacts.union_iff in Hp. destruct Hp as [Hp|Hp];
        [left; apply H; right; eauto | right; apply H0; right; eauto].
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
                 (s_sk (casch st sr g gr s))).
Proof.
  intros st sr g gr s Ct Cr Hgi Hgri Hgf Hgrf Hsubt Hsubr Hfx1 Hfx2 HfreshT HfreshR
    HcT_t HcT_r HcR_t HcR_r.
  set (B := ap_typ st sr (ren_typ g gr (s_body s))).
  (* ftv of the renamed body: b in ftv(ren body) <-> g b in ftv body *)
  assert (HFren : forall b, b `in` ftv_typ (ren_typ g gr (s_body s)) <-> g b `in` ftv_typ (s_body s)).
  { intro b. unfold ren_typ. apply (proj1 (Ftv_ren_mut g g gr Hgi Hgi)). }
  assert (HRren : forall b, b `in` frv_typ (ren_typ g gr (s_body s)) <-> gr b `in` frv_typ (s_body s)).
  { intro b. unfold ren_typ. apply (proj1 (Frv_ren_mut g gr gr Hgri Hgri)). }
  unfold sch_equiv, casch; simpl. split; [| split; [| split]].
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
Qed.

(* ===================== context substitution relation ==================== *)

(* A scheme absorbs a substitution when, for every pair of kinding
   environments the substitution respects, each instance of the scheme maps to
   an instance of the substituted scheme. *)
Definition sch_subst (st:tsub) (sr:rsub) (s s':scheme) : Prop :=
  forall D D', kres D D' st -> forall W, inst D W s -> inst D' (ap_typ st sr W) s'.

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
  intros st sr T D D' Hk W HW. apply inst_mono_eq in HW. subst W. apply inst_mono_self.
Qed.

(* a substitution fixing a scheme's free vars preserves its instances pointwise:
   this is the [T-Var] "re-chosen instance" with no renaming needed. *)
Lemma sch_subst_fix : forall st sr s,
  (forall a, a `in` ftv_sch s -> st a = typ_Var a) ->
  (forall r, r `in` frv_sch s -> sr r = row_Var r) ->
  sch_subst st sr s s.
Proof.
  intros st sr s Hf Hfr D D' Hk W [pt [pr [Hpt [Hpr [HW Hsat]]]]].
  exists (fun a => if AtomSetImpl.mem a (s_tq s) then ap_typ st sr (pt a) else typ_Var a),
         (fun r => if AtomSetImpl.mem r (s_rq s) then ap_row st sr (pr r) else row_Var r).
  split; [| split; [| split]].
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
    rewrite Hm. eapply sat_ap; [ exact Hk | apply Hsat; exact Ha ].
Qed.

(* The environment seen through a renaming of its atoms. *)
Definition dperm (g : atom -> atom) (D : denv) : denv := fun a => D (g a).

Lemma sat_ren : forall g gr D k T, (forall a, g (g a) = a) ->
  sat D k T -> sat (dperm g D) k (ren_typ g gr T).
Proof.
  intros g gr D k T Hi H. destruct T; simpl in *; try exact H.
  unfold dperm. rewrite Hi. exact H.
Qed.

(* renaming a scheme's instance along a bijection fixing the scheme's free vars
   lands on another instance of the SAME scheme, in the renamed environment. *)
Lemma inst_ren_same : forall g gr D s W,
  (forall a, a `in` ftv_sch s -> g a = a) ->
  (forall r, r `in` frv_sch s -> gr r = r) ->
  (forall a, g (g a) = a) ->
  inst D W s -> inst (dperm g D) (ren_typ g gr W) s.
Proof.
  intros g gr D s W Hgf Hgrf Hgi [pt [pr [Hpt [Hpr [HW Hsat]]]]].
  exists (fun a => if AtomSetImpl.mem a (s_tq s) then ren_typ g gr (pt a) else typ_Var a),
         (fun r => if AtomSetImpl.mem r (s_rq s) then ren_row g gr (pr r) else row_Var r).
  split; [| split; [| split]].
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
    rewrite Hm. apply sat_ren; [ exact Hgi | apply Hsat; exact Ha ].
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
  (forall a, g (g a) = a) ->
  ctx_subst st sr G G' ->
  (forall a, a `in` ftv_ctx G -> g a = a) ->
  (forall r, r `in` frv_ctx G -> gr r = r) ->
  ctx_subst (fun a => st (g a)) (fun r => sr (gr r)) G G'.
Proof.
  intros st sr g gr G G' Hgi HG Hgf Hgrf x s Hb.
  destruct (HG x s Hb) as [s' [Hb' Hss]]. exists s'. split; [exact Hb'|].
  intros D D' Hk W HW.
  assert (Hk2 : kres (dperm g D) D' st).
  { intros a. unfold dperm. unfold kres in Hk. specialize (Hk (g a)). simpl in Hk.
    rewrite Hgi in Hk. exact Hk. }
  rewrite ap_precomp. apply (Hss _ _ Hk2). apply inst_ren_same.
  - intros a Ha. apply Hgf.
    assert (ftv_sch s [<=] ftv_ctx G) by (eapply binds_ftv_sch; eauto). fsetdec.
  - intros r Hr. apply Hgrf.
    assert (frv_sch s [<=] frv_ctx G) by (eapply binds_frv_sch; eauto). fsetdec.
  - exact Hgi.
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

Lemma ftv_sch_gen_sub : forall G T k, ftv_sch (gen G T k) [<=] ftv_ctx G.
Proof. intros. unfold ftv_sch, gen; simpl. fsetdec. Qed.

Lemma frv_sch_gen_sub : forall G T k, frv_sch (gen G T k) [<=] frv_ctx G.
Proof. intros. unfold frv_sch, gen; simpl. fsetdec. Qed.

(* a substitution fixing the context's free vars relates the context to itself *)
Lemma ctx_subst_fix : forall st sr G,
  (forall a, a `in` ftv_ctx G -> st a = typ_Var a) ->
  (forall r, r `in` frv_ctx G -> sr r = row_Var r) ->
  ctx_subst st sr G G.
Proof.
  intros st sr G Hf Hfr x s Hb. exists s. split; [exact Hb|].
  apply sch_subst_fix.
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
  apply sch_subst_fix; intros; reflexivity.
Qed.

Lemma ftv_sch_mono : forall T, ftv_sch (sch_mono T) [=] ftv_typ T.
Proof. intro T. unfold ftv_sch, sch_mono; simpl. fsetdec. Qed.
Lemma frv_sch_mono : forall T, frv_sch (sch_mono T) [=] frv_typ T.
Proof. intro T. unfold frv_sch, sch_mono; simpl. fsetdec. Qed.

Definition tr_supp (st:tsub) (sr:rsub) (A:atoms) : Prop :=
  (forall a, a `notin` A -> st a = typ_Var a) /\
  (forall r, r `notin` A -> sr r = row_Var r).

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
  intros D S V k Hs a Ha. unfold ext.
  destruct (AtomSetImpl.mem a V) eqn:Em.
  - apply AtomSetFacts.mem_iff in Em. exfalso. apply Ha. fsetdec.
  - apply Hs. fsetdec.
Qed.

Lemma sat_ext_mono : forall D V k S k0 T,
  supp_ok D S -> (forall a, a `in` V -> a `notin` S) ->
  sat D k0 T -> sat (ext D V k) k0 T.
Proof.
  intros D V k S k0 T Hs Hv H. destruct T; simpl in *; try exact H.
  unfold ext. destruct (AtomSetImpl.mem a V) eqn:Em.
  - apply AtomSetFacts.mem_iff in Em. rewrite (Hs a (Hv a Em)) in H.
    inversion H; subst; apply finer_any.
  - exact H.
Qed.

(* The renaming step shared by every binder that generalizes ([let] and a
   recursive group): rename the quantified variables of [gen G T1 k] to fresh
   names so the substitution cannot capture them (see the story above).  It
   returns the composed substitution under which the bound term is typed, the
   sorts that term is typed under, the substituted scheme, and the facts the
   body needs about it. *)
Lemma tsubst_gen_core : forall G T1 k st sr G' A D D' S S',
  supp_ok D S -> supp_ok D' S' -> kres D D' st ->
  ctx_subst st sr G G' -> tr_supp st sr A -> tr_compat st sr G G' ->
  exists (s' : scheme) (st1 : tsub) (sr1 : rsub) (A1 N : atoms) (k' : sort_fn),
    kres (ext D (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx G)) k) (ext D' N k') st1 /\
    ctx_subst st1 sr1 G G' /\ tr_supp st1 sr1 A1 /\ tr_compat st1 sr1 G G' /\
    N [=] AtomSetImpl.diff (ftv_typ (ap_typ st1 sr1 T1)) (ftv_ctx G') /\
    supp_ok (ext D' N k') (S' `union` N) /\
    sch_subst st sr (gen G T1 k) s' /\
    sch_equiv s' (gen G' (ap_typ st1 sr1 T1) k') /\
    (forall x, tr_compat st sr ((x ~ gen G T1 k) ++ G) ((x ~ s') ++ G')).
Proof.
  intros G T1 k st sr G' A D D' S S' HS HS' Hk Hcs Hsupp Hcompat.
  destruct Hsupp as [HsuppT HsuppR].
  destruct Hcompat as [HcT [HcFr [HcRt HcRfr]]].
  set (s := gen G T1 k).
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
  { intros D1 D1' Hk1 W HW.
    exact (casch_inst st sr g gr s Hginv Hgrinv HgfixS HgrfixS HstQ HsrQ Hnc1 Hnc2 Hnc3 Hnc4
             D1 D1' Hk1 W HW). }
  assert (Hbridge : sch_equiv (casch st sr g gr s)
                      (gen G' (ap_typ st sr (ren_typ g gr (s_body s))) (fun a => s_sk s (g a)))).
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
  set (k' := fun a => k (g a)).
  assert (Hap1 : ap_typ (fun a : Atom.atom => st (g a)) (fun r : Atom.atom => sr (gr r)) T1
                 = ap_typ st sr (ren_typ g gr T1))
    by apply ap_precomp.
  assert (HEq : NS [=] AtomSetImpl.diff (ftv_typ (ap_typ (fun a : Atom.atom => st (g a)) (fun r : Atom.atom => sr (gr r)) T1))
                                        (ftv_ctx G')).
  { rewrite Hap1. exact (proj1 Hbridge). }
  exists (casch st sr g gr s), (fun a => st (g a)), (fun r => sr (gr r)), A2, NS, k'.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - (* the bound term's substitution respects the sorts *)
    intros a.
    destruct (AtomSetImpl.mem a V) eqn:EV.
    + apply AtomSetFacts.mem_iff in EV.
      assert (HgaNS : g a `in` NS) by (apply amap_in; exists a; auto).
      assert (HgaQ : g a `in` amap g (s_tq s)) by (rewrite HsTQ; exact HgaNS).
      rewrite (ext_in D V k a EV). cbv beta. rewrite (HstQ (g a) HgaQ). cbn [sat].
      rewrite (ext_in D' NS k' (g a) HgaNS). unfold k'. rewrite Hginv. apply finer_refl.
    + apply AtomSetFacts.not_mem_iff in EV.
      rewrite (ext_out D V k a EV).
      destruct (List.in_dec Atom.eq_dec a Ng) as [HIn|HNIn].
      * assert (a `notin` S) by (pose proof (HgNB a HIn); unfold Bav in H; fsetdec).
        rewrite (HS a H). apply sat_any.
      * assert (Hga : g a = a) by (apply Hgfix; [ rewrite HsTQ; exact EV | exact HNIn ]).
        cbv beta. rewrite Hga. apply (sat_ext_mono D' NS k' S' _ _ HS').
        -- intros b Hb. assert (HbQ : b `in` amap g (s_tq s)) by (rewrite HsTQ; exact Hb).
           assert (b `notin` Bav) by (apply HgF; exact HbQ). unfold Bav in H. fsetdec.
        -- apply Hk.
  - (* the bound term is typed under the substitution run after the renaming *)
    apply ctx_subst_precomp; [ exact Hginv | exact Hcs | exact HgfixG | exact HgrfixG ].
  - (* tr_supp *)
    split.
    + intros a Ha. unfold A2 in Ha.
      assert (g a = a).
      { apply Hgfix; [ fsetdec | ]. intro Hc. apply lset_in in Hc. fsetdec. }
      cbv beta. rewrite H. apply HsuppT. fsetdec.
    + intros r Hr. unfold A2 in Hr.
      assert (gr r = r).
      { apply Hgrfix; [ fsetdec | ]. intro Hc. apply lset_in in Hc. fsetdec. }
      cbv beta. rewrite H. apply HsuppR. fsetdec.
  - (* tr_compat *)
    unfold tr_compat. repeat split.
    + intros a Ha. cbv beta. rewrite (HgfixG a Ha). apply HcT; exact Ha.
    + intros a Ha. cbv beta. rewrite (HgfixG a Ha). apply HcFr; exact Ha.
    + intros r Hr. cbv beta. rewrite (HgrfixG r Hr). apply HcRt; exact Hr.
    + intros r Hr. cbv beta. rewrite (HgrfixG r Hr). apply HcRfr; exact Hr.
  - exact HEq.
  - apply supp_ok_ext. exact HS'.
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
      uniq G' -> supp_ok D S -> supp_ok D' S' -> kres D D' st ->
      ctx_subst st sr G G' -> tr_supp st sr A -> tr_compat st sr G G' ->
      typing D' G' e (ap_typ st sr T)) /\
  (forall D G fs R, field_typing D G fs R -> forall st sr G' D' A S S',
      uniq G' -> supp_ok D S -> supp_ok D' S' -> kres D D' st ->
      ctx_subst st sr G G' -> tr_supp st sr A -> tr_compat st sr G G' ->
      field_typing D' G' fs (ap_row st sr R)).
Proof.
  apply typing_field_mutind.
  - (* T_Var: the scheme in [G] has a matching scheme in [G'], and any instance
       of the first becomes an instance of the second. *)
    intros D G x s T Hu Hb Hi st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat.
    destruct (ctx_subst_binds _ _ _ _ _ _ Hcs Hb) as [s' [Hb' Hss]].
    apply T_Var with (s := s'); auto. apply (Hss D D' Hk). exact Hi.
  - intros D G n T Hu Hs st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat.
    apply T_Num; auto. eapply sat_ap; eauto.
  - intros D G d Hu st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat. apply T_Dec; auto.
  - intros D G Hu st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat. apply T_True; auto.
  - intros D G Hu st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat. apply T_False; auto.
  - (* T_Abs: the body is typed with the parameter added at [T1]. *)
    intros L D G e T1 T2 Ht IH st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat. simpl.
    apply T_Abs with (L := L `union` dom G'). intros x Hx.
    apply (IH x ltac:(fsetdec) st sr ((x ~ sch_mono (ap_typ st sr T1)) ++ G') D' A S S').
    + constructor; [ assumption | fsetdec ].
    + assumption.
    + assumption.
    + assumption.
    + apply ctx_subst_cons; [ apply sch_subst_mono | assumption ].
    + assumption.
    + apply tr_compat_cons_mono; assumption.
  - (* T_App: nothing is bound. *)
    intros D G e1 e2 T1 T2 Ht1 IH1 Ht2 IH2 st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat.
    simpl in *. eapply T_App; [ eapply IH1 | eapply IH2 ]; eauto.
  - (* T_Let: the renaming of the generalized variables is [tsubst_gen_core];
       here we rebuild the [let] around it. *)
    intros L0 D G e1 e2 T1 T2 k Hgv Ht1 IH1 Ht2 IH2 st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat.
    destruct (tsubst_gen_core G T1 k st sr G' A D D' S S' HS HS' Hk Hcs Hsupp Hcompat)
      as [s' [st1 [sr1 [A1 [N [k' [Hk1 [Hcs1 [Hsupp1 [Hcompat1 [HN [HS1 [Hsi [Hbr Hcx]]]]]]]]]]]]]].
    apply T_Let with (L := L0 `union` dom G') (T1 := ap_typ st1 sr1 T1) (k := k');
      [ assumption | | ].
    + eapply typing_pw.
      * apply (IH1 st1 sr1 G' (ext D' N k') A1
                 (S `union` AtomSetImpl.diff (ftv_typ T1) (ftv_ctx G)) (S' `union` N)
                 Hu' (supp_ok_ext _ _ _ _ HS) HS1 Hk1 Hcs1 Hsupp1 Hcompat1).
      * intros a. apply ext_set_eq. exact HN.
    + intros x Hx.
      apply typing_sch_equiv_ctx with (G := (x ~ s') ++ G').
      * apply (IH2 x ltac:(fsetdec) st sr ((x ~ s') ++ G') D' A S S').
        -- constructor; [ assumption | fsetdec ].
        -- assumption.
        -- assumption.
        -- assumption.
        -- apply ctx_subst_cons; [ exact Hsi | exact Hcs ].
        -- exact Hsupp.
        -- apply Hcx.
      * apply ctx_equiv_cons; [ exact Hbr | apply ctx_equiv_refl ].
  - (* T_LetMono: the binding is monomorphic, so it is the function case. *)
    intros L0 D G e1 e2 T1 T2 Ht1 IH1 Ht2 IH2 st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat.
    apply T_LetMono with (L := L0 `union` dom G') (T1 := ap_typ st sr T1);
      [ eapply IH1; eauto | ].
    intros x Hx.
    apply (IH2 x ltac:(fsetdec) st sr ((x ~ sch_mono (ap_typ st sr T1)) ++ G') D' A S S').
    + constructor; [ assumption | fsetdec ].
    + assumption.
    + assumption.
    + assumption.
    + apply ctx_subst_cons; [ apply sch_subst_mono | assumption ].
    + assumption.
    + apply tr_compat_cons_mono; assumption.
  - (* T_Letrec: the members are typed with the group's record type [R]
       monomorphic, and the body with the group generalized like a [let]. *)
    intros L0 D G fs e2 R T k Hfg Hfs IHfs Ht2 IH2 st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat.
    destruct (tsubst_gen_core G (typ_Record R) k st sr G' A D D' S S' HS HS' Hk Hcs Hsupp Hcompat)
      as [s' [st1 [sr1 [A1 [N [k' [Hk1 [Hcs1 [Hsupp1 [Hcompat1 [HN [HS1 [Hsi [Hbr Hcx]]]]]]]]]]]]]].
    apply T_Letrec with (L := L0 `union` dom G') (R := ap_row st1 sr1 R) (k := k');
      [ assumption | | ].
    + intros p Hp.
      eapply field_typing_pw.
      * apply (IHfs p ltac:(fsetdec) st1 sr1
                 ((p ~ sch_mono (ap_typ st1 sr1 (typ_Record R))) ++ G') (ext D' N k') A1
                 (S `union` AtomSetImpl.diff (ftv_typ (typ_Record R)) (ftv_ctx G)) (S' `union` N)).
        -- constructor; [ assumption | fsetdec ].
        -- apply supp_ok_ext. exact HS.
        -- exact HS1.
        -- exact Hk1.
        -- apply ctx_subst_cons; [ apply sch_subst_mono | assumption ].
        -- assumption.
        -- apply tr_compat_cons_mono; assumption.
      * intros a. apply ext_set_eq. exact HN.
    + intros p Hp.
      apply typing_sch_equiv_ctx with (G := (p ~ s') ++ G').
      * apply (IH2 p ltac:(fsetdec) st sr ((p ~ s') ++ G') D' A S S').
        -- constructor; [ assumption | fsetdec ].
        -- assumption.
        -- assumption.
        -- assumption.
        -- apply ctx_subst_cons; [ exact Hsi | exact Hcs ].
        -- exact Hsupp.
        -- apply Hcx.
      * apply ctx_equiv_cons; [ exact Hbr | apply ctx_equiv_refl ].
  - (* T_Record *) intros D G fs R Ht IH st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat. simpl.
    apply T_Record. eapply IH; eauto.
  - (* T_Proj *) intros D G e l T R Ht IH st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat.
    eapply T_Proj. simpl in IH. eapply IH; eauto.
  - (* T_Conv *) intros D G e T T' Ht IH Hte st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat.
    eapply T_Conv; [ eapply IH; eauto | apply teq_ap; auto ].
  - (* T_Unit *) intros D G Hu st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat. simpl. apply T_Unit; auto.
  - (* T_Str *) intros D G q Hu st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat. simpl. apply T_Str; auto.
  - (* T_If *)
    intros D G e1 e2 e3 T Ht1 IH1 Ht2 IH2 Ht3 IH3 st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat.
    simpl in *. eapply T_If; [ eapply IH1 | eapply IH2 | eapply IH3 ]; eauto.
  - (* T_ToFloat: the operand's sort carries over; [Float] is closed. *)
    intros D G e A0 Ht IH Hs st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat. simpl.
    eapply T_ToFloat; [ eapply IH; eauto | eapply sat_ap; eauto ].
  - (* T_Bin: the signature is stable under a kind-respecting substitution. *)
    intros D G e1 o e2 A0 B0 R0 Ht1 IH1 Ht2 IH2 Hs st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat.
    eapply T_Bin; [ eapply IH1; eauto | eapply IH2; eauto | eapply bin_sig_ap; eauto ].
  - intros D G Hu st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat. simpl. apply FT_nil; auto.
  - intros D G l e T fs R Ht1 IH1 Ht2 IH2 st sr G' D' A S S' Hu' HS HS' Hk Hcs Hsupp Hcompat. simpl.
    eapply FT_cons; [ eapply IH1 | eapply IH2 ]; eauto.
Qed.

Lemma kres_id : forall D, kres D D idt.
Proof. intros D a. unfold idt. simpl. apply finer_refl. Qed.

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
  - apply ctx_subst_weaken. intros x s Hb. apply binds_weaken; exact Hb.
  - split; intros a Ha; reflexivity.
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
   derivation uses internally is replaced by [Int], which satisfies every
   sort; it is only variables in the finite support of the source environment
   that can carry a sort, so only those need replacing. *)
Lemma typing_denv_agree : forall D0 D Sd0 Sd S0 G e T,
  typing D0 G e T -> supp_ok D0 Sd0 -> supp_ok D Sd ->
  ftv_ctx G [<=] S0 -> ftv_typ T [<=] S0 ->
  (forall a, a `in` S0 -> D a = D0 a) ->
  typing D G e T.
Proof.
  intros D0 D Sd0 Sd S0 G e T Hty HS0 HS HG HT Hag.
  set (A := AtomSetImpl.diff Sd0 S0).
  set (st := fun a : typvar => if AtomSetImpl.mem a A then typ_Int else typ_Var a).
  assert (Hst : forall a, a `in` S0 -> st a = typ_Var a).
  { intros a Ha. unfold st. destruct (AtomSetImpl.mem a A) eqn:Em; [ | reflexivity ].
    apply AtomSetFacts.mem_iff in Em. unfold A in Em. apply AtomSetFacts.diff_iff in Em. tauto. }
  assert (Heq : ap_typ st idr T = T).
  { apply ap_typ_fix.
    - intros a Ha. apply Hst. apply HT. exact Ha.
    - intros r Hr. reflexivity. }
  rewrite <- Heq.
  apply (proj1 typing_tsubst_gen_mut D0 G e T Hty st idr G D A Sd0 Sd).
  - eapply typing_uniq; exact Hty.
  - exact HS0.
  - exact HS.
  - intros a. unfold st. destruct (AtomSetImpl.mem a A) eqn:Em.
    + simpl. exact I.
    + apply AtomSetFacts.not_mem_iff in Em. simpl.
      destruct (AtomSetImpl.mem a S0) eqn:Em2.
      * apply AtomSetFacts.mem_iff in Em2. rewrite (Hag a Em2). apply finer_refl.
      * assert (Hnot : a `notin` Sd0).
        { intro Hc. apply Em. unfold A. apply AtomSetFacts.diff_iff. split; [ exact Hc | ].
          apply AtomSetFacts.not_mem_iff in Em2. exact Em2. }
        rewrite (HS0 a Hnot). apply finer_any.
  - apply ctx_subst_fix.
    + intros a Ha. apply Hst. apply HG. exact Ha.
    + intros r Hr. reflexivity.
  - split.
    + intros a Ha. unfold st. destruct (AtomSetImpl.mem a A) eqn:Em; [ | reflexivity ].
      apply AtomSetFacts.mem_iff in Em. contradiction.
    + intros r Hr. reflexivity.
  - unfold tr_compat. repeat split; intros a Ha.
    + rewrite (Hst a (HG a Ha)). simpl. fsetdec.
    + rewrite (Hst a (HG a Ha)). simpl. fsetdec.
    + unfold idr; simpl. fsetdec.
    + unfold idr; simpl. fsetdec.
Qed.

(* A value typed at the body of a generalization has every instance of the
   generalization.  The bound term is typed under the environment extended
   with the sorts the scheme records; the instance is typed in an environment
   that agrees with the ambient one on the context. *)
Lemma typing_inst_gen : forall D0 D Sd0 Sd G v T1 k W,
  typing (ext D0 (AtomSetImpl.diff (ftv_typ T1) (ftv_ctx G)) k) G v T1 ->
  inst D W (gen G T1 k) ->
  supp_ok D0 Sd0 -> supp_ok D Sd ->
  (forall a, a `in` ftv_ctx G -> D a = D0 a) ->
  typing D G v W.
Proof.
  intros D0 D Sd0 Sd G v T1 k W Hv [st [sr [Hst [Hsr [HW Hsat]]]]] HS0 HS Hag.
  cbn [gen s_tq s_rq s_body s_sk] in Hst, Hsr, HW, Hsat.
  set (V := AtomSetImpl.diff (ftv_typ T1) (ftv_ctx G)) in *.
  set (Vr := AtomSetImpl.diff (frv_typ T1) (frv_ctx G)) in *.
  set (A := AtomSetImpl.diff Sd0 (ftv_ctx G)).
  set (st' := fun a : typvar =>
        if AtomSetImpl.mem a V then st a
        else if AtomSetImpl.mem a A then typ_Int else typ_Var a).
  assert (Hst'G : forall a, a `in` ftv_ctx G -> st' a = typ_Var a).
  { intros a Ha. unfold st'.
    destruct (AtomSetImpl.mem a V) eqn:E1.
    - apply AtomSetFacts.mem_iff in E1. unfold V in E1. apply AtomSetFacts.diff_iff in E1. tauto.
    - destruct (AtomSetImpl.mem a A) eqn:E2; [ | reflexivity ].
      apply AtomSetFacts.mem_iff in E2. unfold A in E2. apply AtomSetFacts.diff_iff in E2. tauto. }
  assert (HW' : W = ap_typ st' sr T1).
  { rewrite HW. apply ap_typ_ext.
    - intros a Ha. unfold st'. destruct (AtomSetImpl.mem a V) eqn:E1; [ reflexivity | ].
      apply AtomSetFacts.not_mem_iff in E1.
      assert (HaG : a `in` ftv_ctx G).
      { destruct (AtomSetProperties.In_dec a (ftv_ctx G)) as [H|H]; [ exact H | ].
        exfalso. apply E1. unfold V. apply AtomSetFacts.diff_iff. split; [ exact Ha | exact H ]. }
      rewrite (Hst a ltac:(intro Hc; apply E1; exact Hc)).
      destruct (AtomSetImpl.mem a A) eqn:E2; [ | reflexivity ].
      apply AtomSetFacts.mem_iff in E2. unfold A in E2. apply AtomSetFacts.diff_iff in E2. tauto.
    - intros r Hr. reflexivity. }
  rewrite HW'.
  apply (proj1 typing_tsubst_gen_mut _ G v T1 Hv st' sr G D (V `union` A `union` Vr)
           (Sd0 `union` V) Sd).
  - eapply typing_uniq; exact Hv.
  - apply supp_ok_ext. exact HS0.
  - exact HS.
  - intros a. unfold st'. destruct (AtomSetImpl.mem a V) eqn:E1.
    + apply AtomSetFacts.mem_iff in E1. rewrite (ext_in D0 V k a E1). apply Hsat. exact E1.
    + apply AtomSetFacts.not_mem_iff in E1. rewrite (ext_out D0 V k a E1).
      destruct (AtomSetImpl.mem a A) eqn:E2.
      * simpl. exact I.
      * apply AtomSetFacts.not_mem_iff in E2. simpl.
        destruct (AtomSetProperties.In_dec a (ftv_ctx G)) as [H|H].
        -- rewrite (Hag a H). apply finer_refl.
        -- assert (Hnot : a `notin` Sd0).
           { intro Hc. apply E2. unfold A. apply AtomSetFacts.diff_iff. split; assumption. }
           rewrite (HS0 a Hnot). apply finer_any.
  - apply ctx_subst_fix.
    + intros a Ha. apply Hst'G. exact Ha.
    + intros r Hr. apply Hsr. intro Hc. apply AtomSetFacts.diff_iff in Hc. tauto.
  - split.
    + intros a Ha. unfold st'.
      destruct (AtomSetImpl.mem a V) eqn:E1.
      * apply AtomSetFacts.mem_iff in E1. exfalso. apply Ha. fsetdec.
      * destruct (AtomSetImpl.mem a A) eqn:E2; [ | reflexivity ].
        apply AtomSetFacts.mem_iff in E2. exfalso. apply Ha. fsetdec.
    + intros r Hr. apply Hsr. intro Hc. apply Hr. fsetdec.
  - unfold tr_compat. repeat split; intros a Ha.
    + rewrite (Hst'G a Ha). simpl. fsetdec.
    + rewrite (Hst'G a Ha). simpl. fsetdec.
    + rewrite (Hsr a ltac:(intro Hc; apply AtomSetFacts.diff_iff in Hc; tauto)). simpl. fsetdec.
    + rewrite (Hsr a ltac:(intro Hc; apply AtomSetFacts.diff_iff in Hc; tauto)). simpl. fsetdec.
Qed.
