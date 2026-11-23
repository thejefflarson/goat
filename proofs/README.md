# goat proofs

The mechanized soundness development for goat's type system (ADR 0008, issue
#70). This directory is **outside** the cargo workspace and the
`wasm32-unknown-unknown` build on purpose: it holds no Rust and no manifest, so
`Cargo.toml`'s `members` never lists it and the wasm32 job's explicit `-p` list
never reaches it. It is built by its own CI job (`.github/workflows/coq.yml`),
independent of the Rust `check`/`wasm32` jobs and the Kani `verify` job.

B2 (this directory's first cut) stands up the pipeline and lands two
infrastructure lemmas end-to-end. The soundness proof itself (progress +
preservation) is B3 (#71).

## Files

| File | Role |
| --- | --- |
| `goat.ott` | The typeset spec: the lockstep twin of `docs/semantics.md` (n-ary program/application, n-ary arrow). Source for the typeset rules, **not** for Coq. |
| `goat_ln.ott` | The mechanization source: the locally-nameless core that Coq is generated from. See "Why two Ott files". |
| `Goat_ott.v` | Generated from `goat_ln.ott` by Ott. Committed (see "Generated, committed"). |
| `GoatProofs.v` | Hand-written locally-nameless infrastructure lemma (`subst_exp_fresh_eq`) and derived row-equivalence reflexivity. |
| `GoatRows.v` | Row-equivalence theory: L1 (equivalence + congruence), L2 (head-shape "no confusion" + arrow/record inversion up to `≅`), L2′ (the §3 per-label characterization, soundness direction), L3 (row surfacing). Over `typ`/`row`/`teq`/`req` only. |
| `GoatDefs.v` | The declarative type system and operational semantics (`docs/semantics.md` §4–§6), hand-written over the generated syntax: type/row substitution, free-variable predicates, schemes, contexts, instantiation, generalization, values, small-step reduction, typing. A method field of a record literal is `fs_meth` (`l :m e`): it steps and substitutes as a plain field, `T_Obj` (with `meths_shared` and `unroll_eq`) types a literal that has one, and `fs_plain` makes the record a spread, restrict or record arithmetic builds a plain one. |
| `GoatMu.v` | The type algebra of the one binder in `typ`: unrolling `open_typ`, local closure `lct`, how substitution commutes with unrolling (`ap_open_mut`), how type equality respects unrolling (`teq_open`, `teq_unroll`), and the guard `gd`/`guarded` with its closure under substitution and `teq`. |
| `GoatTags.v` | Tag groups (phase 3): the algebra of a group type's parameter spine and of a tag's payload (`teq_spine_inv`, `teq_tag_payload`, `ap_tag_payload`), and the arms of a `match` under substitution. |
| `GoatRecTypes.v` | Iso-recursive types: worked examples. `P = mu t. {moved: (t) -> t; x: Int}`, a `fold`ed ball, a `step` that unfolds its receiver, a run, and what has no derivation (a fold missing its `x`, self-application, a record with no function). |
| `GoatElab.v` | Elaboration (phase 5, stage 3). `erase` removes `fold` and `unfold`; `erase_step` and `erase_traps` say a step or trap of an elaborated term is a step or trap of its erasure, or one erasure cannot see (`unfold(fold v) --> v`). `unroll_eq n` is the bounded-unrolling type equality T ~~[n] T' (reflexive, symmetric, monotone in `n`, stable under substitution). `chain` and `coerce` are the head coercions, with `coerce_typing` and `erase_coerce`. The converse of `erase_step` is in `GoatElabConverse.v` and a decision procedure for `unroll_eq` in `GoatUnrollEqb.v`. |
| `GoatUnrollEqb.v` | A decision procedure for the bounded-unrolling equality (phase 5, stage 4, part 2). `unroll_eqb n T T'` compares by shape and unrolls a mu that meets another head, spending the budget; `unroll_eqb_sound` says a `true` answer is a derivation of `unroll_eq n T T'`. It needs no assumed-pairs set, since the budget bounds the search. Not complete: `unroll_eq` may go through a middle type (`UE_trans`) the search never builds, and rows are compared by syntax. |
| `GoatKnot.v` | Tying a knot (phase 5, stage 4, part 3). `knot x T` is the recursive type the checker's `tie_ty_knot` solves `x` to: `T` with `x` replaced by the new binder's index. `knot_unrolls`: unrolling it once gives `T` with `x := knot x T`, so `x` and `T` differ by one unrolling (`knot_unroll_eq`), and `knot_chain_fold` / `knot_chain_unfold` give the one `fold` or `unfold` that repairs it. `gdb` decides the checker's guard (every mention under a record field and a function type) and `gdb_abs_guarded` says the body of the knot is `guarded`, which `T_Fold` and `T_Unfold` need. |
| `GoatInferKnot.v` | The knot-tying unifier (phase 5, stage 4, part 3). `unify_k` and `unify_kr` are `unify_t` and `unify_r` with three changes: a variable that occurs in the type it meets is bound to a knot when every mention is guarded and the knot has the variable's sort (`bind_k`); a mu that meets another head is unrolled, spending fuel, and two mus are compared by their bodies first; a bound index meets only itself, so a substitution's images stay closed. `bind_k` also refuses a type with a mu inside whose body is not guarded (`mgb`), which never happens to a type W built and gives `GoatInferGuard.v` its invariant without a hypothesis on the unifier's arguments. `unify_k_sound`: a unifier `s` it returns satisfies `OkS s`, respects sorts, and makes `s T1 ~~[m] s T2` for some `m` (rows: `unroll_row`). `infer` calls it through `unify_co` (`GoatCoerce.v`). |
| `GoatGuard.v` | Guarded recursive types (phase 5, stage 4, part 4). `mg T` says every `typ_Mu B` inside `T` has a guarded body (`guarded B`: every mention of its index sits under a record field and a function type); `mgb` decides it. `gsub s` says a substitution's images are closed and `mg`; it survives application and composition, and `mg_knot` says a knot of a guarded type whose variable is guarded is guarded. |
| `GoatInferGuard.v` | W's recursive types are guarded (phase 5, stage 4, part 4). `infer_guarded`: if `infer_closed_elab fuel e = Some (D, T, e')` then `mg T`, and `infer_closed_env_guarded` says the same of `infer_closed_env`. The proof follows the algorithm. `unify_k_gsub`: every substitution the knot-tying unifier returns is `gsub`, with no hypothesis on its arguments, because `bind_k` refuses a type with an unguarded mu inside. `unify_t_gsub`: the plain unifier's substitutions are `gsub` when its arguments are `mg`, as is every type W builds from the context. |
| `GoatElabConverse.v` | The typed converse of `erase_step` (phase 5, stage 4, part 2). For a well-typed elaborated term `e`, if `erase e` steps to `r` then `e` reaches, by steps that include `unfold(fold v) --> v`, a term whose erasure is `r` (`erase_converse`, and for a run of the erased term, `erase_converse_multistep`). The proof uses canonical forms and `value_reach`: a typed term whose erasure is a value reaches a value by steps erasure cannot see. Untyped it is false. |
| `GoatInferElab.v` | W returns the elaborated term (phase 5, stage 4). `infer_elab fuel e = Some (D, e', T)` gives `typing D nil e' T` and `erase e' = e` (`infer_elab_sound`). `e'` is `e` with the head `fold` and `unfold` of the joins written in, so it is `e` only when no recursive type meets its unrolling. `infer_mu_free` and `infer_fold_free` are gone: W builds recursive types now, and `erase e' = e` is proved directly; `infer_guarded` (`GoatInferGuard.v`) states what W's types satisfy instead. |
| `GoatCoerce.v` | The coercion pass (phase 5, stage 4, part 3b). `coerce_dec` decides which head coercions take one type to another and `coerce_dec_sound` says they form a `chain`; `teq_dec` finds `teq` by syntax or by a `unify_t` run that changes neither type. `unify_co` is the unifier W calls: `unify_t` first (the two types are then `teq` and nothing is inserted), then `unify_k` and `coerce_dec`; a difference below a function type or a record field has no head coercion and the unifier fails (a deep coercion). `unify_co_sound` gives `OkS s`, respected sorts and `chain cs (s T1) (s T2)`, the join lemma W's soundness proof uses. `chain_apT`: a chain survives a substitution. |
| `GoatClose.v` | Closing a term over a variable (phase 5, stage 4, part 3b). W infers a binder's body opened at a fresh variable and returns the elaborated body closed over it again (`cl`). `lce k e` says the indices of `e` are below `k`; closing and opening undo each other on such a term (`cl_open_mut`), opening a closed body is substitution (`open_cl_mut`), and `erase` commutes with closing (`erase_cl_mut`). |
| `GoatInferW.v` | Algorithm W (the algorithm itself, calling the unifiers of `GoatInfer.v`, `GoatInferKnot.v` and `GoatCoerce.v`), returning a fifth component, the elaborated term, built from the elaborated subterms alone: no substitution rewrites it. `infer_closed_elab` is the program-level entry and `infer_closed_env` drops the term. A recursive group's members are unified with the slots of their names by `unify_grp`: where `unify_t` fails and the member is a function meeting a function type, the parameters are unified and the head coercions that take the result to the slot's result go under the member's lambda (`unify_mem`, `mem_co`, `pw_co`; `unify_grp_sound` in `GoatInferSound.v`), so `g = program(p) do {a: p, b: g(p)} done` gets a recursive result with a `fold` where the record is made. A record literal with a method field (`fs_meth`) goes through `infer_obj`, which gives every method one receiver (a record of slot variables for the literal's fields and a row variable for what a use adds) and infers each body with it in scope, and `tie_obj`, which then unifies each slot with its field's type, so a method that mentions its receiver gets a recursive type and a field that meets its slot up to unrolling gets the head coercions. `infer_sound` (`GoatInferSound.v`) proves the result is typed by `T_Obj`: `tie_obj_sound`, `meth_rel`, `meths_shared_of`. |
| `GoatMethods.v` | Methods in the iso calculus, worked: a `ball` with a `moved` method that spreads `self`, `ball.moved()`, `step(ball)`, their runs, the erasure back to the source program, a head coercion, and what has no derivation without the unfold. Then the shared receiver (`T_Obj`, ADR 0034): `ball` with its method marked, typed at the receiver's row empty and at `{size: Int}` (what `big = {...ball, size: 10}` needs, with `big.moved()`), a literal with three methods that share one receiver, and `obj_one_receiver`: a typed literal with a method hands back one row for all its methods. |
| `GoatCompleteFuel.v` | Completeness of W, stage 7.5, L0 (`docs/design/phase7-proof-plan.md` section 4). `unify_t_mono`, `unify_r_mono`: a `Some` at one fuel is the same `Some` at every larger fuel. W, `unify_co` and `coerce_dec` are not monotone (they fall back to a second search when the first returns `None`, which also means "out of fuel"), so the completeness induction states each run as `Stable` (true from some fuel on): `Stable_and`, `Stable_below`, `unify_co_stable` (a plain unifier success is a stable coercion-free `unify_co` success), and `infer_app_stable` as the pattern of one construct. |
| `GoatCompleteInst.v` | Stage 7.5, L1. The instance order: `sch_le D s s'` (every instance of `s` is an instance of `s'`, the free variables of `s'` are free in `s`, stable under an `ext`/`extr` of `D` that misses them), `ctx_le`, and `typing_ctx_le` (a derivation under the instances' context is one under the more general context, the `typing_ftv_mono` proof with the instance order). Two examples show the order is neither empty nor total. |
| `GoatCompleteGen.v` | Stage 7.5, L1. A sort or kind reads only the variables of the type (`sat_loc`, `rkok_loc`), and an instance of a generalization carries the sorts of a type from the derivation's kinding environment to the instance's (`gm_sat`, `gm_rkok`). |
| `GoatCompleteMono.v` | Stage 7.5, L1. `gen_mono`: the derivation's generalization of `S2 T'` over its pinned context is an instance of `S2` applied to the algorithm's `gen_ren`, given `kres`/`rkres` of `S2` and that `S2` sends the algorithm's free variables to the derivation's (`frozen`). `let_pin_frozen`: a variable the algorithm pins is frozen by the derivation's `lit_pinned` premise. |
| `GoatCompleteLet.v` | Stage 7.5, L1. `gen_mono_let`: `gen_mono` with the algorithm's pin `let_pin`, the let case's comparison as the induction states it. |
| `GoatSatTeq.v` | Stage 7.6b. `sat_teq`, `rsat_req`: `sat` and `rsat` are invariant under `teq` and `req` (both directions), spine sorts included; a `Maybe` entry reads through its presence (`Bool` is absent, anything else is a field), so a sorted variable may be sent to any representative of a type's class. |
| `GoatCompleteRows.v` | Stage 7.6, L2. The row combinatorics: sizes `tsz`/`rsz` that `teq`/`req` preserve, and for a closed spine of fields `surface_req` (the first entry of a label can be swapped to the front), `req_of_pi` (equal field lists at every label make two rows `req`: the converse of `req_pres` that the plan asked for), `req_cancel` and `rewrite_row_found`. |
| `GoatCompleteUnify.v` | Stage 7.6, L2. `unify_t_complete`, `unify_r_complete`, `unify_co_complete`: on types of base types, variables, arrows and (with `b = true`) records of closed rows, a substitution that unifies two types up to `teq`/`req` and respects the sorts makes the unifier succeed (`Stable`) with a substitution `S` factors through (`Res`), with no variable invented. `rewrite_row_lacking` shows `rewrite_row` now succeeds at a row variable that lacks the label (stage 7.6c); the invention of the factoring substitution for the fresh variables of `rewrite_row` and `bind_row` is the part of rows with tail variables that is not proved. |
| `GoatMeta.v` | The metatheory: locally-nameless infrastructure (via a computable `lc_at`), `typing_regular`, canonical forms (L7), typing inversions, and **Progress**. |
| `GoatSubst.v` | The Hindley–Milner substitution-algebra groundwork: the type/row-substitution algebra and `teq_ap`, the structural L4 lemmas (`typing_sch_equiv_ctx`, `typing_ftv_mono`), the free-variable facts of a bijective renaming, and `gen_more_gen` (generalizing over a smaller context quantifies more, at the sorts the extra atoms already had). What `GoatBij`/`GoatHM`/`GoatSound` build on. |
| `GoatBij.v` | Freshening infrastructure (finite-atom permutations, `mk_rename`) feeding the T-Let freshening (#151). |
| `GoatHM.v` | Capture-avoiding scheme substitution `casch` and its instance-preservation `casch_inst` (#151). |
| `GoatNum.v` | The integer arithmetic behind whole-number literals and the 64-bit `Int` range, kept apart because ZArith defines notations that clash with Metalib's `x ~ T`. |
| `GoatLit.v` | Reads the argument of `e_num` as an integer, so `e_num 3` works in a file that never imports ZArith (and in the generated printer table). |
| `GoatPhase1.v` | Phase 1 of ADR 0037: worked examples (and the inference algorithm run on a few of them) for `Unit`, strings, `if`, the operators on `Int`, `Float`, `String` and `Bool`, and the Int-to-Float coercion; and the generic operators: a numeral at `Float`, `float(1.5)`, and a `let`-bound function used at `Int` and `Float` but not at `String`. Which programs type, what they evaluate to, which trap (division by zero, overflow), and which have no derivation (`1 < "a"`, `true + true`, `if 1 then ...`, a numeral-sorted function used at `String`), and a numeral in a record that stays one type across the body's uses (`shared_numeral_not_int`). |
| `GoatPhase2.v` | Phase 2 of ADR 0037: worked examples for the value restriction (which terms `is_gen_value` accepts), a generalized binding used at two types, a recursive group (its typing, its unrolling, a run) and a group member that is not a function (no derivation). |
| `GoatPhase3.v` | Phase 3 of ADR 0037: worked examples for tag groups: `Hit(3)`, a `match` that runs, an `else`, `Link(1, Link(2, Empty))`, and what has no derivation (a match missing a tag, a repeated arm, a tag outside the group, a list that mixes element types). |
| `GoatPresence.v` | Presence rows (phase 4): the old row equivalence `req0` (no `pre` or `abs`), the normalizer `nf`, `presence_inv` (a record literal's row equals `l ^ P : T ; R` only when `P` is `Unit`, or `Bool` with the row equal to `R` and no `l`), and `rm` (the first field of a row) respecting `req`. |
| `GoatRecArith.v` | Record arithmetic (ADR 0012): `row_sig` (every field of a row takes the operator), `bin_sig_record`, and `zip_typing`, which pairs the fields of two records typed by rows equivalent to one numeric row and types the record of operator applications that `rec_zip` builds. Progress and preservation use it. |
| `GoatSpread.v` | Spread and restrict (phase 4): the inversions, and `spread_step_typing` and `restrict_step_typing`, which preservation uses. |
| `GoatPhase4.v` | Phase 4 of ADR 0037: worked examples for spread (an update, an extension, one `set_x` for a record with and without `x`), restrict, and what has no derivation (a type-changing update, a restrict on a record without the label). |
| `GoatRowKinds.v` | Stage 7.2: worked examples for row kinds: a comparison of two records whose open row has an `Eq` tail, a spread onto a row variable that lacks the label, and `let set_x = program(p) do {...p, x: 1} done in set_x({y: true})`, where the scheme quantifies a row variable that lacks `x`. |
| `GoatPhase6.v` | Phase 6: worked examples for the `Eq` sort and structural comparison: `()` compares, a function does not, `same = program(x) do x == x done` is used at `Int`, `String` and `Unit`, records compare equal in either field order, by their second field when the first ties, and in label order, nested records compare, a record holding a function is not `Eq`; tags compare by position (`Low < Medium < High`), a list lexicographically with a prefix first, and a recursive tree by `fold`. The differential test covers the algorithm. |
| `GoatRecArithExamples.v` | Record arithmetic, worked: a record sum, a nested product with the fields in another order at both levels, a record with a non-number field (no derivation). |
| `GoatSound.v` | The general substitution lemma `typing_tsubst_gen_mut` (freshening the let-generalized variables so `gen` commutes with a capturing substitution, `casch_gen_sch_equiv`, and so the sorts they carry survive), with `typing_weaken` (L4) and `typing_denv_agree` / `typing_inst_gen` (a derivation moves between two kinding environments); then term substitution **L6a/L6b** (`typing_subst_gen_mut`), **Preservation** and **Soundness**. All axiom- and admit-free. |
| `GoatGrammar.v` | Generated from `grammar/goat.peg` by `parser/examples/emit_coq.rs` (`make gen-grammar`); `make check-grammar` fails on drift. Never hand-edited. |
| `GoatPeg.v` | Ford-style relational PEG semantics of the generated grammar over a token stream, and **T2** `peg_deterministic`. |
| `GoatDen.v` | The denotation of core-fragment parse trees as Ott terms (curried, locally nameless via `close_exp`, labels interned by first occurrence, a block's leading function bindings grouped as a `letrec` by `bind_group`, a record with a spread as the nest `spread_nest`, a rest pattern as the lets and restricts of `unpack`, tags resolved through a table of declared tags, `match` arms read as the calculus reads them, a list literal as `Link` and `Empty`), and its local closure. |
| `GoatShape.v` | The forests the core rules can produce, the shape of each core node's children, and totality: every valid, complete core tree whose tags are declared has a denotation. |
| `GoatParse.v` | **T1** `parse_denotes_lc`, with the two-pass tag table (`Den_goat`, `goat_known`). |
| `GoatLex.v` | The lexer (phase 8, stage 1, ADR 0030 amendment): `lex` from a list of Unicode code points to tokens. Each class of token is a function that returns how many code points it matches; the lexer takes the longest, the earlier class on a tie, and an unmatched code point is a token of its own. The two Unicode predicates for code points of 128 and up are arguments; ASCII is decided in the model. Tied to `parser::lexer::lex` by `make differential` (`differential/lex_driver.ml`). |
| `GoatLexSpec.v` | What makes `lex` a lexer: `lex_concat` (the tokens spell the source, no gap, no overlap) and `lex_nonempty`; `step_longest` (the token is the longest any class matches) and `step_class` (a class matches it, no earlier class matches that much); `word_boundary` (a keyword or `true`/`false` is never followed by an identifier character, so `done` is a keyword and `doner` a name); a name and a whitespace run are maximal (`name_maximal`, `whitespace_maximal`). |
| `GoatLexBarrier.v`, `GoatLexStep.v` | Whitespace is a barrier: a class of token that holds no whitespace reads the input only up to the first whitespace code point, so two inputs that agree up to it give it the same match (`number_stable`, `name_sm_stable`, `word_len_stable`, `prefix_len_stable`). `step_stab`: the token at the start of `x ++ z` is the token at the start of `x ++ z'` when it ends inside `x` and `z`, `z'` start with whitespace or are empty, with two guards for the classes that can reach into `z'` (a comment, and `start at`). |
| `GoatLexText.v` | T1 over text: `lex_toks` maps the lexer's tokens to the PEG's, `parse_text_denotes` says a source that `lex` and the PEG parse denotes a locally closed term, and `lex_toks_trivia_independent` says the parser's tokens depend only on the tokens that are not whitespace or comments. The two Unicode predicates are declared here (`xid_start_hi`, `xid_cont_hi`), and `parse_text_denotes_xid` is T1 at them, resting on exactly those two. |
| `GoatLexEdit.v` | The formatter's link (ADR 0041): `edits_preserve_tokens`. Replace whitespace tokens of the lexed text, one after another, by non-empty runs of whitespace that keep a line break after a comment and do not make `start at` out of `start` and the next token, and the text of the result lexes to the result, so its tokens other than whitespace are the original's; `edits_preserve_parse` says it parses the same. An edit that inserts a gap or leaves none can join two tokens and is not covered. |
| `GoatLexExtract.v` | Extracts `lex` to OCaml for the differential test. |
| `GoatPegTac.v` | Helper tactics (`pok`, `pfail`) that build derivations of the PEG relation. No theorem lives there. |
| `GoatPrint.v` | The printer: a closed core term to its parse tree and token stream, binders named by depth (`v0`, `v1`, ...), mirroring the curried style of `checker/tests/core_roundtrip.rs`. |
| `GoatPrintChain.v`, `GoatPrintPrim.v`, `GoatPrintBlock.v`, `GoatPrintParse.v` | The parse side of T3: a printed chain, each primary and postfix, records and bindings, and every printed block, each with the ordered choices that could commit wrongly shown not to. |
| `GoatPrintDen.v`, `GoatPrintLabels.v`, `GoatPrintTop.v` | The denotation side: the printed tree denotes the term, the label table is the first-occurrence table of the term's labels, the top rule parses it. |
| `GoatRoundtrip.v` | **T3** `print_parse_roundtrip`. |
| `GoatRoundtripExample.v` | Terms meeting T3's hypotheses (a spread among them), and one failing the label hypothesis. |
| `GoatPrec.v` | Operator runs (phase 8, stage 3): `resolve`, the fold of a flat run of operands and operators into a term by `prec` (`or` loosest, left-associative, `not` at level 3 taking the operand after it), the same stack algorithm as `lower.rs`. The connectives are derived forms: `a and b` is `if a then b else false`, `a or b` is `if a then true else b`, `not a` is `if a then false else true`, so the calculus does not change. `resolve_total` (a run of operands joined by operators always resolves) and `resolve_lc` (it is locally closed). |
| `GoatPrecTable.v` | Generated by `checker/tests/precedence.rs`: for every operator pending on lowering's stack and every infix operator that arrives next, whether lowering folds the first, observed by lowering real source. Coq proves `prec` gives the same 210 answers, so `prec` and `lower.rs` cannot drift. |
| `GoatPrinterTable.v` | Generated by `checker/tests/core_roundtrip.rs`: 200 terms (strings, `Float` literals, `if` with and without an `else`, spreads, and operators included) with the token streams the Rust printer writes; Coq checks its printer agrees. |
| `GoatExample.v` | A fuel-bounded PEG interpreter, sound for the relation, parsing small programs; T1 applied to three of them, the recursive-group program `countdown` shown to denote the `GoatPhase2.v` term that types as an `Int`, and a rest pattern shown to denote two restricts. |
| `GoatTagExample.v` | Tags, `match` and lists, worked (phase 8, stage 4): the tables the `tag` declarations of GoatPhase3.v's `list_g`, `level` and `shot` build, a list literal shown to denote the term GoatPhase3.v types as a list of Int, and T1 applied to a program that declares a tag and matches on it. |
| `GoatLoopExample.v` | Loops, worked (phase 8, stage 5): `repeat`, `for ... from ... to` and `for ... in` each shown to denote the tail-recursive term of `GoatDen.v` (`counted`, `each_term`), and T1 applied to a program that runs each. |
| `GoatBlockExample.v` | The block, worked (phase 8, stage 6): an empty program, a program that ends in a binding, `a; b`, `program()`, `f()`, and a function written after a value it uses, each shown to denote a locally closed term. |
| `GoatAssumptions.v` | `make check-assumptions` fails unless T1, T2, T3, `progress`, `preservation`, `soundness`, `infer_closed_sound`, `erase_step`, `erase_traps`, `coerce_typing`, `infer_elab_sound`, `unroll_eqb_sound`, `erase_converse`, `erase_converse_multistep`, `knot_unrolls`, `unify_k_sound`, `coerce_dec_sound`, `unify_co_sound`, `infer_guarded`, `lex_concat`, `step_longest`, `word_boundary`, `parse_text_denotes`, `edits_preserve_tokens` and `edits_preserve_parse` print "Closed under the global context", and `parse_text_denotes_xid` rests on exactly the two Unicode parameters. |
| `_CoqProject`, `Makefile` | Build. |

## Phase 1: Unit, strings, `if`, and the operators on Int, Float, String, Bool (ADR 0037)

`goat_ln.ott` has the types `Int`, `Float`, `Unit` and `String`, the terms
`unit`, a whole-number literal `n` (an integer), a `Float` value `d` (opaque),
a string literal, `if e1 then e2 else e3`, `e1 o e2` and the coercion
`float(e)`, and the operator syntax `o`. `GoatDefs.v` adds:

- the typing rules `T_Num` (an `Int`), `T_Dec` (a `Float`), `T_Unit`, `T_Str`,
  `T_If`, `T_ToFloat` and `T_Bin`, where `T_Bin` asks the operator signature
  `bin_sig` (ADR 0017, ADR 0036) which operand types the operator takes and
  what it gives. Both operands of an arithmetic or comparison operator have one
  type, so an `Int` meets a `Float` only through `float(e)`;
- the reduction rules for `if`, operators and the coercion, with the value of
  an operator given by the relation `bin_step`;
- `Int` is a signed 64-bit integer: `+ - *` and `//` `%` step only when the
  result is in `[int_min, int_max]` (`in_int`), `//` and `%` floor, and a zero
  divisor or a result outside the range is a trap;
- `Float` is opaque. `e_dec d` carries a payload no rule reads, and every
  `Float` operation (`+ - * / // %`, `float(n)`) relates its operands to every
  `Float`, and a `Float` comparison to either boolean. That is an unspecified
  function written as a relation, so it needs no axiom or parameter, and a
  theorem about it holds for any function a compiler computes;
- a trap: `traps e k` says evaluation reaches an integer operation that divides
  by zero (`trap_div_zero`) or leaves the 64-bit range (`trap_overflow`).
  `progress` says a closed well-typed term is a value, steps, or traps, and
  `soundness` carries that along any run.

The coercion `float(e)` is what elaboration inserts wherever the checker accepts
an `Int` for a `Float`: a call whose parameter is a `Float`, an operator with a
`Float` on one side, a literal settled as a `Float`. The calculus has no
subtyping, so the rule is `T_ToFloat`: `float(e)` is a `Float` when `e` is an
`Int`. Preservation and progress cover it like any other term. That the
elaborator inserts it exactly where the checker accepts an `Int` for a `Float`
is not a theorem: the differential test checks it (`differential/README.md`),
by writing `float(e)` from the checker's own node types and requiring the
proven algorithm to accept the result with the checker's type.

`progress`, `preservation` and `soundness` hold with 0 admits, and
`make check-assumptions` checks every theorem in the list under "Theorems checked
closed" below.

What the model leaves out, each checked against `goat check` and `goat run`
(`docs/semantics.md` section 9): the embedded target's 32-bit `Int`, IEEE
rounding, infinities and NaN (a `Float` is opaque), the `trap()` builtin,
IEEE behavior inside a compound (a `Float`
inside a record or tag relates to every result, so a NaN's place in the order is not
modeled) and the `Ordered` sort. A comparison takes the sort `Eq` (`sat`): `Int`,
`Float`, strings, booleans and `Unit`, a record of `Eq` fields, a recursive type
whose body is `Eq`, and a tag group whose parameters are. A function inside a type
makes it not `Eq`. `cmp_rel` is the order (ADR 0036): two records compare field by
field, in the order of their labels, each label read as its first field in either
record, so `{x: 1, y: 2} == {y: 2, x: 1}` (`cr_rec`); two tags of one group compare
by position, then by payload (`cr_con_eq`, `cr_con_lt`, `cr_con_gt`); `fold` compares
its contents (`cr_fold`). `cmp_total` shows two values of one `Eq` type always
compare, by induction on the size of the first value, so a recursive type needs no
well-founded type order; `rec_align` is the record alignment fact it rests on, and
`cmp_unerase` carries it through elaboration.

What phase 6 does not prove, and where each gap is tracked:

- **Sort propagation (#623), closed in phase 7 stage 7.3.** The unifiers return the
  kinding environment and push a sort onto the variables inside the type a
  variable binds to (see "Algorithm W with sorted variables"), so
  `f = program(x) do same({p: x}, {p: x}) done` is accepted by W, as the checker
  accepts it. The five hand-written programs of #623 are in the corpus.
- **NaN inside a compound.** The compiler orders a number by `==`, then `<`, else
  greater, so `{x: 0} > {x: NaN}` and `{x: NaN} > {x: 0}` both hold, which breaks
  antisymmetry and contradicts ADR 0036's "a NaN sorts after everything". The model
  does not decide it (`cr_float` relates to every result) and no order law is
  proved for `Float`-bearing values. This is an open question for the owner
  (`docs/design/phase6-proof-plan.md`, section 9, question 1).
- **`sat_b` on `mu` and tag groups (closed, stage 7.4).** `sat_b_iff` proves
  `sat_b D k T = true <-> sat D k T`, including `mu` (the body at `Eq`), a bound
  index, and a tag group (`spine_sat_b`, which checks each parameter a tag uses),
  so W decides a comparison at a recursive type or tag group as the calculus does.
  The reader no longer skips a comparison in a program with tags.
- **The label bridge.** The calculus orders labels as `nat`, the checker by name.
  The corpus reader numbers labels in sorted-name order (`number_labels_by_name`,
  `checker/examples/core_corpus.rs`), so a record comparison in the corpus means
  what the checker means. The differential test compares types, not values, so this
  and mono's derived comparison computing `cmp_rel` are trusted, not proved.
- **Order laws.** Reflexivity, antisymmetry and transitivity of `cmp_rel` on
  `Float`-free values (what `sort` relies on) are not proved; soundness does not
  need them.

One gap is accepted: `5 // 0` typed at `Float` (two bare numerals the
checker settles as `Float`, as in `f(5 // 0)` for `f = program(x) do x + 1.5 done`)
steps as two `Int`s in the calculus, so it traps with `Div_by_zero`, while the
compiled program divides decimals and gives `inf`. `+ - *` and numerals are generic over the sorts `Numeric` and
`Literal`, below. The inference algorithm (`GoatInfer.v`) covers the
whole of phase 1: `Unit`, strings, Float values, `if`, `float(e)` and the
operators, besides functions, bindings and records, and it infers the generic
operators (below). A comparison unifies both operands with one fresh variable
of sort `Eq` (`generic_sort`), so `x < 1.5` fixes `x` to `Float` and
`program(a, b) do a == b done` is generic.

The parser fragment widens in step: a string, a `Float` literal (a `TDec` token
that denotes the opaque `e_dec`), a conditional with or without an `else` (the
missing branch is `e_unit`), and an operator run of any length (phase 8, stage 3, below).
`GoatDen.v` reads a run through `GoatPrec.v`'s `resolve` (`Den_math`; `DM_bin` is
still the one-operator case); the printer parenthesises the operand of an
operator when it is a binding or another operation, so a printed term never
contains a run.

## Phase 2: recursion and the value restriction (ADR 0037)

`goat_ln.ott` has one new term, `letrec x = { fs } e2`: a recursive group. The
group's name `x` is one locally-nameless binder over the record of the group's
functions `fs` and over the body `e2`; a member `f` of the surface group
`letrec f1 = e1, ..., fn = en in e` is the projection `x.l` of its label. The
surface form is the n-ary letrec of `docs/semantics.md`; the single binder is
what the locally-nameless infrastructure handles, as the curried single-binder
`program` is for `program(x1, ..., xk)`. `GoatDefs.v` adds:

- `is_gen_value`, the value restriction's predicate (ADR 0027): unit, literals,
  names, functions, and records of those, with `float(v)` of a value and a
  `letrec` around a value (what substituting an unrolled group for its name
  needs);
- `T_Let` generalizes only when `is_gen_value e1`; `T_LetMono` types any `let`
  with a monomorphic binding, and a computed binding has no other rule;
- `T_Letrec`: the members (`fn_group`: all `program` literals) are typed with
  the group's name at the record type of the members, and the body with the
  name generalized against the context, so each use of a member instantiates
  the group afresh;
- `st_letrec`: the group unrolls at once, replacing its name in the body by
  the record of its members, in each of which the name is the group again.

`progress`, `preservation` and `soundness` cover the new terms with 0 admits.
`step_gen` (a syntactic value stays one when it steps) keeps `T_Let` after
`st_let1`; `is_gen_subst` keeps it under the term substitutions of `ST-Beta`,
`ST-LetV` and `ST-Letrec`; `tsubst_gen_core` is the capture-avoiding renaming
that `T_Let` and `T_Letrec` share in the type-substitution lemma.

The inference algorithm covers these forms (`GoatInfer.v`, `GoatInferRec.v`,
`GoatInferSound.v`): a `let` of a computed value is typed monomorphically
(`T_LetMono`), and a `letrec` infers its members with the group's name bound
to a row of fresh variables, unifies each member's type with its variable
(`unify_pw`), and generalizes the group's record type for the body
(`T_Letrec`). The grammar has no new
form, but the parser fragment now reads the surface group: the function
bindings that lead a block (`f = program(x) do ... done`, ADR 0003) are one
`letrec`, each member named by its position (`GoatDen.v`, `DK_hoist`). Every
occurrence of a member's name in the members and the rest of the block becomes
the projection of that member from the group (`bind_group`). A function binding
after a value binding is placed by what it uses (phase 8 stage 6, see "The
block"). A binding whose value is a parenthesised function is a plain `let`, so
the printer parenthesises a function that is a binding's value. T1 covers groups, and
`GoatExample.v` shows one program parsing to the group `GoatPhase2.v` types. T3
does not (decided: deferred to the tail of phase 8): the printer does not write a
`letrec`, which would need the group's projections printed as bare member names.
The lexer stays trusted until phases 3 to 6 land, then is verified once (decided).

## Phase 3 (ADR 0037, amended): iso-recursive types

`goat_ln.ott` has two new types, `bv i` (the index of an enclosing `mu`) and
`mu T` (the body counts the `mu` as index 0), and two new terms `fold(e)` and
`unfold(e)`; a `fold` of a value is a value. `GoatDefs.v` adds:

- `open_typ k U T` (replace the index `k` by `U`, lower the ones above), the
  closure predicate `lct k T`, and the guard `gd`/`guarded`: every mention of
  the index sits under a record field and under a function type (ADR 0032);
- `T_Fold`: `fold(e) : mu B` when `mu B` is closed, `B` is guarded and `e` has
  the unrolling `open_typ 0 (mu B) B`; `T_Unfold` is its converse. `fold` carries
  no type annotation, so terms stay free of types;
- `st_unfold_fold` (`unfold(fold(v)) --> v`) and the two congruences.

`teq_mu` is congruence only. There is no unrolling equation: that is what makes
the recursion iso, and it keeps `teq_Mu_inv` (a type equal to a `mu` is a `mu`)
a plain induction. The binder is a de Bruijn index written into the grammar, not
an Ott binder: a cofinite `teq_mu` would make `teq_ap` (type equality under
substitution) need a fresh atom the substitution fixes, and so a finite-support
hypothesis on every substitution that reaches `T_Conv`. The index has no sort
(ADR 0038), and a `mu` satisfies only `k_Any`, so `kres` is untouched.

One price: `ap_open_mut` (substitution commutes with unrolling) needs the
substituted types closed. `lc_sub st sr` says so, and it rides along where a
substitution did already: in `inst` (a generic instance has closed images), in
`tr_supp` (so in `OkS`, the algorithm's substitution invariant) and in
`casch_inst`. `GoatInfer.v` stays sound by construction: its occurs check (`occT`, `occR`)
refuses to bind a variable to a type with a free index (`lcb`), which never
fires on a type the algorithm builds. In this phase W produced no `mu`
(`docs/design/w-recursive-types-plan.md`, option C); phase 5 gave it knots and
retired `GoatInferMuFree.v`, and "Phase 5" below says what W returns now.

`progress`, `preservation`, `soundness` and `infer_closed_sound` hold with 0
admits. `canon_mu` (a value typed at a type equal to a `mu` is a `fold`) joins
the canonical forms; `teq_unroll` (equal `mu`s have equal unrollings) retypes a
fold at an equal type. `GoatRecTypes.v` shows the guard doing its job
(`no_fold_at_self_application`: a `fold` has no type equal to
`mu t. (t) -> t`, through any conversion). The parser fragment is unchanged:
`mu`, `fold` and `unfold` have no surface syntax, so T1 to T3 only gained the
cases that say a printed term is never one.

The elaboration theorem and the type of an open-extensible recursive receiver
came in phase 5 (below). Phase 3's tag signature keeps closed payload types in
the sense of `lct`, since a payload under a `mu` mentions an index.

## Phase 3 (ADR 0037, continued): tag groups, construction and `match`

The language design this models is `docs/design/closed-tags-plan.md` with the
owner's later decisions on #500: every tag is closed, and a tag belongs to a
group. `tag G = A | B(_, G) | C(Int, _)` declares tags whose payload slots are a
concrete type, the group itself (the recursion), or `_`, an implicit parameter
of the group: a fresh type at each construction, and the same type throughout
one value. A tag without parentheses has no payload. A lone `tag Ping` is a
group of one. A `match` pins its scrutinee to one group and must name every tag
of it unless it has an `else`. Lists are the prelude group
`tag List = Empty | Link(_, List)`, with `[..]` as sugar. The plan is
`docs/design/phase3-proof-plan.md`; its owner answers are on #452.

What the calculus gained, in `goat_ln.ott` (and `Goat_ott.v`, regenerated):

- a type `grp w T`, the type of a value of the group `w`, whose argument `T`
  spells the group's parameters as a spine `(T0) -> (T1) -> ... -> Unit`;
- a term `con w tg (e)`, tag `tg` of the group `w` around the payload `e`, and a
  term `match w (e) with ars`, whose arms `ars` are a list ending in nothing
  (the arms must then be exhaustive) or in `else e`. Each arm
  `tg x => e` binds one variable, the payload. The arms are a third nonterminal
  in the mutual block with `exp` and `fields`, so Ott generates `open`, `lc`,
  `fv` and `subst` for them, and every proof that inducts over terms gained a
  third conjunct.

`GoatDefs.v` defines the group declaration `gdecl` (the group's name as bytes,
then a list of tags, each a list of slot codes; the name makes groups nominal, so
two declarations of one shape are two types and `if c then Ping else Pong` with
`tag A = Ping` and `tag B = Pong` has no type, `ping_or_pong_rejected`. The slot
codes are `0` the group, `1` to `5` the concrete `Int`, `Float`, `Bool`,
`Unit`, `String`, and `6 + j` the group's parameter `j`), the payload type of a
tag (`tag_payload`: `Unit` for no slots, else the closed record of the slots,
labelled by position), the arms functions (`arms_find`, `arms_default`,
`arms_idx`, `arms_wf`), and:

- `T_Con`: tag `tg < length (gtags w)` around a payload of `tag_payload w Ts tg` has type
  `grp w (spine Ts)`. This is where the group instantiates its `_`s: `Ts` is any
  list of types;
- `T_Match`: a scrutinee of type `grp w (spine Ts)`; arms that name each tag at
  most once, only tags of `w`, and either every tag or an `else` (`arms_wf`,
  ADR 0037 decision 1, exhaustiveness in the rules); every arm typed with its
  variable at `tag_payload w Ts tg`, and the `else` typed, at one result type;
- `st_con1`, `st_match1`, `st_match_arm` (the arm for a finished construction's
  tag runs on the payload) and `st_match_else`; `tr_con` and `tr_match` carry a
  trap out of the subterm.

`GoatTags.v` is the algebra the proofs need: equal parameter spines are equal
lists (`teq_spine_inv`), equal parameters give equal payloads
(`teq_tag_payload`), substitution acts on the parameters alone
(`ap_tag_payload`), and substituting into arms keeps `arms_wf`.

`progress`, `preservation`, `soundness` and `infer_closed_sound` hold with 0
admits and no axiom (`make check-assumptions`). The new canonical form is
`canon_grp_spine` (a value at a group type is a construction of one of its
tags around a value), and `match_inv` and `con_inv` are the inversions
preservation uses. `GoatPhase3.v` shows the rules working: `Hit(3)`, a `match`
that runs, an `else`, `Link(1, Link(2, Empty))`, `Empty` at every element type,
and what has no derivation (a match missing a tag, a repeated arm, a tag outside
the group, `Link(true, Link("a", Empty))`).

Modelling calls made for this phase, each the conservative choice, none a
language change:

- **Groups are nominal.** The recursion is carried by the group's declaration,
  not by `mu` and `fold`: `T_Con` and `T_Match` are the fold and unfold of a
  group type, built in. A value of a recursive group needs no `fold` term, and
  `mu` stays what ADR 0032 uses it for (recursive records). The declaration `w`
  sits in the type and in the term, so no tag signature threads through the
  judgment: every `typing` statement is unchanged, and no theorem has a
  well-formedness hypothesis, because the rules are sound for any `w`. (The
  owner's Q1 option A, a signature on the judgment, was written before the
  declaration moved into the group type; the declaration in the type removes
  the threading cost Q1 was about.)
- **Parameters are a spine.** The arguments of `grp w T` are `(T0) -> (T1) -> ... -> Unit`
  rather than a list or a row, so type equality (`teq_grp`) reuses the arrow's
  congruence and `typ` gains no list. A parameter slot beyond the spine reads
  `Unit`; the checker never builds one.
- **Concrete slots are the five base types.** Records, lists and functions as
  concrete payload slots (the checker allows them) need slot codes that name a
  type, not a number; that changes `gdecl`, `slot_ty` and the denotation, so it
  is left to its own ticket.
- **Rank** (ADR 0036) is the tag's position in `w`. No phase-3 rule reads it.
- **Else with full cover** is accepted, as the checker accepts it. A repeated
  arm has no derivation.
- **A payload is the closed record of its slots** (a tag with one slot, too);
  surface `Tag(a, b)` denotes to a construction of the record `{0: a; 1: b}` and
  an arm to projections of its variable, as in the plan's Q7.
- **Literal `match`, list patterns, `for`, destructuring** are not calculus
  forms (plan Q8): they denote to `if v == lit` and to nested `match`es.

Outside the proven fragment, by decision D5(b): the host's event and shape
families (`Tick`, `KeyDown`, `Circle`, `Line`, and the rest of the vocabulary)
stay open rows in the checker and are not modelled here. A `match` on a host
event with an `else` is the checker's, not the calculus's.

The parser and printer proofs (T1 to T3) are unchanged: the printed fragment
never contains `con` or `match` (`scoped` excludes them), and the denotation
functions (`close_exp_rec`, `bind_group_rec`, `inst_rec`) gained the cases that
carry the arms through. Tag declarations, construction and `match` have no
denotation yet, so `rule_map.rs` exempts `e_con` and `e_match`.

### Algorithm W on tag groups

`GoatInfer.v` infers `con` and `match`, and `unify_t` unifies two group types
when their declarations are equal (`gdecl_eq_dec`) by unifying their spines;
different declarations do not unify. `infer_closed_sound` and `infer_mu_free`
still hold with 0 admits and no axiom (`make check-assumptions`).

- `con w tg (e)`: `tg` must be a tag of `w`. The algorithm infers `e`, takes
  `nparams w` fresh parameters (the largest `6 + j` among the slot codes, less
  five), unifies the payload's type with `tag_payload w Ts tg`, and returns
  `grp w (spine Ts)` under the unifier.
- `match w (e) with ars`: `arms_wf_b w ars` must hold (each tag at most once,
  only tags of `w`, an `else` or every tag; `arms_wf_b_sound`). The scrutinee is
  unified with `grp w (spine Ts)` at fresh parameters. `infer_arms` then walks
  the arms in order against a result variable: an arm's payload binder is typed
  by `tag_payload w Ts tg`, every arm's type is unified with the result so far,
  and the parameters and context are re-applied after each unifier. One binder
  name (`fresh_var` of the whole match) serves every arm, so `T_Match`'s
  `forall x notin L` is stated once.
- `arms_typ` is `T_Match`'s two premises on the arms (each arm under a binder,
  the `else`); `arm_lift` carries an arm's derivation across a later
  substitution, the one new fact beyond the lifts `ite` already needs.
- `mu_free` now looks into a group's spine, so `infer_mu_free` says the
  parameters are `mu`-free too (`mf_tag_payload`).

What waits: the differential test for tag programs. The checker's tag groups
(#517) are not on master, so `core_corpus.rs` cannot write them yet;
`differential/README.md` lists what the corpus and the driver must add. The
typeset `goat.ott` and `docs/semantics.md` do not yet state the group rules.

## Phase 4 (ADR 0037, ADR 0033): spread and restrict

The language design this models is ADR 0033: `{...p, x: v}` updates a field `p`
has, keeping its type, or extends `p` with a field it lacks, and the type of a
function that does either, `program(r) do {...r, x: 1} done`, carries a
presence variable (Rémy) so that one function serves both records. The plan is
`docs/design/phase4-proof-plan.md`.

What the calculus gained, in `goat_ln.ott` (and `Goat_ott.v`, regenerated):

- a row entry `l ^ P : T ; R` (`row_Maybe`): the field `l` at `T`, present when
  the presence `P` is `Unit`, absent when it is `Bool`, unknown when it is a
  type variable. `P` is a type, so a presence variable is a `typ_Var` and
  `ftv`, `gen`, `inst` and substitution handle it unchanged; the pun is the
  checker's (`PRESENT = Unit`, `ABSENT = Bool`);
- five rules of row equivalence: congruence, `l ^ Unit : T ; R ≅ l : T ; R`,
  `l ^ Bool : T ; R ≅ R` when `l # R` (the spine of `R` names no `l` and ends in
  `nil`; `rlacks`, embedded before the relation), and the swaps of a `Maybe`
  entry past an `Ext` entry or another `Maybe` entry;
- terms `spread(e1, l, e2)` and `restrict(e, l)`. A multi-field spread is the nest
  of single ones, and a rest pattern with `k` labels is `k` restricts;
- `T_Spread` (`e1 : {l ^ P : T ; R}`, `e2 : T` gives `{l : T ; R}`) and
  `T_Restrict` (`e : {R0}` and `rm l R0 T R` gives `{R}`, where `rm` is the first
  `l` of the row, skipping other entries); `st_spread1`, `st_spread2`,
  `st_spread` (`fs_set`: replace the first `l`, or add one in front),
  `st_restrict1`, `st_restrict` (`fs_drop`), and `tr_spread1`, `tr_spread2`,
  `tr_restrict`.

`progress`, `preservation` and `soundness` hold with 0 admits and no axiom
(`make check-assumptions`); `typing D G e T` is unchanged. Progress needs no new
idea: a finished base is a record literal, and `fs_set` and `fs_drop` are total.
Preservation is where the model pays. `presence_inv` (`GoatPresence.v`) answers
which presence the type of a literal's row can have: the normalizer `nf` turns a
`Unit` entry into a field and drops a `Bool` entry whose normalized tail lacks
its label; `nf` commutes with every `req` rule up to `req0`; and a literal's row
has no `Maybe` entry, which `req0` counts. So the literal's row meets
`l ^ P : T ; R` only through `Unit` (the field is there, and an update keeps its
type up to equality) or a lacking `Bool` (no `l`, and the row equals `R`).
`rm` respects `req` by induction on the derivation, both directions for `sym`.
The guard `gd` of a recursive type skips the field type of an absent entry,
because `abs` drops it and a guard that counted it would not survive equality.

Modelling calls made for this phase, each the conservative choice:

- **`lacks` is syntactic in `req`.** `l # R` holds only of a closed spine, so it
  is stable under substitution and `teq_ap` needs no new idea. A row variable's
  lacks facts live in the kinding environment instead and reach the typing
  judgment through `T_SpreadL` (the section on row kinds below), so a spread
  whose base ends in a row variable that lacks the label (the remainder of a rest
  pattern put back) has a derivation.
- **Scoped labels stay.** A row may hold a label twice and the first one wins, so
  a spread or restrict touches the first. The checker's rows never do (ADR 0033
  decision 5); the calculus accepts a superset of types, which is sound.
- **A presence is a type, ill-sorted ones included.** `P` instantiated at `Int`
  is stuck: no rule reads the slot except `pre` and `abs`, so such a row never
  equals a record literal's, and no value has it.
- **Restrict carries its premise.** `T_Restrict` states `rm`, not "`R0` is
  `l : T ; R`", because preservation of the latter needs `req` to cancel an
  entry (the completeness direction `GoatRows.v` does not prove); `rm` commutes
  with `req` instead.
- **The `method` flag of a row entry is not modelled** (phase 6).

Algorithm W infers both terms (`GoatInfer.v`, `GoatInferUnify.v`).
`rewrite_row` presents a label with a presence: `Unit` for a field the row has,
`Bool` for a closed row that has none, and for a row variable a binding to
`l ^ p : a ; r'` with `p` fresh. `unify_r` treats a plain field as a presence of
`Unit` and unifies the presences, the field types and the rests. A spread
unifies the base with `{l ^ p : T2 | r}` and returns `{l : T2 | r}`, and a
restrict unifies with `{l : a | r}` and returns `{r}`. `infer_sound`,
`infer_closed_sound` and `infer_mu_free` keep 0 admits and no new axiom, and the
differential test compares spread and restrict programs (`differential/README.md`).
The calculus's syntactic `l # R` holds of a closed row alone; phase 7 stage 7.3b
extends the algorithm with lacks facts on row variables.

What waits, each its own ticket: the typeset `goat.ott`. The parser fragment now reads spread and rest patterns (the
section on the parser claim says how).

## Phase 5 (ADR 0037, amended): the elaboration theorem, methods and dot calls

**What is proved.** The checker's types are equi-recursive (a type equals its
unrolling); the calculus's are iso-recursive (`fold` and `unfold` are terms). The
two meet in Algorithm W, which returns the elaborated term:

- **The elaboration theorem.** `infer_elab_sound`: if W accepts a program `e` it
  returns `(D, e', T)` with `typing D nil e' T` and `erase e' = e`. `erase` drops
  `fold` and `unfold`. There is no second, equi-recursive typing relation, so
  "the same behaviour" is `erase_step` (a step of `e'` is a step of its erasure,
  or an `unfold(fold v) --> v` that erasure cannot see), `erase_traps`, and the
  typed converse `erase_converse` / `erase_converse_multistep` (a step of the
  erasure is reached by `e'`).
- **W ties knots.** `unify_k` binds a variable to a recursive type when it
  occurs in the type it meets and every mention is guarded (`knot_unrolls`,
  `unify_k_sound`). The equality it decides is the bounded-unrolling relation
  `T ~~[n] T'`, searched by `unroll_eqb` (`unroll_eqb_sound`, not complete).
- **Head coercions.** Where a type meets its unrolling, W writes one `fold` or
  `unfold` at that node (`coerce_dec_sound`, `coerce_typing`, `unify_co_sound`),
  so `erase e' = e` holds exactly. A difference below a function type or a record
  field would need an eta-expansion; W refuses such a program (a deep coercion).
- **Guardedness.** `infer_guarded`: every recursive type W returns is guarded
  (every mention of the binder sits under a record field and a function type), so
  `T_Fold` and `T_Unfold` apply. `bind_k` refuses a type with an unguarded mu
  inside, which gives the knot-tying unifier's substitutions this property with
  no hypothesis on its arguments.
- **Recursive groups.** `unify_grp` ties the members of a `letrec` group to the
  slots of their names and puts the head coercions of a member's result under its
  lambda (`unify_grp_sound`), so `g = program(p) do {a: p, b: g(p)} done` elaborates
  with a `fold` where the record is made.
- **Methods and `self`.** `fs_meth` is a field of the record spine that steps and
  substitutes as a plain one. `T_Obj` types a literal with methods and gives all
  of them one receiver (`meths_shared`: each method's type equal up to unrolling
  to a function of one receiver, the literal's row plus a tail): the shared
  receiver of ADR 0034 decision 2 is a rule. A spread, restrict or record
  arithmetic builds a plain record (`fs_plain`). W's literal case (`infer_obj`,
  `tie_obj`) infers each method body with the receiver in scope and unifies the
  slots with the fields afterwards; `infer_sound` types the result by `T_Obj`.
  `GoatMethods.v` works the `ball` with a `moved` method through, with `big =
  {...ball, size: 10}` typed at a wider receiver.
- **Dot calls in the parser fragment.** `r.f(a)` on any receiver is in T1: a path
  repeats the receiver (`DP_dot_path`), another receiver binds a hidden `let`
  (`DP_dot_bind`), and `r::f(a)` is `(r.f)(a)` (`DP_take`). See "The parser claim".

**Theorems checked closed** (`GoatAssumptions.v`, `make check-assumptions`, 27):
`peg_deterministic`, `parse_denotes_lc`, `print_parse_roundtrip`, `progress`,
`preservation`, `soundness`, `infer_closed_sound`, `erase_step`, `erase_traps`,
`coerce_typing`, `infer_elab_sound`, `unroll_eqb_sound`, `erase_converse`,
`erase_converse_multistep`, `knot_unrolls`, `unify_k_sound`, `coerce_dec_sound`,
`unify_co_sound`, `infer_guarded`, `cmp_total`, `cmp_unerase`, `lex_concat`,
`step_longest`, `word_boundary`, `parse_text_denotes`, `edits_preserve_tokens` and
`edits_preserve_parse`. 0 admits, no axioms. The lexer theorems hold for any answer
of the two Unicode predicates; `parse_text_denotes_xid` is the same T1 at the two
declared parameters `xid_start_hi` and `xid_cont_hi` (whether a code point of 128
or more may start or continue an identifier: the tables of `unicode_ident`, checked
by the differential test), and `make check-assumptions` requires it to rest on
those two and nothing else.

**What the differential test covers.** `make -C proofs differential` on this
commit: 44773 programs written, 43348 compared with 0 mismatches, 1412 skipped
by the driver, and the lexer differential 78617 sources, 4351098 tokens, 0
disagreements. Inferring a recursive group before the value bindings between its
members (#628) brought in 59 of the 65 programs it used to skip; the other 6 use
a later feature or are real cycles the checker rejects. The reader numbers labels
in name order, which wrote 206 more programs than before (a corpus line repeats
only if its term, mode and verdict do) and changed no checker verdict. Of the 43
programs whose checker type is recursive, 32 are compared and 11 refused. Phase 8
stage 6 reads a program that ends in a binding (the value of the last binding: the
checker gives `x = 1` the type of `x`), a function or call with no parameters (a
hidden parameter pinned to the unit value, and a call passing the unit value), and
an `if` without an `else` (`ite c t unit`); the three skips are gone and their
programs, 70 of them before this stage, are compared with 0 mismatches. The
corpus reader's skips, by the feature that keeps a program outside the calculus
(the first of a fixed order that it uses):

| Count | Skip |
| ---: | --- |
| 5233 | does not lower (the checker rejects it before typing) |
| 99 | tags and `match` |
| 43 | an inferred type the corpus cannot write |
| 41 | `print` or `trap` |
| 23 | the checker rejects a method used as a plain function or the reverse (`MethodFlag`) |
| 18 | a foreign host call |
| 7 | arithmetic on non-primitive operands |
| 4 | a numeral of 2^30 or more |
| 2 | a rest pattern with no fields |
| 12 | none of the above, among them the real cycles (a group member reading a value that calls the group), which the checker rejects |

`MethodsAndDotCalls`, `SharedReceiver` and `ResourceLimit` are no longer skips
and `RecursiveType` is a compared class, not a skip.

**Known incompleteness.** Every item is on the sound side: W or the calculus is
more restrictive than the checker, never less, and the differential test counts
the programs and records no mismatch.

- **11 recursive programs W refuses (#606).** Each is sound but incomplete:
  the checker accepts, W refuses, and there is no mismatch. The refusals were
  measured again by logging each `None` in the extracted algorithm, and by
  prototyping the fix the first measurement suggested (in the extracted OCaml,
  not committed). Corpus lines below are the current `core_corpus` numbering.
  - **Row variable occurs, 3 (lines 7, 18, 291).** `occR`: a row variable meets
    a row that contains it, as in `{l1: M, ...} ~ {l0 | r}` where `M` mentions
    `r`. A prototype `unify_kr` case solves it: split the row at the one field
    whose type mentions `r`, put a fresh variable `x` there, solve `r := row[x]`
    with `x := knot x (T[r := row[x]])`, and `unroll_eq` 1 holds between the two
    sides. It does not make any of the three compared: the substitution leaves
    `s T1` and `s T2` one unrolling apart below a record field whose row has a
    variable tail, and `unify_co` fails in `coerce_dec`, which has only head
    coercions. A record with an open tail cannot be eta-expanded, since the
    coercion would have to rebuild labels it cannot name.
  - **Tail occurs, 3 (lines 254, 299, 300).** `rewrite_row` refuses because the
    tail variable is in the other row. Trying the other row first (same rule,
    arguments swapped) reaches the row-variable case above and the same
    `coerce_dec` refusal (line 300), or refuses again (254, 299).
  - **Deep coercion, 3 (lines 288, 292, 301).** `unify_k` succeeds and
    `coerce_dec` refuses, for example `{...ball, size: 10}.moved()`.
  - **Line 312, `step(ball).x`.** Not a `bind_k` fault and not a corpus fault.
    `bind_k` refuses a type with a free index (the one logged refusal) when
    `unify_k` compares two mu bodies, which is only the first attempt: the
    fallback unrolls and meets the same pair (the field's mu against the
    record-level mu of `ball`) again, until the fuel (100000 calls) runs out.
    The two types are one regular tree written with the knot in two places, and
    no `unroll_eq` with a finite budget relates them (there is no mu/mu
    congruence rule), so the algorithm would need an assumed-pairs set and a
    spec stronger than `unroll_eq`.
  - **Line 315, `h = program(r) do ... (r.g)({stop: true, g: h}) ...`.**
    `unify_t` fails on the member's type against its slot variable (the slot
    occurs in the member's type); the slot would be bound to a knot, and the
    member would then need a `fold` around its whole lambda, which `T_Letrec`
    does not allow (`fn_group`).
  Three things would be needed to compare these: a coercion below a record with
  an open row (or a way to place the knot so that no coercion is needed, over the
  record type that carries the row variable), a coinductive type equality
  (assumed pairs) in `unify_k`, and a `T_Letrec` that admits a `fold` of a
  lambda. Each changes the calculus or its spec; none is a local proof.
- **`lacks` on a row variable (#564), closed in phase 7 stage 7.3b.** The calculus
  derives a spread whose base ends in a row variable the checker knows lacks the
  label (`{x, ...rest} = p` then `{...rest, x: 2}`, by `T_SpreadL`), and algorithm
  W now carries the lacks facts (see "Algorithm W carries the kinds"), so the 222
  programs the corpus reader used to skip under `LacksOnTail` are compared.
- **No non-derivation of `{...lit, x: 1}.a()`.** The checker and W both reject a
  method literal spread and then called, but the calculus has no theorem that no
  derivation exists: it needs an inversion lemma for `unroll_eq`.
- **Recursive groups split by a value binding (#628).** The checker infers and
  generalizes a whole recursive group before it types a value binding that sits
  between its members, which is the hoisted `letrec` the reader writes, so the
  65 programs that used to be skipped (`SplitGroup`) are compared.

## Loops and foreign calls (decided)

**Loops need no calculus extension** (phase 6a of #435, a check and not a build). `lower.rs` desugars `repeat`, `for ... from
... to` and `for ... in` to a local function that runs the body and calls itself
(`go = program(i) do if i < stop then _ = B  go(i + 1) else () done done`, then
`go(start)`), as ADR 0013 says: the loop is tail self-recursion, with no loop
node. The proofs read lowered HIR, so a counted loop is `let`, `program`, a
recursive call, `if`, `+` and a comparison: phase 1 and phase 2 already type and
run it, and `progress`, `preservation` and `soundness` cover it. A `for ... in`
loop walks a list with the list tags and `match`, so it is in-fragment once
phase 3's list sugar is. The differential reader reads every loop (a program is
no longer counted under "a loop"; the entry is gone from the skip list). What a loop does need is
elaboration agreement, which the differential test already checks, since the
Rust lowering and the proofs both read the desugared form.

**A `foreign` call is an opaque typed constant.** The checker gives a `foreign
"module" "name" (params) -> ret` binding the fixed monomorphic scheme
`(params) -> ret` over the boundary types `Number` (a `Float`), `Int`, `Bool`,
`Unit` and `String`. The calculus models it as a name in the typing context at
that arrow type, with no body and no free variables, and a call steps to any
value of the return type or traps, as the host may do either. That is the same
device as the opaque `Float` operations (a relation, so no axiom): `progress`
and `preservation` hold for whatever the host returns, which is the claim the
embedding needs, and `goat_ln.ott` needs a context entry and one step rule, not a
new type or term. What the proofs do not say is what a host function computes.
This waits behind phase 1 (the boundary types) and is cheap; it is listed as
phase 6b of #435.

## Row kinds: lacks and sorts on row variables (stage 7.2, #564)

A row variable has a **kind**, as a type variable has a sort: `RK s ls`, where
`s` is a sort (what the fields of a record it tails must satisfy) and `ls` is
the set of labels it lacks. The kinding environment is a record
`DEnv {dsort; drk}`, coerced to `dsort` so `D a` still reads a sort, and
`drk D r` is the kind of `r`. `k_Any` and `rk_any` (no label lacked) are the
defaults outside a finite support (`supp_ok` says both).

- **Sorts on a row tail.** `rsat D k (row_Var r)` holds when `r`'s sort in `D` is
  at or above `k`, so a record with an open row satisfies `Eq` or `Numeric` when
  its fields do and its tail has the sort. This makes the open-row comparison
  derivable (`GoatRowKinds.v`). A `Maybe` entry `l ^ P : T ; R` satisfies a sort
  when `R` does and either `P` is `Bool` (the field is absent, whatever its type)
  or `T` does, which is what the checker does, so `sat` cannot tell `teq` types
  apart (`GoatSatTeq.v`, `sat_teq`) and a substitution that sends `P` to `Bool`
  cannot break it. `sat_b` decides the same clause (`is_abs P || sat_b D k T`).
- **Lacks.** `rlacksD D l R` is `rlacks` with a variable tail read from `drk D`;
  `T_SpreadL` gives `{...e1, l: e2} : {l : T ; R}` from `e1 : {R}` and
  `rlacksD D l R`. `req_abs` is unchanged: it keeps the syntactic `rlacks`. For a
  value the row has no variable (`req` preserves the tail, `req_rtail`), so
  `rlacksD` is `rlacks` and `spread_step_typing_L` turns the derivation into a
  `T_Spread` one with `req_abs`; preservation reuses `spread_step_typing`.
- **Substitution.** A row substitution respects the kinds when `rkres D D' sr`:
  `sr r` satisfies `r`'s sort in `D'` and lacks every label `r` lacks
  (`rkok`). `sat_ap`, `bin_sig_ap`, `rlacksD_ap` and `casch_inst` take it beside
  `kres`.
- **Schemes and `let`.** `Sch` records `s_rk`, the kind of each quantified row
  variable, and `gen G T k rk` takes it. `T_Let` and `T_Letrec` type the bound
  term under `extr (ext D V k) Vr rk`, `D` extended on the generalized rows `Vr`
  by `rk`, and `inst` demands `rkok D (s_rk s r) (sr r)` of each quantified row
  variable's image. The shortcut "generalized rows carry no lacks" breaks
  preservation: term substitution removes a binder from the context, which makes
  a row variable generalizable that was free before, and the `let` body's
  derivation then needs a lacks premise the original lacked. So `rk` rides
  wherever `k` does: `casch` (through the row renaming `gr`), `sch_more_gen`
  (`rkup` beside `kup`), `typing_denv_agree` (a row variable the context does not
  mention goes to the empty row, which lacks everything), `typing_inst_gen`,
  `tsubst_gen_core`, and `sch_equiv`.
- **Algorithm W carries the kinds (stage 7.3b).** `DOk D n` says `D` has the
  default sort and the default row kind beyond the first `n` even atoms, and
  `KR D D' s` says `s` respects the sorts and the row kinds (`kres` and `rkres`);
  `Good` carries one for the substitution and one for the refinement of the
  environment, and `KR_comp` composes them (`rkok_ap` is its row half). A row
  variable gets a kind in three places. `bind_row` binds a row variable to a row:
  the variable at the row's tail is renamed to a fresh one whose kind is the
  join of both (`rk_join`: the finer sort, the union of the lacks; a lacks set is
  a function, so the two kinds cannot be compared and the renaming is always
  made), the sort reaches the type variables of the fields (`push_sort`), and the
  row must satisfy the sort and avoid the labels the variable lacks (`lacks_ok`,
  `rlacksD_spine`). A type variable of sort `Eq` or `Numeric` that binds to a
  record pushes its sort onto the row variables in it too (`push_sort_r`: each
  coarser row variable is renamed to a fresh one of that sort that lacks the same
  labels), so `program(a, b) do (if a == b then 1 else 2 done) + a.x done` types
  at an `Eq` row tail; the fuzz target's `GAPS` row for it is gone. `rewrite_row` fails on a row variable that lacks the label
  and gives the fresh tail of `l ^ p : a ; r'` the kind it replaces. `restrict`
  gives its tail the removed label. `gen_ren` records the kind of each
  quantified row variable (`gen_rk`) and `inst_den` gives each fresh one that kind
  back; `T_Let` and `T_Letrec` type the bound term in `Dsc D sc`, `D` extended by
  the scheme's sorts and kinds, which `KR_Dsc_lift` carries across a step.
  A spread tries `T_SpreadL` first: it unifies the base with a fresh row
  variable and, when the result lacks the label, types the spread at
  `{l : T | R}`; otherwise (and when the unifier fails) it falls back to the
  presence-variable `T_Spread` (`spread_present`), so a base that has the field,
  or whose row may gain it, types as before. The extracted algorithm is
  differentially tested on the 222 programs the corpus reader used to skip.
- **Statement B.** The row environment is read by `sat` only at a `row_Var`, so
  it extends to recursive types (a `mu` body's row tails are read the same way,
  `sat_open_mut` is unchanged) and to methods (`T_Obj` is typed against the same
  environment) without another change to the environment; the algorithm side
  (a unifier that updates `drk` and a completeness proof against it) is stage 7.3.

## Generic operators: sorted type variables (design Q)

The typing judgment carries a kinding environment `D` (`typing D G e T`): a
total map from type variables to a **sort** (`k_Any`, `k_Numeric`,
`k_Literal`), `k_Any` outside a finite support. A type satisfies a sort
(`sat D k T`) when it is `Int` or `Float`, or a variable whose sort in `D` is at
or above `k`. A scheme records the sort of each quantified variable
(`Sch tq rq body sk`), so `gen G T k` quantifies the free variables of `T` not in
`G` at the sorts `k`. `T_Let` and `T_Letrec` type the bound term under
`ext D V k`, `D` extended on the generalized set `V` by `k`, which is why the
sort of a variable lives in the environment and a type variable stays a plain
`typ_Var a`. A numeral has any `k_Literal` type, `float(e)` takes any
`k_Literal` operand, and `+ - *` take two operands of one `k_Numeric` type. A
substitution respects the sorts when `kres D D' st`: each `a` goes to a type
that satisfies `D a` in `D'`.

The substitution lemma needs three things the plain calculus did not.
`sch_subst` and `ctx_subst` quantify over all pairs of environments the
substitution respects, so renaming the generalized variables moves the
environment by the renaming (`dperm`). The target and source environments are
`k_Any` outside a finite set (`supp_ok`), so a fresh name a `let` is renamed
onto is `k_Any` and carries any sort. And a derivation moves between two
environments that agree on the free variables of its context and type
(`typing_denv_agree`), sending the variables it uses internally to `Int`, which
satisfies every sort; term substitution under a `let` needs exactly that, because
the bound term is typed in an extended environment. `sch_more_gen` (for
`typing_ftv_mono`) is indexed by the environment for the same reason.

The program judgment is `typing d_any nil e T` with `d_any` the all-`k_Any`
environment. Defaulting (ADR 0017: a `Literal` variable left unconstrained is
`Int`; `Numeric` has none) is therefore a choice among derivations, not a rule:
in `d_any` a closed derivation instantiates each generalized `Literal` variable
at `Int` or `Float`, and `numeral_binding_is_generic` in `GoatPhase1.v` shows
both choices.

A `let` may keep some variables of its binding monomorphic: `T_Let` takes a
type `Tm` and generalizes over the context extended with a binding of `Tm`
(`pin_ctx`), so the variables of `Tm` stay free. The rule's `lit_pinned`
premise says that, unless the bound term is a function or a bare numeral
(`let_open`), no variable it quantifies has the sort `Literal` in `k`: a numeral
inside a record stays one type across the body's uses, as in the checker
(`r = {a: 1}` is one record, not a fresh one per use). The algorithm pins
exactly the `Literal` variables of such a value (`let_pin` in `GoatInfer.v`).
A derivation that re-pins after the context shrinks (substituting for a
variable, `typing_ftv_mono`) picks a new `Tm` that stands for the old context's
variables (`repin`). A recursive group as a `let`'s bound term is not `let_open`:
it unrolls to a record, which pins. `shared_numeral_not_int` (`GoatPhase1.v`)
is the non-derivation: `r = {a: 1}  {y: r.a, x: r.a + 1.5}.y` has no derivation
at `Int`. ADR 0038 records the choice.

## Algorithm W with sorted variables

`GoatInfer.v` threads a kinding environment `D` through the algorithm
(`infer f D G e n` returns `(s, D', T, n')`), so a type variable has the sort
`D` gives it. `D` is `Any` on every even atom from the supply number `n` on
(`DOk`, `GoatInferSort.v`), and only a fresh variable gets a sort, by `upd`.

- **Unification** (`unify_t f D T1 T2 n`, and `unify_r`, `unify_k`, `unify_kr`,
  `unify_co`) returns `(s, D', n')`. A variable meets a non-variable type only if
  the type satisfies the variable's sort (`sat_b`: an `Int` or `Float` satisfies
  every sort, any other type only `Any`); two variables bind the coarser to the
  finer (`finer_b`), so the survivor keeps its sort. Before the check the sort is
  pushed onto the type (`push_sort`, `bind_prop`): each variable inside the type
  that is coarser than the sort is renamed to a fresh variable of that sort, one
  fresh atom at a time, and `D'` is `D` updated (`upd`) on those atoms. Each
  renaming is a `Good` step (`Good_rename`: the new atom is `Any` in `D` by `DOk`,
  and its sort is finer than the renamed variable's), so `push_sort_good` follows
  by induction on the variable list and the unifier's statement is `GoodU D n s D'
  n'`: the supply grows, and from a well-kept `D` the step is `Good` (the
  implication keeps `teq_dec`, which runs the unifier at supply 0, free of
  `DOk`). A substitution that respects the sorts is `kres D D' (sT s)`.
- **A numeral** is a fresh `Literal` variable, **`float(e)`** unifies its operand
  with a fresh `Numeric` variable, and **`+ - *`** unify both operands with one
  fresh `Numeric` variable, the type of the result. So `1 + 1.5` infers `Float`
  and `program(x) do x * 2 done` infers `a -> a` with `a` `Literal`.
- **`generalize`** (`gen_ren D`) records the sort `D` gives each variable it
  quantifies, on the renamed variable (`gen_sk`), and **`instantiate`** gives each
  fresh variable its scheme's sort (`inst_den`).
- **`infer_closed_env`** returns the type and the kinding environment, so the
  sorts of the variables the type leaves free. `infer_closed_sound` says the
  program has that type in that environment: `typing D nil e T`. A closed program
  is typed in `d_any`, where each such variable stands for any type of its
  sort, so the defaulting of ADR 0017 (a `Literal` variable left free is `Int`) is
  the choice of that instance; the algorithm makes no choice and the theorem
  covers every one. A comparison needs no choice either: it unifies its
  operands at an `Eq` variable.

The soundness proof (`GoatInferSound.v`) carries one invariant per step, `Good D
n s D' n'`: `D` is `Any` beyond `n`, `s` is a substitution of the algorithm, the
supply only grows, `D'` refines `D`, and `s` respects the sorts. A derivation
moves forward through a step by the substitution lemma (`typing_ap`), which
already quantified over the environments a substitution respects. At a `let`
the bound term is typed in `ext D V k`, the environment extended with the sorts
the scheme records on the renamed variables (`typing_gen_ren`,
`kres_ext_lift`).

Record arithmetic (ADR 0012, `GoatRecArith.v`): a closed record whose fields are
all `Numeric` is `Numeric` (`sat`, `rsat`), so `+ - * // %` take two records of
one such type, and `/` takes two records of `Float`s (`sig_quot_rec`). Two
records step by `st_binrec`: `rec_zip` pairs each field of the first with the
first field of the second under its label, in the first's order, and the result
is a record of operator applications, which the field rules then evaluate; a
trap in one field is the record's trap. The two operands may list their fields
in different orders. A record is never `Literal`, so `float(e)` takes a
`Literal` operand (`T_ToFloat`), not a `Numeric` one: `float` of a record has
no step. The algorithm binds a `Numeric` variable to a record whose fields all
satisfy `Numeric` (`sat_b`); it does not push the sort onto a variable inside
the record, as the checker does, because a substitution keeps the kinding
environment, so a record that holds a variable of no sort is rejected where the
checker accepts it. It does not infer `/` on records.

Metalib's atoms are opaque to computation, so the Coq examples that run the
algorithm on a numeral (a fresh variable) do not reduce; the differential test
runs the extracted algorithm on them instead.

## Records and projection in the Ott source

`goat_ln.ott` adds the record literal `{ fs }` and projection `e.l` to the term
grammar. The field sequence `fs` is a **mutually-recursive cons-list** baked
into the same inductive block as `exp` (`fs_nil`, `l : e ; fs`), *not* a Coq
`list (label * exp)`. This is deliberate: given a `list`-valued subterm, Ott
0.34 aborts its locally-nameless `lc`/`fv`/`subst` code generation (it prints
`only native lists supported`, then fails with `Not_found`). The mutual
cons-list is the same finite ordered field sequence and lets Ott emit the full
`open`/`subst`/`fv`/`lc` companions (`open_fields_wrt_exp`, `fv_fields`, …) that
the metatheory needs. Type and row variables remain a free-variable set
(`nat`), not binders, exactly as B2 chose.

## Build

Needs an opam switch with Rocq 9.1.1 (the opam `coq.9.1.1` package), Ott 0.34,
and metalib (not on opam — pinned from `github.com/plclub/metalib` at
`144ddcd0fff6717229140314cf559d85fad6eae0`). Rocq 9.2 and 9.3 fail to build
metalib. With those on `PATH` (or under `opam exec --switch=rocq-9 --`):

```
make        # regenerate Goat_ott.v from goat_ln.ott, then compile under Rocq
make ci     # check the committed Goat_ott.v matches the source, then compile
```

metalib installs onto Rocq's `user-contrib` path, so no extra `-R` is needed for
it; `_CoqProject` maps this directory to the logical name `Goat`.

## Why two Ott files

`goat.ott` is the readable typeset spec and must stay in lockstep with
`docs/semantics.md`. The Coq generation needs two things that spec does not
carry, which `goat.ott` itself flags as "realized in B2, not here":

1. The term-variable metavar must be marked `repr-locally-nameless` for
   metalib/LNgen.
2. The n-ary multi-binder needs a concrete encoding.

Putting those in a separate `goat_ln.ott` keeps the typeset spec clean and lets
the mechanization make its encoding choice explicitly.

## The n-ary binder: internal currying to a single-binder lambda

`docs/semantics.md` §10 names two encodings for `program(x1,...,xk)`: (a)
internal currying to a single-binder lambda, or (b) a telescope /
simultaneous-substitution encoding. **B2 chooses (a).**

Why: metalib/LNgen's locally-nameless machinery — `open`/`close`/`subst`/`fv`
and the cofinite `lc` predicate, plus the full suite of lemmas LNgen emits — is
built for **single** binders. A single-binder core is the one encoding where all
of it, and the large locally-nameless PL-metatheory corpus ADR 0008 wants to
crib from, applies unchanged. In `goat_ln.ott` `program` binds one parameter,
application is unary, and the arrow `(T1) -> T2` is unary; Ott generates exactly
the standard `open_exp_wrt_exp` / `subst_exp` / `fv_exp` / `lc_exp` from it.

The cost, as §10 says, is a surface/core gap. goat's surface function is
genuinely k-ary: `program(x1,...,xk)`, `e(e1,...,ek)`, `(T1,...,Tk) -> T`, and
the sharp-edge examples depend on that arity. The curried core is the k-fold
iteration of the unary core, reconnected to the surface by uncurry/arity lemmas.
B2 does not need that bridge (its lemmas are stated on the core); B3 carries it.

Type and row variables are **not** binders (ADR 0008): a free-variable set with
named substitution. In this B2 core they are `nat`; refining them to metalib
`atom` with atom-set free-variable functions is a B3 step. Neither lemma below
depends on that choice.

## Generated, committed

`Goat_ott.v` is generated but **committed**, so the development builds without
Ott present and so diffs are reviewable. The generation command lives in the
`Makefile`; `make ci` (and the CI job) regenerate into a scratch file and
`diff` against the committed copy, failing on drift. CI pins `ott.0.34` so the
diff is byte-reproducible.

LNgen — which would *emit* the infrastructure lemmas rather than our proving
them — is a Haskell tool not packaged on opam, so it is not in the pipeline.
The one infrastructure lemma below is therefore hand-proved; wiring LNgen in (it
needs a Haskell toolchain in CI) is a later step.

## What is proved (B3, issue #71)

**Status:** Progress, Preservation and Soundness are all proved, assumption-free.
The two canonical Hindley–Milner lemmas — general weakening (L4,
`typing_weaken`) and type/row substitution (L5, `typing_tsubst_fix`) — that the
term-substitution lemmas L6a/L6b rest on are now **closed** (#151), so the whole
development is unconditional.

The soundness statements of `docs/semantics.md` §7 are mechanized here. By
`Print Assumptions`, **`progress`**, **`preservation`** and **`soundness`** are
all *closed under the global context*: no axioms, no admits.

Fully closed, no admits:

- The row theory (`GoatRows.v`): L1, L2 (incl. arrow/record inversion up to
  `≅`), L2′, L3. The §3 characterization is proved in the **soundness
  direction** — `req` respects the tail-and-per-label-list reading — which is
  exactly L2′ and is what the record cases of canonical forms, L3, and
  `ST-ProjRec` need. The *completeness* direction (the characterization implies
  `req`, the swap-congruence obligation ADR 0008 names as the schedule risk) is
  **not** needed for progress/preservation and is not proved.
- Locally-nameless infrastructure (`open`/`subst` commutation, `subst_intro`),
  `typing_regular`, canonical forms (L7), the T-Conv-aware typing inversions,
  **Progress**, all **Preservation** congruence cases, and `ST-ProjRec`.
- **Term substitution** (`GoatSound.v`): `typing_subst` (L6a, monomorphic, for
  `ST-Beta`) and `typing_subst_poly` (L6b, polymorphic, for `ST-LetV`), both
  instances of one lemma `typing_subst_gen_mut`, by mutual induction on the typing
  derivation, prefix-generalized over the context so the induction goes under
  binders. Their `let` cases need no new theory: dropping a binding from the
  context only makes `gen` more general with no new free variables
  (`gen_more_gen`), the good direction for `typing_ftv_mono`. Also
  `typing_inst_gen` (every instance of a generalization is derivable).

- **The two canonical HM lemmas** (`GoatSound.v`), on which the term-substitution
  lemmas (hence Preservation's `ST-Beta`/`ST-LetV` and Soundness) rest:
  - `typing_weaken` (L4): inserting a middle block of bindings preserves typing;
  - `typing_tsubst_fix` (L5): substituting the type/row variables *not* free in
    the context preserves typing (in the all-`k_Any` environment, where
    algorithm W works).

  Both follow from one general lemma, `typing_tsubst_gen_mut`: a type/row
  substitution applied to a derivation, with the context substituted
  capture-avoidingly (the `ctx_subst` relation, which also allows **extra**
  target bindings, so the identity substitution gives weakening). Every case is
  structural except `T-Let`, whose hard point is that generalization does not
  commute with a *capturing* substitution. The fix (approach (a) of the #151
  analysis) is a derivation-level freshness step carried out in the proof, not in
  the typing rule: at each `T-Let` the let-generalized variables are renamed to
  atoms fresh for the substitution and the target context (`mk_rename`), so the
  capture-avoiding substituted scheme (`casch`, `GoatHM`) both preserves the
  instance set (`casch_inst`) and equals `gen` of the substituted body over the
  target context (`casch_gen_sch_equiv`, `GoatSound`). The typing rules are
  untouched, so the set of accepted programs is unchanged.

`make ci` runs a frozen-admit guard (`make check-admits`) with
`EXPECTED_ADMITS = 0`: it fails if any `Admitted.` reappears in `proofs/*.v`.

## Rank-2 inference is not part of the language

An earlier pass added a rank-2 typing rule (`T_AppPoly`) and `GoatRank2.v`. Both
are deleted: goat has no type-annotation syntax and ADR 0027 declines
annotation-free rank-2 inference, so the sharp-edge programs `both` and `use2` stay
untypeable, which `docs/semantics.md` section 8 states as the language's limit.

### Infrastructure (`GoatProofs.v`)

- `teq_refl` / `req_refl`: reflexivity of `≅`, derived by mutual induction (the
  relation states symmetry, transitivity, and label swap but no reflexivity).
- `subst_exp_fresh_eq`: `y ∉ fv_exp e → subst_exp u y e = e`, over the
  generated `subst_exp`/`fv_exp` (now mutual with the `fields` spine).

## The parser claim (ADR 0030)

`peg_deterministic` (T2): a token stream has at most one parse. `parse_denotes_lc`
(T1): every parse of the top rule `goat` whose tree is in the core fragment is
either a tree lowering reports (`Reject`: a record whose spread is not first, or
that has a second) or denotes a term that is both `lc` (the local closure the
soundness proof uses) and the generated `lc_exp`. `parse_denotes_accepted` is the
second half on its own, for a tree `Accepted` (no `Reject` shape in it).

Boundary:

- **Spread and rest patterns.** `{...(p), x: v, y: w}` denotes
  `spread(spread(p, x, v), y, w)` (`spread_nest`: a multi-field spread is the nest
  of single ones, the first field innermost). `{x, y, ...r} = v body` denotes
  `let s = v in let x = s.x in let y = s.y in let r = restrict(restrict(s, x), y) in body`
  (`unpack`: a rest pattern with k labels is k restricts), where `s` is a
  variable the program does not use, as lowering's fresh symbol is. Complete trees
  keep a spread first in its record and at most one (lowering reports the rest),
  a destructure needs its body, and a function parameter is a name (a record
  pattern there, and every list pattern, stay outside the fragment). T1 covers
  all of it. T3 covers the spread: the printer writes `{...(base), lab: v}` with
  the base always parenthesised, so a name there cannot read as the rest binding
  of a record pattern. A bare `restrict` has no text of its own (a rest pattern
  also binds the labels it removes), so `scoped` still excludes `e_restrict`;
  `core_roundtrip.rs` checks the lowering of a rest pattern directly instead.
  Label numbering for a destructure follows text order (pattern names first);
  nothing in T3 depends on it, because the printer never writes one.
- **Operator runs, `and`/`or`/`not`, negation (stage 3).** A statement is a flat
  run of operands and operators. `Den_run` reads the tree into items (a value, a
  prefix `not`, an infix operator) and `Den_math` says the expression is
  `resolve` of those items (`GoatPrec.v`), the stack fold of `lower_expr_chain`.
  `resolve_one`, `resolve_left`, `resolve_right`, `resolve_not_loose` and
  `resolve_not_tight` state the readings the checker expects: equal levels fold
  to the left, a tighter operator on the right nests, and `not` takes the operand
  after it and takes a following operator inside only when that operator binds
  tighter than `not` (`not a == b` is `not (a == b)`). `and`, `or` and `not` are
  derived forms, so `goat_ln.ott` and `Goat_ott.v` do not change; their typing
  (`infer_logic`: Bool operands, Bool result) is the typing of the `if`. The
  evidence that lowering agrees is the differential reader, which now reads
  `And`, `Or` and `Not` as that `if` (the 21 programs it used to skip as
  connectives are compared, with 0 mismatches). `-x` is `0 - x` (`D_neg_chain`)
  and a bare `-3` is the literal (`D_neg_int`); a negated Float literal keeps
  `e_dec`'s opaque value, so its sign is not modelled (`D_neg_dec`).
  `Complete` no longer limits a run to one operator. `precedence.rs` checks the
  Coq `prec` against lowering and checks the lowering of negation. T1 covers all
  of it. T3 needs nothing new: no term of the calculus has a connective or a
  negation to print, and the printer parenthesises every nested operation, so it
  never writes a run.
- **Tags, `match`, lists (stage 4).** `tag` declarations are read first, as a
  function of the program's leading `tag_decl` nodes, into a table
  (`decl_entries`: tag name to the group's slot codes and the tag's position;
  `Number` is code 2, `Int` 1, `Bool` 3, `Unit` 4, `String` 5, the group's own
  name 0, the `j`-th `_` code 6 + `j`). The prelude's declarations are the
  parameter `ptbl` of `Den_goat`, ahead of the program's, as lowering looks
  tags up (the first entry for a name wins). A name that is in the table is a
  tag, not a variable (`D_name` needs it absent): `Circle(2)` denotes
  `con w tg {0: 2}` (`DC_tag_call`; the payload is always the record of the
  tag's slots, labelled by position, as GoatPhase3.v builds it) and a bare tag
  `con w tg ()` (`DC_tag`). An arm `Tag(a, b) then body` denotes the arm
  `let a = p.0 in let b = p.1 in body` over one payload variable `p` that the
  program does not use (`DArm`, `slot_lets`), the arms in source order and the
  `else` as the default, with the group taken from the first arm
  (`D_match_tags`). A `match` whose arms are scalar literals is lowering's chain
  `if v == 0 then a else if v == 1 then b else c`, the scrutinee used directly
  when it is a variable and bound once to a fresh one otherwise
  (`D_match_lit_var`, `D_match_lit_let`, `lit_chain`). A list literal `[a, b]` is
  `Link(a, Link(b, Empty))` through the table's `Link` and `Empty`
  (`D_list`, `list_of`). `Complete` keeps a declaration's payload types to names
  the table can encode, a `match` to arms of one kind (tag or literal) with an
  `else` after literals, and `Known` (hypothesis of T1, `goat_known`) says each
  arm's tag and the list tags are in the table. T1 covers all of it. What stays
  outside the fragment: list patterns (in a `match`, a destructure or a
  parameter, which lowering compiles to a decision tree of `Empty` and `Link`
  matches), payload types other than a name or `_` (`[Int]`, `{x: Int}`,
  function types), an `else` with no arm, a literal `match` on `true` and `false`
  that leaves out the `else`, and a binder named like a tag (Den reads the tag).
  Arity, exhaustiveness, a tag outside every group and arms from two groups are
  the checker's errors; `Den` denotes them (the group of the first arm) and T1
  says only that the term is locally closed. T3 is stated at the empty tag table:
  the printer writes no tag, so a program that builds or matches one has no
  printed form yet (`print_parse_roundtrip` is unchanged but for `Den_goat var_of
  [] t e`); T3 through tags is the part of this stage that remains.
- **Loops (stage 5).** `repeat n times do B done`, `for i from a to b do B done`
  and `for x in xs do B done` denote the term lowering builds (`lower.rs`,
  `lower_loop`), over names no source name can spell. A counted loop is
  `let start = a in let stop = b in (letrec go = program(i) do if i < stop then
  (let _ = B in go(i + 1)) else () done in go(start))`: `<` and start 0 for
  `repeat`, `<=` for `for` (both ends included), the counter `i` the loop's own
  name for `for` and a hidden one for `repeat`, the body `()` when absent. The
  group is the one-member `letrec` of a block's function binding (`group_fields`,
  `bind_group`), so the recursive call is a projection from the group
  (`counted`, `D_repeat`, `D_count`). `for x in xs` is the `letrec go =
  program(r) do match r do Empty then () Link(x, rest) then (let _ = B in
  go(rest)) done done in go(xs)`: the arms are `Empty` then `Link`, and the
  `Link` arm reads the payload's slots as an ordinary tag arm does (`link_arm`,
  `each_term`, `D_each`); the group is the one `Empty` and `Link` resolve to
  (`Known` asks both tags to be in one group, as the prelude's are). The fresh
  names (`go`, the two bounds, the parameter, the payload and the rest) are
  pairwise distinct and apart from the free variables of the bounds, the list
  and the body and from the item or counter (`apart`, as the dot call's receiver
  is apart from its arguments); `exists_apart` makes totality produce them. The
  words `from`, `to` and `in` are `word_tok`: the name token the lexer writes or
  the keyword token of that spelling, which the generated grammar also accepts.
  The body's value goes to a binding nothing mentions, written `e_let B call`
  with no name to close. The loop rules and the four keyword rules are Core in
  `rule_map.rs`. The evidence that `Den` is what lowering builds is
  `checker/tests/loop_shape.rs`, which lowers each form and compares the HIR to
  these shapes, and the differential reader, which writes the HIR loop as a
  `letrec` term (the same term, in locally nameless form) and compares its
  type with the algorithm's. T1 covers all three. T3 is unchanged: the printer
  writes the desugared form, so a loop never comes back from it.
- **Dot calls and `::`.** `r.f(a)` denotes `(r.f)(r, a)` when `r` is a name or a
  path of field accesses (`is_path`: the receiver is repeated, `DP_dot_path`), and
  `let s = r in (s.f)(s, a)` for any other receiver (`DP_dot_bind`), where `s` is
  a variable no argument uses, as lowering's fresh `@receiver` symbol is. `r::f(a)`
  is `(r.f)(a)` (`DP_take`, `DP_call`). A call straight after an access is always
  a dot call, on any receiver and in an expression with an operator. T1 covers all
  of it (`posts_den`). T3 needs nothing new: the printer parenthesises a
  projection callee, so it never writes a dot call, and a printed chain parses
  through the ordinary call rule. `core_roundtrip.rs` checks the lowering of a
  path receiver, a computed receiver and a take directly, and its generator
  writes `p.l(a)` for path receivers in the dot style.
- **Core fragment only.** The rules of `grammar/goat.peg` that `goat_ln.ott` has
  a production for (`core_rule` in `GoatShape.v`, checked against
  `parser/tests/rule_map.rs` by a Rust test), minus the shapes ADR 0030 excludes
  (`Complete` in `GoatShape.v`), which is now only what no `Den` rule reads yet:
  a record pattern or any list pattern as a parameter, a payload type with no
  slot code, and a `match` whose arms mix kinds or are literals with no `else`.
  Shapes lowering reports are `Reject`.
- **The block (phase 8 stage 6).** `Den_blk ctx fin cs xs gs b` reads a block
  from its start: `ctx` holds the value bindings and late functions so far, `fin`
  is what the block is if it ends here, `xs` and `gs` are the functions hoisted
  into the block's group, and `b` is the rest. `a; b` is `let _ = a in b`
  (`DK_seq`, with no name to close in locally nameless form) and a stray `;` is
  skipped (`DK_skip`), as in lowering. A block that ends in a binding is the
  value of its last binding (`fin` is that name, `DK_value`): the checker gives a
  program `x = 1` the type of `x`, which the differential test showed; a block
  that ends in `a;` is the unit value, and so is an empty program or body
  (`DBo_none`). A function binding joins the hoisted group when none of its free
  variables is a name in `ctx` (`mentions_any`, computed over the denoted term;
  `DK_hoist`), and otherwise stays where it is written, as a plain `let`, or as a
  group of one when it names itself (`fn_place`, `DK_late`). A binding that is an
  operand reads the same way (`D_local_fn`). `program()` takes one hidden
  parameter pinned to the unit value (`unit_arg`: the parameter is compared with
  the unit value, so its type is `Unit -> t`, which is what the checker's function
  of no parameters has), and `f()` applies `f` to the unit value; `Tag()` is `Tag`.
  Mutually recursive functions that both use a value are each placed alone, so a
  call from one to the other is a free name: a gap in what `Den` says, not in
  `lc`. `block_shape.rs` pins the HIR lowering gives each form.
- **The lexer is trusted.** The input is a list of tokens; nothing is said about
  how characters become tokens. A text terminal matches a punctuation or keyword
  token by its spelling, and a name token by its spelling when the word is
  `contextual` (`from`, `to`, `in`, `foreign`; names elsewhere), so a rule can
  spell them out. No core rule does; `gen` has `G_word` for the match, and the
  printer proof shows a printed name is never `foreign`.
- **Recovery annotations are not in the generated grammar.** They change nothing
  about valid input.
- **Not verified:** the Rust interpreter `parser/src/interp.rs`, the lowering
  `checker/src/lower.rs`, and every rule outside the fragment. Connecting them to
  these theorems stays a testing argument (`rule_map.rs`,
  `checker/tests/core_roundtrip.rs`).

Side conditions. Duplicate record labels and repeated parameters are lowering
errors that `goat_ln.ott` allows (ADR 0030). `goat_ln.ott` is unchanged; they are
conditions on the term, to be hypotheses of the round-trip theorem T3 where they
matter. T1 does not need them: `close_exp` yields a locally closed term whatever
names repeat, so T1 is stated without them rather than with unused hypotheses.
Recursive function bindings and a block's function group are no longer a
disagreement: `DK_hoist` is that reading.

`print_parse_roundtrip` (T3): for a closed core term `e` (`scoped 0 e`) whose
labels are numbered by first occurrence in the printed text (`Interned e`), and
a `var_of` that gives the printer's binder names `v0`, `v1`, ... distinct atoms
(`names_distinct`), the PEG relation parses `print e` to a tree `t` and
`Den_goat var_of t e` holds, so `t` denotes exactly `e`.

- **Printer.** The curried style of the Rust printer. A call's callee and a
  projection's base are parenthesised when they are a binding, a number or a
  `Float`; a binding's value is parenthesised when it is a binding or a function
  (a bare function would be a group member). A conditional whose else is the
  unit value is printed without an `else`. The grouped style is not mirrored.
- **Side conditions.** Duplicate labels or repeated parameters are not
  hypotheses of T3. The printer names each binder by its depth, so no name
  repeats; the model's `Den` accepts duplicate labels. They concern the Rust
  front end, which `checker/tests/core_roundtrip.rs` covers by testing.
- **Label table.** `labels` (T1) now lists each distinct label once, in order of
  first occurrence, the numbering lowering gives. Before, it kept repeats, so a
  label after a repeat got a larger index than lowering assigns.
- **Printer alignment.** `GoatPrinterTable.v` is generated: the Rust test fails
  when the committed file differs from what the Rust printer writes
  (`UPDATE_PRINTER_TABLE=1 cargo test -p goat_checker --test core_roundtrip`
  rewrites it), and the Coq build fails when the Coq printer disagrees with a
  row.
- **Match rule.** The checker types a `match` as phase 3 models it: the
  scrutinee is pinned to the group of the arms' tags, and the arms name every
  tag of that group or end in an `else`. The host's event and shape families
  are the one exception: a match on them still narrows an open row, outside
  this model.
- **Not covered.** Free variables (T3 is for programs), the grouped style, a
  `letrec` (T1 reads one; the printer does not write one), the unit value on its
  own, `float(e)`, everything T1 leaves out.

## CI

`.github/workflows/coq.yml` builds this directory under Rocq on the self-hosted
runner image, in its baked `rocq-9` opam switch (Rocq 9.1.1, Ott 0.34, metalib).
The job fails with the expected versions when the switch is missing. It triggers only on
changes under `proofs/**` (or to the workflow), plus manual dispatch, so
ordinary Rust PRs do not pay for a Coq image. It is intended as an
informational check, not a required one — promote it in branch protection once
the development stabilizes.
