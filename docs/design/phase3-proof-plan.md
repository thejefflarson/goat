# Phase 3 proof plan: tags, variants, `match`, lists (design pass)

Status: DRAFT for owner decisions. No Coq has been written. Issue #452, part of
#435, governed by ADR 0037. Written against `master` at 09dc843. PR #485 (ADR
0038, the kinding environment `D`) had not merged when this was written; every
statement below that mentions the judgment assumes the post-#485 shape
`typing D G e T`.

## 1. What the checker does today

Read from `checker/src/infer.rs`, `lower.rs`, `ty.rs`, ADRs 0010, 0016, 0028,
0030, 0036, and `docs/semantics.md`.

- **Tag declarations are hoisted and program-wide** (`lower.rs`
  `declare_tags`). Two kinds. A lone `tag Circle` (no group name, one case, no
  payload) is *flat*: the tag builds an **open** row `<Circle: Unit | r>`. Any
  declaration with a group name, a payload, or a `|` is a *group*: each of its
  tags builds the group's whole **closed** row (`construct_grouped`), and a tag
  belongs to exactly one group. A flat tag may be redeclared (idempotent); a
  grouped one may not. `Empty` and `Link` are built-in flat tags.
- **Payload shapes.** A tag with 0 arguments has payload `Unit`, with 1 its
  type, with n >= 2 the closed record `{0: T0; 1: T1; ...}`. `Link(a, b)` is
  `Link({0: a, 1: b})`. A group's payload types are monomorphic and restricted
  to `Number` (= Float), `Int`, `Bool`, `Unit`, `String`, records of those, and
  the group itself. No lists, no functions, no type parameters.
- **Rows.** A variant type is `Ty::Variant(Row)` on the same row type as
  records (scoped labels, open tail or `nil`). Construction of a flat tag has
  type `<C: T | r>` with `r` fresh. Rows keep labels sorted, so declaration
  order is not in the type; ranks (ADR 0036) live in a program-wide side table
  `tag_ranks` (`or_insert` in `lower.rs`) that no typing rule reads.
- **`match`** (`infer_match`). The scrutinee is unified with an open variant
  row. Each arm `C(binders)` adds `<C: T | fresh>` to it by unification
  (`constrain_arm`); an arm for a tag outside a *closed* scrutinee row, or a
  repeated arm, is an error. Arm bodies are joined to one result type. With an
  `else`, the scrutinee row stays open. **Without** an `else`, `close_match`
  demands an arm for every tag in the row and then *closes the row tail to
  `nil`*. So exhaustiveness is part of inference, not a later pass.
  Arm binders are monomorphic. A pattern with k >= 2 names types its payload
  as the **closed** record of exactly those fields; one name binds the whole
  payload.
- **Lists are not a type.** `[a, b]` lowers to `Link({0: a, 1: Link({0: b, 1:
  Empty})})`. `[x, ...xs]` patterns lower to a decision tree of nested
  `match`es on `Empty`/`Link`. `type_of("Link(1, Empty)")` is `[Link: {0:
  Number, 1: [Empty | t]} | t']`: an open row. `for x in xs`, `[a, b] = xs`
  and list parameters lower to the same tags.
- **Recursive types are inferred, equi-recursive.** `x = row` that mentions `x`
  under a variant payload is tied into `Ty::Rec` by `tie_row_knot` (guarded:
  the cycle must cross a tag, `Guard`). A recursive group
  (`tag Tree = Leaf | Node({left: Tree, right: Tree})`) is `Ty::Rec` from the
  start. Even `length(xs)` over a list needs it: the parameter type must equal
  its tail's type.
- **Literal `match`** (`lower_literal_match`) is a pure desugar to
  `v = e  if v == 0 then ... else ...`. A number or string match needs an
  `else`; a bool match naming both values does not.
- **`gen_value`**: `Tag(payload)` is a syntactic value iff its payload is
  (`is_syntactic_value`). A `match` is not.
- **Constraints that touch variants** and are *not* phase 3: `==`/`<` on rows
  (`Eq`, phase 6), `++` on lists (`Appendable`, a row sort).

## 2. Calculus additions (draft, subject to section 3)

Syntax. Types: `T ::= ... | <R>` (variant type, reusing the row nonterminal `R`,
so scoped labels and `swap` equivalence come free). Terms: `C(e)`, and
`match e do C1(x1) then e1 ... Cn(xn) then en [else e0] done`. Values:
`C(v)`. Environment: a tag signature `Delta`, an *ordered* list of
declarations: `flat C : T` or `group g { C1 : T1 | ... | Cn : Tn }`, every
`Ti` closed.

Typing (sketch).

- `T_TagFlat`: `Delta(C) = flat C : T0` and `G |- e : T0` give `G |- C(e) : <C: T0 ; R>` for any row `R`.
- `T_TagGroup`: `Delta(C) = group g {...}` and `G |- e : Ti` give `G |- C(e) : <C1:T1;...;Cn:Tn; nil>`.
- `T_MatchClosed`: `G |- e : <C1:T1;...;Cn:Tn; nil>`, labels distinct, each arm
  `G, xi:Ti |- ei : T` give `G |- match e do ... done : T` (exhaustive).
- `T_MatchElse`: same with scrutinee `<C1:T1;...;Cn:Tn ; R>`, `R` any row, plus
  `G |- e0 : T`.
- `T_Conv` gains the variant congruence rule; `teq` gains `<R> ~= <R'>`.
- `gen_value (C(v))` when `gen_value v`.

Reduction. `C(e) --> C(e')`; `match C(v) ... --> ei[xi := v]` when `C = Ci`;
`--> e0` when `C` is none of the `Ci` and there is an `else`; scrutinee
congruence.

Theorems that change: `progress` and `preservation` gain the cases above
(canonical forms: a closed value of type `<R>` is `C(v)` with `C` in `R` by
the existing L3 row surfacing; with no `else`, `C` is one of the arms because
the closed row is exactly the arm labels); `soundness` follows. `typing_weaken`,
`typing_tsubst_fix` (L4/L5) and the term-substitution lemmas L6a/L6b gain a
case each. No new statement is needed beyond threading `Delta`.

## 3. Decisions the owner must make

Each is a semantics, proof-model or theorem-statement question. Options are
concrete; the recommendation is mine and decides nothing.

### Q1. How tag declarations enter the judgment

```goat
tag Level = Low | Medium | High
tag Circle
x = Circle
match Low do Low then 1 Medium then 2 High then 3 done
```
- **A. A signature `Delta` carried by the judgment** (`typing Delta D G e T`),
  closed payload types, with a well-formedness hypothesis on every theorem
  (distinct names, one group per grouped tag). Faithful to the checker's
  program-wide table; `T_Tag*` look the tag up.
- **B. Elaborate declarations away**: a program is `Delta` plus a term, and a
  `tag` use is typed by a premise supplied in the rule with no environment.
  Smaller judgment, but "undeclared tag" is not rejected by the rules, so the
  later completeness theorem cannot say the checker's "unknown tag" error is
  right.
- **C. `Delta` as a Coq Section variable** that closes to option A in the
  statements; less text in lemma statements, same threading cost.

Recommend **A** (a Section variable inside the files, an explicit argument in
the final theorem statements). Closed payloads make `Delta` stable under type
substitution, so the L5 substitution lemma only passes it through.

### Q2. Do ranks (ADR 0036 amendment) enter phase 3?

Ranks are read only by `<` on tags. `<` on tags is phase 6 per ADR 0037 and
`semantics.md` section 1.
- **A. `Delta` is an ordered list; the rank of a tag is its position; no phase-3
  rule reads it.** The ADR 0036 amendment states this one sentence (rank =
  position in `Delta`, prelude declarations first, `Empty` before `Link`, a
  group's tags consecutive) and phase 6 reads it.
- **B. Put an explicit `rank : tag -> nat` in `Delta` with a well-formedness
  condition** matching the checker's `or_insert` rule. More Coq, nothing in
  phase 3 uses it.
- **C. Leave order out of `Delta` until phase 6.** Cheapest, but changes the
  signature later and touches every `Delta` lemma twice.

Recommend **A**. Wrinkle for the amendment: the checker allows a flat tag to be
redeclared and ranks it at its *first* declaration, so "position in `Delta`"
means first occurrence, and `Delta` must accept an idempotent flat repeat.

### Q3. Closed groups versus open flat tags: two typing rules, or one?

```goat
tag Shape = Circle(Number) | Dot
tag Ping
f = program(s) do match s do Circle(r) then r Dot then 0 done done   # closed
g = program(p) do match p do Ping then 1 else 2 done done            # open
```
- **A. Two construction rules (`T_TagFlat` open, `T_TagGroup` closed) and the
  group type is the structural closed row `<...; nil>`.** Same as the checker:
  `close_match` on an open row also produces a structural closed row, and a
  group type is not nominal.
- **B. A nominal `Named g` type for groups.** A new type former with its own
  equality; contradicts `construct_grouped` and breaks unifying a closed
  match with a group value. Not recommended.
- **C. Drop flat tags from the calculus** (everything grouped). The prelude's
  `Empty`/`Link` and the host's flat tags would no longer be representable.

Recommend **A**.

### Q4. Is exhaustiveness part of typing?

```goat
tag Level = Low | Medium | High
match x do Low then 1 Medium then 2 done    # checker: error, High unhandled
```
- **A. Yes, in the rules** (`T_MatchClosed` needs an arm per tag of a closed
  row; `T_MatchElse` is the only way to leave tags out). `progress` keeps its
  present statement: a closed well-typed term is a value, steps, or traps.
  Faithful to `close_match`.
- **B. Separate `exhaustive e` predicate** and `progress` takes it as a
  hypothesis. Weaker theorem; hides a gap the checker does not have.
- **C. A runtime "match failure" trap** so a non-exhaustive match types and
  `progress` allows `traps`. Weakest: the checker never lets this happen, and
  the trap would be a new observable behavior.

Recommend **A**. A also decides: an `else` on an already-exhaustive match is
accepted (the checker accepts it, `lib.rs`
`a_grouped_match_may_still_have_an_else`), and a repeated arm has no derivation
(distinctness premise), which also makes reduction deterministic.

### Q5. What recursion does phase 3 get? (the dead-end question)

Lists are open variants and every list function (`length`, `sum`, `map`) needs
a recursive type: `length`'s parameter must equal its tail's type.
ADR 0037 decision 3 puts iso-recursive `mu` types, `fold`/`unfold` and the
elaboration theorem in phase 5 (#454).
- **A. Phase 3 has no recursive types.** Lists are finite nested rows
  (`Link(1, Link(2, Empty))` types), recursive groups (`tag Tree = ...`) and
  recursive list functions are out until phase 5. Soundness covers tags,
  variants, `match` and list *literals and fixed-shape matches*. Cheapest, and
  respects the phase order, but the "lists" in the title are then little more
  than syntax, and the prelude's list functions stay unmodeled.
- **B. Pull the minimal iso-recursive core into phase 3**: `mu a. T`, `fold`,
  `unfold`, with the list literal and `Link(...)` elaborated to insert folds.
  Phase 3 then proves `length`. But `typ` has **no type binder** today (type
  variables are a free-atom set, `goat.ott` header); `mu` is the first one, so
  every type function (substitution, `ftv`, `lc`, `gen`, `teq`, row lemmas)
  changes. That is the bulk of phase 5, done early and under a deadline.
- **C. Equi-recursive `mu` in the calculus** (`mu a. T ~= T[mu a. T / a]` in
  `teq`), matching the checker directly. Contradicts ADR 0037 decision 3, and
  `teq` loses its syntax-directed inversions (arrow/record inversion in L2,
  which `T_Proj`/`T_App` rely on).

Recommend **A**, with the ticket text and the PR saying plainly that recursive
list functions are modeled in phase 5. If the owner wants lists to be
meaningful at phase 3, **B** is the only route consistent with ADR 0037, and
it should be its own ticket ordered before this one, not folded in.

### Q6. Lists: sugar over tags, or a primitive type?

```goat
xs = [1, 2, 3]
match xs do [] then 0 [x, ...rest] then x done
```
- **A. Sugar: `Empty`/`Link` are built-in flat tags in `Delta`; `[a, b]` is
  `Link({0:a, 1:Link({0:b, 1:Empty})})`.** What `lower.rs` does; lists are
  open, structural, and compare by the same rule as tags (ADR 0036). No new
  calculus constructs.
- **B. A primitive `List T` type with `nil`, `cons`, and a list `match`.**
  Simpler types, but a different language from the checker (open rows,
  `Appendable`, mixing with `else`), so the completeness theorem of ADR 0037
  decision 2 would not hold.

Recommend **A**.

### Q7. Payload shape and arm binders

```goat
tag Pair(Number, Number)
match p do Pair(a, b) then a + b done
```
Checker: payload is `{0: ., 1: .}` (closed record); a pattern with k >= 2
names types the payload as the *closed* record of exactly those fields.
- **A. One binder per arm; k-ary patterns denote to projections.** The arm
  binds `p`, and the denotation replaces `a`, `b` with `p.0`, `p.1`; `T_Match`
  gets a premise that the payload is the closed record when k >= 2. One
  locally-nameless binder, like `x = e1 e2`. Matches the checker's
  closedness; projections do the rest.
- **B. A telescope of k binders per arm.** Direct, but multi-binders were
  already costly (`program` is curried internally for that reason).
- **C. Tags take one argument only in the calculus**; multi-argument surface
  syntax elaborates to a record literal and a projecting arm with *open*
  projection typing. The rules would accept payloads with extra fields that the
  checker rejects, so completeness (decision 2) fails in the other direction.

Recommend **A**. Labels `"0"`, `"1"` are interned like any label.

### Q8. Literal `match` and list patterns: calculus or denotation?

- **A. Neither is in the calculus.** A literal `match` denotes (in `GoatDen`) to
  `v = e  if v == lit then ... else ...`, exactly the `lower.rs` desugar, using
  phase-1 forms. List patterns denote to the nested `match` on `Empty`/`Link`.
  The calculus stays `match` on tags only.
- **B. A primitive literal-`match`** typing rule and reduction rule. Duplicates
  `if`/`==`.
- **C. Out of scope for phase 3**; a later "sugar" ticket.

Recommend **A** for literal match (the desugar is a short chain); for list
patterns see Q9. Unassigned in ADR 0037's phase list: `for x in xs`,
destructuring (`[a, b] = xs`), list parameters, `and`/`or`/`not`, loops.
Recommend phase 3 owns only list literals and list `match` patterns as
calculus-level concerns; the rest get a later ticket.

### Q9. How much of the parser fragment?

`GoatDen`/`GoatShape`/`GoatPrint*` prove T1 (parse denotes a term) and T3
(print then parse round-trips). New: `tag_decl*` at the top, so the denotation
of a program becomes `(Delta, e)`. `Name(args)` is a tag construction or a call
*by `Delta` lookup in `lower`*, and a local binding shadows a tag.
- **A. Tag declarations (with payload types), tag construction, `match` with tag
  arms and `else`, list literals; denotation is `Delta`-aware with the
  checker's precedence (local, then tag, then builtin); T3 proves
  non-capture.** Complete for the calculus, largest proof.
- **B. Same fragment as A, but T1/T3 assume tag names and bound names are
  disjoint** (a hypothesis; true of the printer's `v0`, `v1`... binders).
  Avoids the shadowing proofs.
- **C. A plus list patterns**, i.e. the decision tree (`ListMatch` in
  `lower.rs`, ~250 lines, with cases per row and `rest`). No direct Coq
  analogue; the highest-risk piece of phase 3 on the parser side.

Recommend **B**, with list patterns out of the fragment until their own ticket
(consistent with Q8). The Rust side keeps honest through `rule_map.rs` and
`core_roundtrip.rs`, as for phases 1-2.

### Q10. Algorithm W

- **A. Separate follow-up ticket**, like #483 for phase 2 (W over the new forms:
  soundness only, differential test extended).
- **B. Inside this ticket.**

W's soundness is cheap (every derived type is derivable); *completeness* needs
row-variable closing (`close_match`) and the checker's order-sensitive
`row_subst.insert(var, Empty)` argued away. The declarative rules give the same
answer in any order, but the proof is not free.

Recommend **A**, matching ADR 0038 decision 4.

### Q11. Equality and `++` on variants

`==` on a variant type needs the `Eq` sort extended to rows (`constrain_row`);
`++` needs an `Appendable` row sort. Both are sorts in the sense of ADR 0038.
- **A. Out of phase 3.** `==`, `<` and `++` on tags and lists wait for phase 6
  (ADR 0037: structural ordering) and the `Eq` sort. In phase 3, no operator
  takes a variant.
- **B. Add the `Eq` and `Appendable` sorts in phase 3.** Extends `sort`,
  `finer`, `sat` of #485 with row cases.

Recommend **A**. It is consistent with `semantics.md` ("comparison of Unit,
records and tags (phase 6)"), but the first PR to touch `++` or `==` on lists
is then gated behind phase 6 under ADR 0037 decision 4.

## 4. Size estimate

Calibrated against phase 1 (#460: +2630/-645 across 37 files) and phase 2
(#478: +1279 across 25 files; parser fragment #482: +1264).

| File | Change | Lines |
| --- | --- | --- |
| `goat.ott`, `goat_ln.ott`, `Goat_ott.v` | `<R>`, `C(e)`, `match`, an arm list (mutual, like `fields`), values, rules | 150 |
| `GoatDefs.v` | `Delta`, typing rules, step rules, `gen_value` | 120 |
| `GoatRows.v` | variant congruence, no-confusion, inversion for `<R>` | 60 |
| `GoatMeta.v` | `lc`, regularity, canonical forms for variants, progress cases | 250 |
| `GoatSubst.v`, `GoatBij.v`, `GoatHM.v` | a case per new construct | 100 |
| `GoatSound.v` | L4/L5/L6 and preservation cases (match: substitution of the payload) | 450 |
| `GoatPhase3.v` | worked examples (Shape, Level, list literal, non-exhaustive has no derivation) | 250 |
| `docs/semantics.md`, README, ADR 0036 amendment | prose | 200 |
| Parser: `GoatDen`, `GoatShape`, `GoatPrint*`, `GoatPrinterTable`, `rule_map.rs`, `core_roundtrip.rs` | per Q9 option B | 900-1200 |
| **Total, calculus + soundness** | | **~1400** |
| **Total with parser fragment** | | **~2400** |

Algorithm W extension (Q10): a further ~400, own ticket.

## 5. Risks

1. **No recursive types (Q5).** The biggest risk. Without them phase 3 proves
   soundness for a language whose lists cannot be traversed; with `mu` now,
   `typ` needs its first binder. Choose before the port starts.
2. **Phase-2 repeat: the judgment changed midway** (ADR 0038 added `D` after
   the port began). The equivalent here is `Delta`: if it is threaded after the
   first lemma is written, every statement changes. Fix its shape (Q1) first.
3. **Scoped labels in variant rows.** A row can hold `A` twice, so a closed
   row of the arm labels could differ from the scrutinee's row by a shadowed
   label. It is sound: a value `A(v)` has the *first* `A`'s payload type by L3,
   and the shadowed one is uninhabited (no `inject`). The proof must say so;
   it is not a decision but it is the one non-routine lemma in `progress`.
4. **`typ` mutual induction.** `typ_Variant row` rides on the same mutual
   `typ`/`row` induction as `typ_Record` (about 80 `typ_Record` occurrences
   across 12 files), so each is a mechanical sibling, but each `Fixpoint`,
   `inversion` on `teq` and `lc_at` clause changes. Budget build churn, not
   proof difficulty.
5. **Parser: `Delta`-aware denotation and shadowing (Q9).** `lower` resolves
   tag versus variable, so the denotation is no longer a function of the
   parse tree alone. T3 needs the disjointness hypothesis (B) or a
   shadowing proof.
6. **The list-pattern decision tree (Q9 option C)** has no Coq analogue. Avoid.
7. **Spike worth doing before the port.** The hardest single lemma is
   `progress` for `T_MatchClosed`: from `G |- C(v) : <R>` and `R ~= (C1:T1;...;
   Cn:Tn; nil)` conclude `C` is some `Ci` with `v : Ti`. It needs L3 twice
   (surface `C` in the value's row and in the arm row) plus "labels of an arm
   row are distinct". A 100-line spike over `GoatRows.v` alone, before any
   syntax change, would settle whether L2'/L3 give it directly or the row
   lemmas need a label-set characterization. I did not run it: this pass
   writes no Coq.
