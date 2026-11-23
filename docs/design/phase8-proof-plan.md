# Phase 8 proof plan: the parser over the full grammar (design pass)

Status: DRAFT for the architect, with owner questions in section 9. Issue #457,
part of #435, governed by ADR 0037 (phase 8, "the parser over the full grammar")
and ADR 0030 (the core-fragment parser claim it grows). Written against `master`
at 72d6145, after phase 5 (methods, dot calls on any receiver) and phase 6
stages 1a to 1c. The owner delegated the proof-model choices to this pass; each
is recorded in section 3. No `proofs/`, `parser/`, `checker/` or ADR file
changes in this PR.

Terms. **T1** is `parse_denotes_lc`: every complete parse tree of the top rule
`goat` denotes (`Den_goat`) a term that is locally closed. **T2** is
`peg_deterministic`: a token stream has at most one parse. **T3** is
`print_parse_roundtrip`: parsing the printed text of a closed term gives a tree
that denotes that term. **The fragment** is the set of trees the three theorems
cover: today the trees built only from `core_rule` rules (`GoatShape.v`) and
satisfying `Complete`. **Trivia** is whitespace and comments, which the lexer
sets aside. **Lowering** is `checker/src/lower.rs`, the Rust pass from the parse
tree to HIR; "denotes" means the Coq `Den` relation says what lowering does.
**Recovery** is `parse_recovering` in `parser/src/interp.rs`, which builds a tree
with `ERROR` and `MISSING` nodes from broken input.

## 1. Where the proved fragment stands

`grammar/goat.peg` has 80 rules. `parser/tests/rule_map.rs` classifies each as
`Core(<Ott production>)` or `Outside`: 47 are Core and 33 Outside. All 77 are in
the generated `GoatGrammar.v` (the grammar is generated, never transcribed), so
the generic half of the story is already whole: **T2 is stated for any PEG
expression and any input, so it already covers the full grammar** and needs no
work beyond regenerating. T1 and T3 are what the fragment limits. They are
limited three ways: by rules (`core_rule`), by tree shape (`Complete`), and by the
input being a token list (the lexer is trusted, ADR 0030 decision 2).

### 1.1 Rules outside (`rule_map.rs` `Outside`)

| Rule(s) | What it is | Why it is out today |
| --- | --- | --- |
| `tag_decl`, `tag_kw`, `group_name`, `tag_case` | `tag Shape = Circle(Number) \| Dot` | The calculus has `con`/`match` over a group `w` (phase 3) but `Den` does not build one from a declaration |
| `list`, `list_pattern`, `match_expr`, `arm`, `pattern`, `labels`, `literal_pattern` | `[a, ...r]`, `match`, scalar-literal arms | Same: the parser fragment was not grown with phase 3 (`e_con`, `e_match` are exempt in `every_ott_production_is_reached_by_some_core_rule`) |
| `and_op`, `or_op`, `not_op`, `negation` | `and`, `or`, `not`, unary `-` | No Ott node: the HIR has `And`, `Or`, `Not` and lowering emits `0 - x` for `-x`; the calculus does not |
| `sequel` | the `;` of a statement | No rule reads it, so the tree is not decoded; `Den` would need to read `a; b` as a binding of a hidden name |
| `foreign_kw`, `foreign_decl`, `foreign_name`, `fn_type`, `_type_expr`, `list_type`, `record_type`, `field_type`, `type_name`, `infer_type` | `foreign "m" "f" (Number) -> Unit` and the type syntax of tag payloads | The calculus has no foreign constant (phase 6b of #435 is decided but not built) and the only type syntax is in these two places |
| `repeat_loop`, `count_loop`, `each_loop`, `for_kw`, `from_kw`, `to_kw`, `in_kw` | `repeat`, `for i from a to b`, `for x in xs` | Loops need no calculus extension (README, "Loops and foreign calls"): lowering desugars them to a self-recursive local function. `Den` has no rule for that desugaring |

### 1.2 Shapes the `Complete` predicate excludes

`Complete` (`GoatShape.v`, `complete_node`) removes trees that are valid goat but
that `Den` does not read. Each is a row of the plan:

| Excluded shape | Source of the exclusion |
| --- | --- |
| `program()` (no parameter) | `R_params` must be present: the calculus has one binder |
| an empty body `do done`, a call with no arguments `f()`, an empty program | `has R_expr`, `has R_arguments`: no unit-argument reading |
| a block that ends in a binding | `last_is_decl` |
| a function binding after a value binding in one block | `fns_first`; owner decision 6 on PR #482, "a later phase decides placement by free variables" |
| a function binding as an operand (`1 + f = program(x) do x done f(2)`) | `local_ok` |
| a run of two or more operators (`1 + 2 * 3`) | `ops_ok`: lowering resolves precedence (ADR 0013) and the model does not |
| a spread that is not first, or two spreads | `spread_first` (lowering reports it; see 2.7) |
| a record pattern or any list pattern as a parameter | `not_pattern` and `R_list_pattern` out |
| a dot call inside an expression with an operator | phase 6 widened this; kept only where `ops_ok` bites |

### 1.3 Beyond the tree

- **The lexer is trusted.** A parse takes a token list. Nothing relates source
  text to tokens: not identifiers, numbers, string escapes, comments, the
  reserved words, nor the contextual words `from`, `to`, `in` and `foreign`. The
  owner decided (2026-11-15, #457 comment, item 4) that the lexer is "verified
  once for the whole grammar" after phases 3 to 6 land. They have, so this phase
  owns it.
- **A text terminal matches punctuation or keyword tokens only.** The four
  contextual words are names everywhere except where a rule spells them out, so
  the model cannot match them. No core rule spells them; the loop rules do.
- **Recovery** is a Rust-only feature the generated grammar drops (the `@expect`,
  `@sync`, `@anchor` and `@nest` annotations "change nothing about valid input").
- **The printer** writes the curried style for the printable core only. T3's
  `scoped` excludes the unit value, `Float` values, `float(e)`, `e_restrict` and
  letrec groups (owner decision 5 defers the letrec case "to the tail of phase 8").

## 2. How each outside rule extends T1, T2 and T3

The rule of ADR 0030 decision 5 governs: **the parser claim cannot be larger than
the calculus.** A rule whose meaning the calculus cannot state stays out, however
simple its grammar. Section 2 sorts every row of section 1 into *extends now*,
*extends by desugaring* (lowering reads the construct as a combination of core
forms, so `Den` does too and nothing in the calculus changes), and *stays out*.

### 2.1 Tags, `match`, lists (stage 4)

The calculus has `con w tg (e)` and `match w (e) with ars` (phase 3), the prelude
supplies the `List` group, and lowering already builds exactly these. T1 extends
by new `Den` rules:

- **Declarations.** `tag_decl*` is read first, as a pass over the leading
  children, into a declaration table (group `w`, tag name to number, payload slot
  codes). The reading of the rest of the program takes that table as a parameter.
  This is two-pass because tags are hoisted: "every tag is visible to the whole
  program".
- **The prelude.** Lowering prepends `prelude/prelude.goat`, so the program's
  table starts from the prelude's. T1 is stated for **any initial table** `D0`
  and is instantiated by a Coq lemma that reading the prelude's tree yields the
  table the generated example uses. That keeps the prelude out of every proof
  while the proof gate still fires when it changes.
- **Construction and match.** `Circle(2)` is `con w tg (2)`; a tag with no payload
  is `con w tg (unit)`; `match` reads each `arm` to an arm of `e_match`, an `else`
  arm to the default, and `[x, ...rest]`, `[]` to the `List` tags (`Link`, `Empty`).
- **Scalar literal arms** (`match n do 0 then ... done`). Lowering reads them as a
  chain of `==` comparisons; `Den` follows lowering (a stage-4 reading task: the
  note does not decide this from the source alone, see D2 of section 3).
- **Tag payload types** (`_type_expr` in `tag_case`). The calculus slots a payload
  as a base type, the group itself (slot 0), or a parameter (slot `6 + j`).
  `Circle(Number)`, `Cons(_, Pile)` and `Link(a, List)` fit. A payload `[Int]` or
  `{x: Int}` has no slot code. Those shapes are `Outside` (a named residue, 2.9)
  unless stage 4's reading of lowering shows them reduced to slots.
- **Exhaustiveness and the match rule.** `Den` does not check the arms name every
  tag; T1 says only that the parse denotes a term. The checker's match rule is the
  typing claim, not the parsing one.

T2 needs nothing. T3: the printer gains `con`, `match`, and list syntax; the
printable set grows by `scoped` admitting `e_con` and `e_match` over a printable
table. The printer's own table is generated like `GoatPrinterTable.v`. The hard
part is only that a printed program must also print its `tag` declarations first,
so T3 for tags states the round trip for `(D, e)`, not `e` alone.

### 2.2 `and`, `or`, `not`, unary minus, operator runs (stage 3)

*Landed.* The theorems are `resolve_total`, `resolve_lc` and the reading lemmas
(`resolve_one`, `resolve_left`, `resolve_right`, `resolve_not_loose`,
`resolve_not_tight`) of `GoatPrec.v`; `GoatPrecTable.v` is generated from the
behaviour of lowering rather than from `lower.rs`'s source text, so the check
cannot pass by reading the same table twice. The evidence that `and` is the `if`
is the differential reader reading HIR `And`/`Or`/`Not` as `if`, with 0
mismatches, in place of the `core_roundtrip.rs` case sketched below.

`ExprKind::And`/`Or`/`Not` have their own typing in the checker
(`infer_logic`: Bool operands, Bool result) and lowering gives `-x` as `0 - x`
(with a `+ 0.0` so `-0.0` becomes `0.0`, lowering line 1283). The calculus models
none of them. Two ways to bring them in:

- **A: new Ott nodes** `e_and`, `e_or`, `e_not` with typing and step rules.
- **B: derived forms.** `a and b` is `if a then b else false`, `a or b` is
  `if a then true else b`, `not a` is `if a then false else true`, `-x` is
  `0 - x` (and the float form lowering writes). `Den` reads them so; the calculus
  does not change.

**Chosen: B**, because the typing agrees (`if` with a Bool test and Bool
branches is `infer_logic`'s whole rule), `if` is already proved, it keeps
`goat_ln.ott` and the generated `Goat_ott.v` fixed, and it is the same device
phases 5 and 6 used for dot calls. The cost: the HIR's short-circuit `And` is
read through `if`, so the evidence that lowering agrees is a Rust test over the
generated programs (`core_roundtrip.rs` grows an `and`/`or`/`not` case reading the
lowered `If`-shaped HIR) rather than a Coq theorem. A would make that a theorem at
the price of a calculus extension in the middle of a parser phase, and it fails
the "cannot be larger than the calculus" rule in reverse (it widens the calculus
for the parser's sake). If the differential reader already reads `And` as `if`, B
is free; otherwise it adds one line to the reader.

**Operator runs and precedence.** `_statement <- _operand _more_math*` is a flat
run; lowering resolves it by `prec` (7 levels, `Or` loosest, left-associative;
`not` binds at level 3 and takes the operand after it) in a precedence-climbing
pass. T1 needs a Coq `resolve` function equal to that pass. The plan:

1. A Coq `prec : op -> nat` and `resolve : operand -> list (op * operand) -> exp`,
   total, by precedence climbing over the flat run.
2. A generated table (`GoatPrecTable.v`, as `GoatPrinterTable.v` is) the Rust
   test checks against `lower.rs`'s `prec`, so the two cannot drift.
3. `Den` for a run is `resolve` applied to the denotations of the operands.
4. A theorem that `resolve` of a single operator is the one-operator reading
   already proved (so the phase 1 case is a corollary), and that resolving a run
   of two operators of different level nests the tighter one (the check a reader
   expects).

T3: the printer parenthesises every nested operation (as today), so a printed
term never contains a run and the printer needs no precedence. Under B there is
no term for `and`, `or`, `not` or `-` to print: the derived forms are `if` and
`0 - x`, which the printer already writes. T3 gains nothing here and loses
nothing; it states the round trip through `Den_goat var_of t e`, which reads a
printed `if` as an `if`.

### 2.3 Strings (stage 1 and 2)

The grammar has `STRING` as a token and nothing more: no interpolation, no
operators. "Strings beyond literals" is therefore a lexer matter (escapes,
unterminated quotes) and a builtin matter (`char_at`, which is a prelude function
the checker types, not syntax). With the lexer verified, a string token carries
its source bytes. **Chosen: `e_str q` keeps `q` abstract**, related to the bytes
only by a `str_of` function the lexer defines. No rule of the calculus reads the
characters of a string, so a theorem that `Den` agrees on the unescaped contents
would be a statement the soundness proof never uses. Revisit if the string
builtins enter the calculus.

### 2.4 Loops (stage 5)

`repeat n times do B done`, `for i from a to b do B done` (both ends included),
`for x in xs do B done` desugar (README, "Loops and foreign calls") to a local
recursive function that tests, runs the body, and calls itself:
`go = program(i) do if i < stop then _ = B go(i + 1) else () done done go(start)`.
All pieces are in the calculus: `letrec` (the hoisted group), `if`, `+`, `<`, and
for `in` the list `match`. So T1 extends by `Den` rules for the three loop shapes
with **fresh names** (`go`, the stop bound, the `_`), exactly as `DP_dot_bind`
takes a fresh `s` that no argument uses. Side condition: the fresh names do not
occur in the body or bounds (lowering guarantees it with symbols no source name
can spell). `for ... from ... to` needs the contextual keywords `from` and `to`:
that is the grammar-model change of 3.3 (a text terminal may match a name token
by spelling).

Evidence tying `Den` to lowering is again the `core_roundtrip.rs` pattern: the
generator writes the three loops and the test compares the lowered HIR to the
`Den` shape. A loop whose bound is `i <= stop`-shaped versus `<` is exactly the
detail that test exists to pin. T3: a loop never comes back from the printer (the
printer writes the desugared form, as it writes no dot call), so there is no T3
row; the claim is the lowering evidence.

### 2.5 The `;` statement rule, empty forms, block placement (stage 6)

`a; b` is `_ = a  b`: a binding of a hidden name, with the same freshness side
condition as a dot call's receiver. Each excluded shape of 1.2 gets a reading that
copies what lowering does:

- `do done`, an empty program, `program()`, `f()` all read to the **unit value**
  or a unit-taking function (`e_unit` is already a production, today reachable
  only through an `if` without `else`). The exact form for `program()` (does it
  bind a hidden unit parameter, and is `f()` an application to `e_unit`?) is read
  off `lower.rs` and the semantics note in the stage's first PR, and recorded in
  `proofs/README.md`. Any of those that lowering rejects goes to the reject class
  of 3.2.
- **A block that ends in a binding** reads as the binding with the unit value as
  its body, if lowering does (otherwise it is a reject).
- **A function binding after a value binding** (owner decision 6). The block's
  leading function bindings form the hoisted `letrec` (ADR 0003), and lowering
  places a later function by what it captures. `Den` needs a free-variable
  function over the denoted body: a function binding joins the hoisted group when
  none of its free variables is an earlier value binding of the block, and is a
  plain `let` otherwise. This is **the** nontrivial step of the stage: it adds a
  `DB_split` rule and a lemma that placement is order-independent for the
  functions that join the group. Estimated as the largest single lemma family
  (~500 lines).
- **A function binding as an operand** (`1 + f = program(x) do x done f(2)`) is
  the same placement decision inside `local`; it follows from the block rule once
  `local_ok` is relaxed.

T3: the printer never writes a `;` or an empty form (a printed term has none).
The letrec tail (stage 7) is the exception.

### 2.6 Foreign declarations and type syntax (stays out until phase 6b)

`foreign "m" "f" (Number) -> Unit` is an opaque typed constant in the checker;
the calculus does not have it (README: "This waits behind phase 1 ... listed as
phase 6b of #435"). The type syntax (`fn_type`, `list_type`, `record_type`,
`infer_type`, `type_name`) serves only `foreign` and tag payloads. **These stay
Outside** until 6b lands: a context entry and one step rule, after which T1 gains
a `Den` rule (a `foreign` binding denotes a name at the declared arrow type, with
the module and name checked to be string literals) and the types map to
slot-free `typ`. This plan does not schedule 6b; stage 8 lists the rows as a
named residue, with 6b as the unblocking ticket. The two rule groups cost about
350 lines once 6b exists.

### 2.7 Lowering errors and the reject class

The grammar accepts programs lowering rejects (`{...a, ...b}`, duplicate record
labels, repeated parameters, `program(x, x)`, a loop bound that is not a number
is a *checker* error, not lowering). CLAUDE.md's rule is "errors come only from
the checker"; the parser's T1 must say something about these trees.

**Chosen: T1 becomes a dichotomy.** For every parse tree `t` of `goat`, either
`Den_goat var_of t e` for some term `e` (and then `e` is `lc`), or `Reject t`
holds, where `Reject` is an inductive set listing exactly the shapes lowering
reports as diagnostics (a spread not first, two spreads, a duplicate parameter,
`program(x, x)`, ...). `Complete` becomes `~ Reject`, so the fragment stops being
a list of things the model does not read and becomes a list of things lowering
refuses, which is a property of the language, not of the proof. The Rust
evidence is a test that every shape in `Reject` is reported by lowering with a
span (`checker/tests/syntax_errors.rs` is the natural home), and that no tree
outside `Reject` is.

### 2.8 Comments, whitespace, the lexer, recovery

**Comments and whitespace (stage 1).** Trivia is a lexer concern: no grammar rule
mentions it. With a Coq lexer, T1 is restated over text: `parse_text` is `lex`
followed by the parse, and the theorem is `parse_text_denotes`: if `lex s = Some
ts` and the parse of `ts` succeeds, the tree denotes an `lc` term. The new
obligations are the lexer's own properties:

- **No gaps, no overlap.** The token spans partition the source (the Rust
  `lex` already promises this: "so the source reconstructs from the spans").
- **Longest match and word boundaries.** `doner` is a NAME and `done` is not; a
  numeral is maximal. Stated as `lex` taking the longest token of any class and
  a reserved word beating a name only at a word boundary.
- **Token stream determinism** (`lex` is a function, so trivially).
- **Trivia independence.** Two texts whose non-trivia tokens are equal parse to
  the same tree. Corollary of the definition (the parser reads the token list)
  and the premise of 4.

**The lexer model.** Written in Coq as a function over a list of bytes (`ascii`
and UTF-8 continuation handling), with `is_xid_start` and `is_xid_continue` as
**parameters** the Coq development does not define: identifiers follow Unicode
XID (`unicode_ident` in `lexer.rs`), and reproducing those tables in Coq is a
copy of someone else's data. The parameters are listed in `GoatAssumptions.v` and
checked in the differential test below. Restricting identifiers to ASCII would
make the model smaller and would change what the language is (a kid's name in
any script is a name today), so it is not taken; owner question 1 asks the owner
to confirm the parameter.

**Tie to the Rust lexer: a differential test, not a proof about Rust.** The Coq
`lex` is extracted (as W is, ADR 0037 decision 6) and compared to
`parser::lexer::tokenize` on every goat file in the repo, every string the Rust
tests quote (the corpus `goat/tests/format.rs` already walks), and the fuzzer's
programs. A disagreement fails CI. That matches the stance of ADR 0030 and ADR
0037: the Rust implementation is tied to the Coq model by testing, because the
tools to verify Rust of this kind are immature.

**Error recovery stays out of the claim.** Recovery produces a tree from input
that has no parse; the three theorems are about valid input. What is in scope is
the converse guarantee the grammar's header states ("recovery annotations steer
the parser on broken input and change nothing about valid input"). That is a
Rust test, not a theorem: for every valid file in the corpus, `parse_recovering`
and `parse` return the same tree with no `ERROR` or `MISSING` node (stage 8). The
Coq side needs nothing because the generated grammar has no annotations, which
is the model of "the annotation changes nothing". Recovery has no semantics to
connect to the proofs, so there is no T1 for it, only this agreement test.

### 2.9 What stays outside after phase 8

| Residue | Why | Unblocked by |
| --- | --- | --- |
| `foreign_*` and the type syntax rules | no calculus form | phase 6b of #435 |
| tag payload type shapes with no slot code (`[Int]`, `{x: Int}`, `(Int) -> Int`) | no slot | a phase 3 slot extension, or lowering rejecting them (stage 4 reading) |
| recovery (`ERROR`, `MISSING`, the annotations) | not a semantics | never; agreement test only |
| the Rust interpreter, lowering, lexer | tied by tests, not verified | Rust verification tooling (rejected, ADR 0037 decision 6) |
| the `Unicode` tables | a parameter | n/a |

`rule_map.rs` shrinks from 33 `Outside` rules to those in the first three rows;
its `every_ott_production_is_reached_by_some_core_rule` exemptions for `e_con`
and `e_match` go away with stage 4.

## 3. Proof-model decisions and the alternatives they beat

**D1. Where the lexer lives.** Chosen: a Coq `lex` function, extracted and
compared to the Rust lexer, with the Unicode identifier predicates as parameters
(2.8). Beaten: (a) keep it trusted (the owner's decision 4 of 2026-11-15 already
rejected this for the end of the phase); (b) verify the Rust lexer (rejected
tooling); (c) a Coq lexer defined by a *relation* with no executable. (c) cannot
be differential-tested, which is the only tie to the Rust, so a function.

**D2. Scalar literal arms.** Chosen provisionally: read as lowering does
(`==` chain). The source of lowering is the authority; a note in the stage-4 PR
records what it found. Beaten: adding a literal pattern to `e_match` (a calculus
change for a feature that desugars).

**D3. Reading side: relation `Den` plus an executable parser.** Today the PEG is
a relation (`peg e s r`) and the theorems are about it, with `rule_map.rs` and
`core_roundtrip.rs` as the Rust tie. Chosen: keep the relation as the spec and
add an executable, fuel-bounded interpreter `parse_fuel` with `parse_fuel_sound`
(a result of it satisfies the relation), extracted and compared to
`parser/src/interp.rs` on the corpus (stage 8). The two interpreters read the
**same** generated grammar, so the comparison pins the interpreters' semantics
(ordered choice, repetition, the `$` end) against each other. Beaten: relation
only (no machine check that the Rust interpreter implements the relation's PEG
semantics, the gap that remains on `master`); a complete verified parser with
`parse_fuel_complete` (a termination argument for a PEG with left-recursion
absent but unbounded repetition, much larger and buys no soundness).

**D4. Fresh names in a derived reading.** Chosen: each desugaring rule (loops,
`;`, dot call, rest pattern) states a freshness side condition on a name it
introduces and takes the name from a variable the program does not use
(`used_vars`, `GoatShape.v`), as `DP_dot_bind` and `unpack` do. Beaten: a
`gensym` function threaded through `Den` (a state monad in a relation) and
hygienic de Bruijn terms.

**D5. T1 as a dichotomy with `Reject`** (2.7). Beaten: keeping `Complete` as a
hypothesis. `Complete` would remain a list of unread shapes; a `Reject` set is a
claim about lowering, testable.

**D6. `and`, `or`, `not`, `-` as derived forms** (2.2). Beaten: new Ott nodes.

**D7. Precedence.** Chosen: a Coq `resolve` and a generated `prec` table checked
against `lower.rs`. Beaten: reading a run as an unresolved list in the model
(the model would then say nothing about the result's shape, the one property
parsers of arithmetic get wrong).

**D8. Placement of a function binding in a block** (2.5). Chosen: by free
variables over the denoted term, as owner decision 6 asks. Beaten: a purely
syntactic rule (functions first, today's `fns_first`), which is what shrinks the
fragment.

## 4. How the formatter (#539, ADR 0041) relates

The formatter is `editor/format.goat`, a goat program that returns whitespace
edits; the host applies them and refuses an edit that is out of order, out of
range, or over a non-whitespace byte. It does not print an AST, so it is **not**
a T3 consumer in the sense T3 means (a Coq printer over terms, mirrored by the
Rust printer in `core_roundtrip.rs`). It is a consumer of a different and
smaller theorem the verified lexer makes statable:

> **Trivia independence.** If two sources have the same non-trivia token stream
> (comments included), they parse to the same tree, and by T1 denote the same
> term.

`goat/tests/format.rs` already checks the *premise* per file (same tokens, same
tree, same checker result, idempotence). With a Coq lexer the premise becomes a
statement about edit lists: an edit list that replaces only whitespace and does
not merge or split a token (the check `goat::format::apply` could make at run
time by lexing before and after) preserves the token stream. That is worth a
small theorem (stage 1, ~150 lines): `apply_edits_preserves_tokens` for an
`edits_ok` predicate, with the runtime check as the Rust image of `edits_ok`.
It makes the formatter's safety, "a wrong program cannot change what a program
says" (ADR 0041 decision 1), a consequence of the proof rather than of tests
alone. **The formatter's style is not proved** (what is indented how is taste,
not semantics) and stays under `format.rs`'s tests. The formatter's scanner is a
copy of `highlight.goat`'s, not of `lexer.rs`; the differential test of 2.8 does
not cover it, and `format.rs` keeps doing that.

## 5. How #278 relates

#278 ("Formally verify the parser (grammar ⇄ Ott abstract syntax)") predates the
design: it asks for a machine-checked connection between `goat.peg` and the Ott
abstract syntax, weighs "a verified parser extracted", "a proof that the accepted
language maps onto Ott" and "a parser-validator checked in Coq", and notes error
recovery is out of the core. Its sprint (2026-11-11) was scoped to the Ott core
fragment, and that scope is ADR 0030's T1/T2/T3, which landed. #457 is the
remainder of the same goal over the full grammar, and 2.8 records the recovery
note it asked for. **Recommendation: close #278 as a duplicate of #457**, with a
comment that the options it weighed are settled in ADR 0030 (a generated grammar
and a relation plus theorems) and this note (the executable-parser tie, D3), and
that its three sub-issues (#369, #370, #371) shipped. Nothing in #278 is
unrepresented in #457 after this note, so folding it in as a sub-checklist adds no
information. The architect may close it; this PR does not touch the tracker.

## 6. Which files change

| File | Change |
| --- | --- |
| `proofs/GoatLex.v` (new), `GoatLexSpec.v` (new) | the lexer model and its properties; the Unicode parameters |
| `proofs/GoatGrammar.v` | regenerated; text terminals may match a name token by spelling (stage 2) |
| `proofs/GoatShape.v` | `core_rule` grows to all rules but 2.9's residue; `gen` and `complete_node` give way to `Reject` |
| `proofs/GoatDen.v`, `GoatParse.v` | `Den` rules for the new constructs; T1 restated over text, as a dichotomy |
| `proofs/GoatPrec.v`, `GoatPrecTable.v` (new, generated) | `resolve` and the `prec` table |
| `proofs/GoatPrint*.v`, `GoatPrinterTable.v` | printer cases for the new constructs; T3 over `(D, e)` for tags |
| `proofs/GoatPegExec.v` (new) | `parse_fuel` and `parse_fuel_sound` |
| `proofs/GoatAssumptions.v` | the Unicode parameters, any new theorems |
| `parser/examples/emit_coq.rs` | regenerates the grammar; no change expected |
| `parser/tests/rule_map.rs` | `Outside` shrinks; the exemptions for `e_con`/`e_match` go |
| `checker/tests/core_roundtrip.rs`, `syntax_errors.rs` | generator and evidence for each stage's constructs; the `Reject` agreement test |
| `proofs/README.md`, ADR 0030 and ADR 0037 | brought up to date in the close-out stage |

No stage changes `grammar/goat.peg` or the calculus. The proof gate (ADR 0037)
fires on the grammar, `infer`/`lower`/`ty` and the prelude; every stage here
changes `proofs/`, so it is satisfied. A stage that edits only `rule_map.rs` or
tests needs no label.

## 7. What is proved at the end

- **T1** (over text): for every source `s` that lexes and parses, the tree either
  denotes a locally closed term, or is a `Reject` shape lowering reports.
- **T2**: unchanged, already for the whole grammar.
- **T3**: for a closed term over a tag table, with side conditions as today,
  parsing the printed text denotes the same term; printable set grown to tags,
  `match`, lists, `and`/`or`/`not`/`-`. The letrec tail is stage 7.
- **Lexer properties** (2.8), **trivia independence** and
  **`apply_edits_preserves_tokens`** (section 4).
- **`parse_fuel_sound`**, with the extracted parser agreeing with the Rust
  interpreter on the corpus (a test).

Not proved: lowering, the Rust interpreter and lexer, recovery, the Unicode
tables, the formatter's style, and the residue of 2.9.

## 8. Staged PR plan

Sizes are lines added to `proofs/` and tests, excluding generated files, and are
calibrated on phase 5 stage 6 (parser, dot calls, ~350) and phase 3 (+1235 across
25 files). `GoatShape.v` is 1733 lines for the core fragment, and the later
stages extend its `gen` and `Complete` per rule, so rule-heavy stages are
priced by rules added. Stage 4 and stage 6's block placement are the least
certain numbers.

| Stage | Contents | Size | Depends on |
| --- | --- | --- | --- |
| 0 | this note | ~450 (docs) | none |
| 1 | the lexer: `GoatLex.v` (`lex`, no gaps, longest match, word boundaries), the Unicode parameters, `parse_text` and T1 restated over text for the existing fragment, the extracted-lexer differential test, `apply_edits_preserves_tokens`; ADR 0030 amendment (decision 2 retired, the parameters recorded) | ~1500 Coq, ~250 Rust | none |
| 2 | grammar model: a text terminal matches a name token by spelling, so `from`, `to`, `in`, `foreign` can be spelled by a rule; regenerate `GoatGrammar.v`; T2 re-checked | ~200 | 1 |
| 3 | operators: `and`, `or`, `not`, unary minus as derived forms, precedence `resolve` and its generated table, `ops_ok` retired, one-operator corollary, `core_roundtrip.rs` cases | ~1200 | none (parallel to 1, 2) |
| 4 | tags, `tag_decl`, `match`, lists, list patterns, scalar literal arms; the two-pass declaration table and the prelude parameter `D0`; `rule_map.rs` loses its tag exemptions; T3 for tags over `(D, e)` | ~2500 | 3 (operators in arm bodies); the largest stage |
| 5 | loops: `repeat`, `for ... from ... to`, `for ... in` as fresh-name desugarings; the evidence generator cases | ~600 | 2 (keywords), 4 (`for in` uses lists) |
| 6 | the block: `;` statements, empty forms, `program()`, a block ending in a binding, function binding placement by free variables, a function binding as an operand; the `Reject` dichotomy replaces `Complete`; the `Reject` agreement test | ~1500 | 3, 4 |
| 7 | T3 tail: letrec groups (owner decision 5), unit value, `Float`, `float(e)`, rest patterns (the printer cannot write a restrict; stays `core_roundtrip.rs`) | ~700 | 6 |
| 8 | the executable parser `parse_fuel` with soundness, extracted and compared to `interp.rs`; the recovery agreement test; README, ADR 0030 and 0037 close-out; `GoatAssumptions.v` | ~900 | 1 to 7 |
| 9 (blocked) | `foreign` and the type syntax | ~350 | phase 6b of #435 |

Total about 8900 lines for stages 1 to 8, roughly twice the phase 3 to 6
parser-side work together. Orderings: 1, 3 are independent and can run in
parallel; 2 follows 1; 4 follows 3; 5 and 6 follow 4; 7 and 8 last. Stage 8's
executable parser can start earlier (it needs only the generated grammar) if a
second engineer is free, but its comparison test is most useful once the fragment
is the full grammar.

## 9. Owner questions

The plan changes no language semantics: B for `and`/`or`/`not`/`-` keeps the
language as the checker has it, and the `Reject` dichotomy describes what
lowering already refuses. Three points are yours.

1. **Are the Unicode identifier tables a trusted parameter?** Section 2.8. Today
   an identifier is any Unicode XID name (`unicode_ident`). The model cannot
   reproduce the tables, so it takes `is_xid_start`/`is_xid_continue` as
   parameters listed in the assumptions file and checks them in the differential
   test. The alternative is restricting identifiers to ASCII, which the
   proofs prefer and which changes what a name can be. Recommendation: the
   parameter.
2. **Is the lexer tied to the Rust by differential test only?** ADR 0030 and ADR
   0037 decision 6 take that stance for W; this note applies it to the lexer and
   (D3) the parser interpreter. The alternative, verifying `lexer.rs` itself, has
   no tool for Rust of this size. This asks you to confirm the extension, since
   decision 4 of 2026-11-15 said "verified" without saying how it is tied.
3. **How far does T3 go?** The T3 parts of stages 4 and 7 are about 1000 of the
   ~8900 lines and make the printer a mirror of the whole printable language.
   T1 and T2 carry the soundness link (what parses is what is proved sound); T3
   guards the printer, which has one consumer, `core_roundtrip.rs`. The formatter
   does not print an AST (section 4). If no consumer of an AST printer is
   planned (refactoring, codegen), the plan can stop T3 at the operators stage
   and drop stage 7, saving ~1000. Recommendation: keep T3 through tags, drop
   the letrec tail only if the owner prefers; decision 5 of 2026-11-15 already
   put it last.

## 10. Risks

- **Stage 4's size.** The declaration table, two passes, prelude parameter, and
  new arms of `gen` and `Complete` per rule are new proof structure; phase 3's
  precedent is the calculus half only. If it overruns, split declarations
  (`tag_decl`, construction) from `match` and lists.
- **Block placement by free variables** (stage 6) changes `Den` from a purely
  syntax-directed relation to one that computes `fv` of the denoted term. The
  `lc` side of T1 must carry through it. The fallback is to leave a function
  after a value binding outside the fragment, which is the status quo the owner
  accepted (decision 6).
- **Lowering moves.** The `Reject` set and each derived reading are copies of
  lowering's behaviour; a change to `lower.rs` without the evidence test breaking
  would leave the proof describing an old pass. The proof gate fires on
  `lower.rs`, which is the mitigation, and each stage adds its generator cases.
- **Unicode.** If the differential test finds the Coq lexer and `unicode_ident`
  disagree on a code point the parameter assumption is false; the test uses
  every identifier in the corpus and a sweep of code points, not a proof.
- **Ordered-choice commitments.** The grammar notes a choice "commits to an
  alternative that supplies a MISSING node instead of failing" under recovery.
  That is invisible to the generated grammar, so D3's agreement test is the only
  guard that the two interpreters resolve valid input alike.
