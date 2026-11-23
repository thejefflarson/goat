# ADR 0030 — The parser is verified for the core fragment only, over a trusted token stream

- Status: accepted (2026-11-11)
- Supersedes: ADR 0022 §7 ("we do not propose a verified parser … a tar pit").
- Context: ADR 0008 (the Coq development proves the type system over the
  locally-nameless core in `proofs/goat_ln.ott`), ADR 0022 (the grammar is the
  data `grammar/goat.peg`, interpreted by `parser/src/interp.rs`), and
  `docs/semantics.md` §10 (the n-ary surface forms are the k-fold iteration of
  the curried core).

## Context

ADR 0022 §7 declined to verify the parser, because a mechanized grammar for all
of goat buys the three parser requirements nothing. That judgement holds for the
whole language. It does not hold for the small fragment the proofs already
model: the proof's statements start at abstract syntax, so the distance between
source text and the term the proof talks about is unchecked trust. A verified
parser for just that fragment closes the distance where it matters and stays
small enough to finish.

## Decision

1. **The claim covers the core fragment only.** That is what `goat_ln.ott` has: a
   variable, a number, `true` and `false`, `program(x1, …, xk) do e done` with at
   least one parameter, a call `e(e1, …, ek)`, a binding `x = e1 e2`, a record
   literal `{l: e, …}`, a field access `e.l`, a dot call `x.l(e1, …, ek)` on a
   variable receiver `x` (ADR 0031: it denotes `(x.l)(x, e1, …, ek)`), and
   a take `e::l` (ADR 0034: it denotes the projection `e.l`, so `e::l(e1, …, ek)` denotes
   `(e.l)(e1, …, ek)`), and parentheses. A dot call on any other receiver is outside the fragment, and
   so is a call with no argument. The n-ary forms
   are curried into the single-binder core, and field labels are interned to
   `nat` in first-occurrence order of the source text. `program()` with no
   parameter is excluded.
2. **The input is a trusted token stream.** The lexer is outside the claim, so
   nothing is said about how characters become tokens (identifiers, numbers,
   comments, the reserved words).
3. **Three claims, over the fragment.**
   - **T1.** Every parse of a core-fragment token stream denotes a term of
     `lc_exp`.
   - **T2.** The PEG parsing relation is deterministic: a token stream has at
     most one parse.
   - **T3.** Printing any core term and parsing the result gives back the same
     term.
4. **The grammar enters Coq by generation from `grammar/goat.peg`**, never by
   hand transcription. A transcribed copy is a second grammar that can drift
   from the one the parser runs; a generated one cannot.
5. **Everything outside the fragment is unverified.** `if`, `match`, tags, lists,
   operators, strings, loops, destructuring and `foreign` stay out. Widening the
   claim to any of them requires widening the soundness proof over `lc_exp`
   first; a parser claim cannot be larger than the language the proof knows.
   The Rust lowering (`checker/src/lower.rs`) and error recovery
   (`parser/src/interp.rs` `parse_recovering`) are not verified.
6. **The Rust side keeps the claim honest in the meantime.**
   - `parser/tests/rule_map.rs` classifies every rule of `goat.peg` as
     `core(<Ott production>)` or outside the core, and fails when a rule is
     missing from the map, when the map names a rule that no longer exists, or
     when it names a production `goat_ln.ott` lacks.
   - `checker/tests/core_roundtrip.rs` prints 10,000 generated core terms (fixed
     seed) as goat source in two styles, curried and grouped, parses and lowers
     them with the real front end, and checks the lowered HIR reads back as the
     same term. Its printer holds the parenthesisation rules the Coq printer
     mirrors.

## Amendment: phase 1 of the proof coverage (ADR 0037)

The fragment now also holds:
- a string literal (the lexer is trusted, so the token carries no bytes and the
  string denotes `q` for every `q`);
- `if c then a else b done`, with the `else`;
- one binary operator between two operands (`+ - * / // %` and `== != < <= > >=`),
  where an operand is a chain, so a nested operation or a binding is
  parenthesised. A run of two operators is outside the fragment: its precedence
  is resolved by lowering (ADR 0013) and the model does not resolve it. A dot
  call inside an expression with an operator is also outside it.

Still outside (at this amendment; the one below brings in an `if` without an
`else` and `Float` literals): `and`, `or`, `not`, unary minus, an `if` without an
`else` (lowering supplies the `()`), and the unit value, which has no literal. T3
covers the printable core: `scoped` is false for the unit value, for a `Float`
value and for `float(e)`. The coercion `float(e)` has no surface syntax: elaboration
inserts it, so no source text parses to it and the Rust round-trip cannot print
it; `parser/tests/rule_map.rs` exempts it for that reason. The Rust round-trip
test and the printer table (`checker/tests/core_roundtrip.rs`) generate strings,
`if`, and every operator alongside the old core, so each form the Coq printer
writes has a Rust counterpart.

## Amendment: phases 1 and 2 of the proof coverage (#457)

The fragment now also holds:
- a `Float` literal: a decimal NUMBER token (`TDec`) denotes the opaque `e_dec`.
  The lexer is still trusted, so the token carries the part before the point and
  the claim says nothing about which decimal text a payload stands for;
- an `if` without an `else`, which denotes `if c then a else unit`;
- a block's leading function bindings as one recursive group. A declaration
  whose value is exactly a `program(...)` literal is a member (the parse tree
  shape `Node R_value [Node R_function _]`); a parenthesised function is a value.
  `f1 = program(...) ... fn = program(...) rest` denotes
  `letrec x = {0: e1, ..., n-1: en} rest'`, where the group name `x` is one binder
  and each occurrence of a member's name in the members and `rest` is the
  projection of that member, labelled by its position. Value bindings still denote
  the non-recursive `let`.

Outside, deliberately: a function binding after a value binding in the same block
(the group would have to be placed after the values its members read, which
needs name resolution), and a function binding that is an operand of an
expression. `Complete` excludes both. A run of two operators stays outside: its
precedence is lowering's (ADR 0013), and `and`, `or`, `not` and unary minus are
not in the calculus.

Decided (owner, on #457): the lexer stays trusted until phases 3 to 6 land and is
then verified once; T3 for `letrec` is deferred to the tail of phase 8; the
exclusion of a function binding after a value binding stands.

Amended (phase 8, stage 1): decision 2 no longer holds. `proofs/GoatLex.v` models
the lexer as a function `lex` from source text (a list of Unicode code points) to
tokens, and `proofs/GoatLexText.v` restates T1 over text: a source that `lex`
turns into a token stream the PEG parses denotes a locally closed term
(`parse_text_denotes`). "Verified" means a Coq model tied to `parser::lexer` by a
differential test, as the inference algorithm is (ADR 0037, decision 6): `lex` is
extracted, and `make -C proofs differential` compares its tokens with
`parser::lexer::lex`, kind and span, on every `.goat` file of the repo, every
program the corpus generators write and a fixed-seed fuzz of lexer fragments. The
model rests on one declared parameter pair, `xid_start_hi` and `xid_cont_hi`:
whether a code point of 128 or more may start or continue an identifier. They
stand for the tables of `unicode_ident`, which the Coq development does not copy;
the differential test feeds the extracted `lex` the Rust tables and compares.
ASCII is decided inside the model. The Rust lexer itself is not verified, and a
source is a list of code points, so UTF-8 decoding is the host's.

T1 covers all of this. T3 covers `Float` literals and the `if` without an
`else` (the printer writes `e_ite c a e_unit` without the `else`), and no longer
prints a function as the bare value of a binding: it parenthesises it, because a
bare function is a group member now. T3 does not cover `letrec`: the printer
would have to write a group's projections as bare member names, which means
tracking which binders are groups. `GoatExample.v` instead parses a one-member
group and shows it denotes the term `GoatPhase2.v` types. The Rust round-trip
test generates groups, and checks the lowered let chain names each member where
the text mentions it.

The parser rules still outside the fragment (`parser/tests/rule_map.rs`): `tag_decl`,
`tag_kw`, `group_name`, `tag_case`, `sequel`, `and_op`, `or_op`, `not_op`,
`negation`, `spread`, `foreign_kw`, `foreign_decl`, `foreign_name`, `fn_type`,
`_type_expr`, `list_type`, `record_type`, `field_type`, `type_name`,
`destructure`, `record_pattern`, `list_pattern`, `rest_binding`, `list`,
`match_expr`, `arm`, `pattern`, `labels`, `literal_pattern`, `repeat_loop`,
`count_loop`, `each_loop`, `for_kw`, `from_kw`, `to_kw`, `in_kw`. They belong to
phases 3 to 6 (tags, variants, `match`, lists, spread, loops, destructuring,
`foreign`) and to constructs outside the numbered phases (`and`, `or`, `not`,
unary minus, statement sequencing with `;`).

## Amendment: phase 8 close-out (#457)

The core fragment is now the whole grammar except `foreign` declarations and the
structured type syntax (`foreign_kw`, `foreign_decl`, `foreign_name`, `fn_type`,
`list_type`, `record_type`, `field_type`), which wait for phase 6b of #435: the
calculus has no foreign constant. The amendments above
list what each stage added; this one records the final claim.

- **T1 is a dichotomy over text.** For a source that `lex` turns into a token
  stream the PEG parses, the tree either is one lowering reports (`Reject`) or
  denotes a locally closed term. `Reject` is a record whose spread is not first or
  that has a second, and a `match` whose arms mix tag, literal and list patterns;
  each is a diagnostic in `lower.rs`, and `checker/tests/core_roundtrip.rs` checks
  that lowering reports them and accepts the one-kind and spread-first forms. What
  remains outside `Reject` and outside `Den` (`Complete`) is valid goat the model
  does not read: a record pattern as a parameter, a payload type with no slot
  code, a `match` with no arm, and literal arms with no `else`.
- **A block that ends in a binding is the value of that binding.** `x = 1` is the
  number `1`, because that is what lowering and the checker do (the checker gives
  such a program the type of the binding; the type differential found it). A block
  that ends in `a;` is the unit value, and so is an empty program or body.
- **The parser has an executable form.** `parse_fuel` (`proofs/GoatPegExec.v`) is a
  fuel-bounded interpreter of the generated grammar and `pf_sound` says what it
  returns the relation derives. It is extracted and compared, tree for tree, with
  `parser::interp::parse` by `make differential`, which ties the Rust
  interpreter's ordered choice, repetition and end-of-input handling to the
  relation. Recovery stays outside the claim: a Rust test holds that on valid
  input `parse_recovering` returns `parse`'s tree with no diagnostic.
- **Decisions 2 and 5 no longer hold,** apart from the rules above. The lexer is verified in the sense of the stage 1 amendment, with
  `xid_start_hi` and `xid_cont_hi` the only parameters (`GoatAssumptions.v` lists
  them last).
- **Open.** The checker types a function group by shared type variables, so a
  member that no mention links to the rest of its run is typed alone where `Den`
  places the whole least prefix as one `letrec` (`proofs/README.md`, the block
  bullet). A forward mention across a value binding stays a free name in `Den`.
  Neither affects T1.

## Consequences

- The real parser and lowering disagreed with the Ott core in three places. They
  are findings, not bugs the fragment hides, and each is pinned by a test in
  `checker/tests/core_roundtrip.rs`. The first two are now modelled (see the
  amendment above: the group is `letrec`, and a parenthesised function is the
  plain `let`); the tests pin the lowering side:
  - **A function binding is recursive** (ADR 0003): in `x = program(y) do x done; x`
    the inner `x` is the binding itself. The Ott `let` binds `x` in `e2` only. The
    fragment's `let` is non-recursive, so the verified claim must either take the
    ADR 0003 rule for a `program`-valued binding or exclude self-reference.
  - **Functions of one block form a group** (ADR 0003): in
    `g = 1; f = program(y) do g done; g = program(z) do z done; f` the `g` in `f`
    reads the later function. In the Ott `let` it reads the earlier value.
  - **Duplicate record labels** are legal in the Ott core ("duplicates allowed")
    but are a lowering error (`{a: 1, a: 1}`). Likewise `program(x, x)` is a
    lowering error while the curried `program(x) do program(x) do e done done`
    is not.
  The generator avoids the three (unique names for function bindings, distinct
  labels per record, no duplicate parameter in one group). **Decided:**
  `proofs/goat_ln.ott` is not changed, and the three are hypotheses of neither
  T1 nor T3. T1 holds without them because closing a variable yields a locally
  closed term whatever names repeat. T3 holds without them because the printer
  names each binder by its depth, so no name repeats and no binding refers to
  itself, and `Den` reads a binding as the non-recursive Ott `let`. The three
  concern how the Rust front end reads text, and
  `checker/tests/core_roundtrip.rs` covers them.
- T3 (`print_parse_roundtrip`, `proofs/GoatRoundtrip.v`) needs one hypothesis
  beyond a closed term: `Interned`, that the term's labels are numbered by
  first occurrence in the printed text. It covers the curried printer style and
  closed terms only. The grouped style (`program(x, y)`, `f(a, b)`) and terms
  with free variables are not covered.
- T1 to T3 say nothing about the Rust interpreter: they are facts about the
  generated grammar. Connecting the two stays a testing argument (the rule map
  and the round-trip test), not a proof.
- A call on a non-identifier (`1(2)`) and a number as field base (`(1).a`) lower
  fine; rejecting them is the checker's job.
- Adding a grammar rule now forces a classification decision in review, which is
  the point.
