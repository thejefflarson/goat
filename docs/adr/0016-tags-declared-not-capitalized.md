# ADR 0016 — Tags are declared, not capitalized; a `tag` declaration is a closed variant type

- Status: accepted (2026-11-07)
- Context: language design for user-defined variants, `docs/plan.md`
  ("Variants are structural and inferred — no declarations"; "named types are
  an advanced tier … kids never write type declarations"), ADR 0010 (first-use
  variant layout families), ADR 0015 (the host vocabulary in `checker/src/vocab.rs`).
  Supersedes the lexical rule that an uppercase-initial identifier *is* a tag
  (`parser/src/grammar.pest`). Decided with the owner over a long design
  conversation. This is a one-way syntax door: it changes how tags are written
  in every program.

## Context

Today a variant tag springs into existence purely from **capitalization** — an
uppercase-initial identifier is a tag, a lowercase one is a variable, decided in
the lexer with no declaration. Two problems with that for a language aimed at
kids:

1. **Capitalization is invisible, load-bearing magic.** `color` and `Color` mean
   entirely different things, and a miscapitalization silently flips meaning with
   no safety net — you can match on a tag you never defined and can't define.
2. **There is no way to get exhaustive `match`.** The checker already has the
   machinery — a *closed* variant row (a `Row` with an `Empty` tail) and
   `close_match` (`checker/src/infer.rs`), which errors "match doesn't handle X"
   on an uncovered closed-row tag, and which the ADR-0015 host contract relies on
   today — but a user has no way to *declare a closed set*, so their matches stay
   over open rows and always need an `else`.

The owner wants: tags you **declare** (not conjure by capitalizing), and
**exhaustive matching**. Those two converge on one feature.

## Decision

### 1. Tags are introduced by declaration, not by capitalization

A name is a tag **iff** a `tag` declaration (user-written or a compiler-provided
built-in) is in scope. Capitalization becomes **pure style** — `up` and `Up` are
equally valid names, and either can be a tag (if declared) or a variable (if
bound). The lexical case split is removed; `ident` and `tag_name` merge into one
`name` lexeme.

Tag-vs-variable is resolved in `lower`, not the grammar (the grammar gets
*simpler*):
- A `match` **pattern head is always a tag** (goat patterns never bind a bare
  variable — binders live only inside the payload parens), so there is no
  ambiguity there; an undeclared pattern tag is a spanned **"unknown tag"** error.
- A bare `Name` in expression position resolves by precedence: a local binding →
  variable (a binding shadows a tag); else a declared tag → nullary tag; else a
  builtin; else the existing "unknown name" error (with a "did you mean the tag
  `…`?" hint when close).
- `Name(args)` resolves to a **tag construction** iff `Name` is a declared tag
  (and not locally bound), else an ordinary function application — which is why
  `Other(s)` and a call share one syntax, disambiguated by the declaration.

A miscapitalized or misspelled tag (`Dwon` with no `tag Dwon` in scope) is thus a
catchable checker error — the safety net the old lexical rule could never give.

### 2. A `tag` declaration groups tags into a closed variant type

```
tag Red | Green | Blue                              # flat set; name optional
tag Num(n) | Word(s) | Items(xs)                    # payload-carrying cases
tag Tree = Leaf | Node({left: Tree, right: Tree})   # named — referenced in the payload
```

The `|`-separated declaration **closes** the set, and each tag is **bound** to
its group. Constructing a tag therefore yields that *closed* type (not an open
row), so a `match` over it is checked **exhaustive with no annotation** — a
missing arm is the existing `close_match` error; `else` stays optional. A tag
belongs to **exactly one group**. The **name is optional**: omit it for a flat
set, give it (`tag Name = …`) when something must refer back — today that means
**recursion**, and tomorrow type annotations if we ever add them.

This is spelled as *tags* and is deliberately **not** the deferred "named type /
annotation" tier: the closedness rides in on the declaration, so no annotation
syntax is needed at a match site.

### 3. Recursive groups reuse the existing μ-types

`tag Tree = Leaf | Node({left: Tree, right: Tree})` resolves to a `Ty::Rec`
subject to the existing contractiveness rule (a cycle must cross a variant tag) —
the same machinery lists already ride (`Empty | Link(item, rest)`). No new
recursion machinery.

### 4. Literal patterns on scalars

`match` gains literal patterns for the scalar types:

```
match cmd do  "go" then …   "stop" then …   else …  done
match n   do  0 then …      1 then …        else …  done
```

A literal-pattern match is value-matching over the scrutinee's single scalar type
and **always requires an `else`** — number/string domains are infinite, so it can
never be exhaustive (bool, being finite, is the one exception). Orthogonal to the
tag work. `match` still operates on **one** type: all arms are patterns for the
scrutinee's single type (variant tags of one group, or scalar literals, or list
patterns) — never a blend of base types.

## Consequences

- The capitalization magic is gone; a tag typo is a checker error; and users can
  declare their own closed variants and get exhaustive `match` — all three of the
  owner's wants, with one small surface (`tag`).
- Structural rows, parametric polymorphism, and row polymorphism are **unchanged**
  underneath; a closed variant is `Ty::Variant(closed row)`, exactly what
  `close_match` and the ADR-0015 contract already feed mono, so ADR-0010 layout
  families and codegen need no change. "Errors come only from the checker" holds:
  every new failure (unknown/duplicate tag, non-exhaustive match, bad payload) is
  a spanned front-end diagnostic; mono/MIR/codegen see only well-typed closed
  variants.
- **Breaking, pervasive migration (the one-way door):** every tag site is
  affected. The `[]`/`[x, ...xs]` list sugar desugars to `Empty`/`Link`, so those
  get built-in `tag` declarations in the prelude; the ADR-0015 host-vocabulary tag
  *names* (`Tick`, `KeyDown`, `Up`/`Down`/…, `Polyline`, `Line`, …) are injected as
  built-in tag declarations sourced from `vocab.rs` so it stays the single source
  of truth for their payload types and the contract (this is **not** the deferred
  "move the host vocab into the prelude" — only the names become resolvable).
  Examples and test fixtures that use their own ad-hoc tags each gain a `tag` decl.

### Deliberately deferred (reversible / later tiers)

- **Generic / parameterized named types** (`tag Box(a) = …`) — v1 named groups are
  monomorphic; the roadmap's future payoff of this tier.
- **Nested patterns** (`KeyDown(Up)`, `Tick(0)`, `Node({left: Leaf})`) — matching a
  payload's value/sub-tag in the same arm; today you nest a second `match`. A
  natural follow-on (nested patterns + nested exhaustiveness).
- **Type annotations** (`program(c: Color) do …`) — not needed for v1 because
  closedness flows from the declaration; the optional group name is the hook if we
  ever add them.
- **Moving the host vocabulary into a goat prelude** — amends ADR 0015; separable
  follow-on. v1 only makes the vocab tag *names* declared.
