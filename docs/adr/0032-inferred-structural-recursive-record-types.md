# ADR 0032 — Methods on any receiver: infer guarded structural recursive record types

- Status: proposed (2026-11-11). Recommendation: **accept**, with the work list
  in "What is left" below.
- Context: ADR 0010 (mono layout identity), ADR 0027 (rank-1 inference, value
  restriction), ADR 0028 (pure-extension spread recursion is rejected), ADR 0030
  (the verified core fragment), ADR 0031 item 7 (methods on a fixed-type
  receiver stay rejected until a spike measures the structural route). Spike
  branch, not for merging: `spike/390-structural-recursive-types`.

## Context

ADR 0031 makes `r.f(a)` mean `(r.f)(r, a)`. That works when `r` is a record
bound with `=` whose fields are values, because ADR 0027 generalizes it. It
fails for every receiver with one fixed type: a parameter, a call result, a
spread copy, an `if` or `match` result. The owner states the requirement: a kid
will write

```
f = program(x) do x.do_thing(); x.do_another(5) done
```

and it must work, with no type declaration. Written out the way master reads
it today (the receiver passed explicitly), that program is
`x.do_thing(x); x.do_another(x, 5)`.

Inside `f`, `x` has one type. `x.do_another(x, 5)` makes the type of the field
`do_another` a function whose first parameter is `x`'s own record type. That
record type contains itself: `P = {do_another: (P, Int) -> … | ρ}`. Today the
occurs check rejects it ("cannot construct the infinite type").

## Decision

Accept **inferred, guarded, equi-recursive record types**, with these rules.

1. **The occurs check ties a knot** instead of failing, when every cycle goes
   through both a record field and a function type (a parameter or the result).
   The result is a `Ty::Rec` (`μt. …`), the same node variants already use.
   `tie_ty_knot` and `tie_row_knot` (`checker/src/infer.rs`) generalize their
   "under a variant payload" test to a `Guard`: a mention is *guarded* if it is
   under a variant payload, or under both a record field and a function type.
2. **These stay rejected**, each with a test:
   - `x(x)` (a cycle through a function type and no record field),
   - `{a: x}` cycles with no function type,
   - ADR 0028's pure-extension spread recursion
     (`go = program(s) do go({...s, stop: true}) done`), whose cycle has no
     function type, and so keeps `spread_regress_message`.
3. **Named types are never required.** The type is inferred; nothing is
   declared.
4. **The guard counts a function *result*, not only a parameter.** The issue
   text says "under a function parameter". The first thing a method does is
   return an updated copy of itself (`moved: program(self) do {...self, x: …}
   done`), so `P = {moved: (P) -> P}`. The second `P` is in result position.
   Restricting the knot to parameters rejects the primary use case. This is a
   deviation from the ticket for the owner to ratify.
5. **Mono** lowers a `μ` over a function or record by reserving its signature
   or layout id before lowering the body (see Evidence, item 2).
6. **`{...v, k: e}` is a syntactic value** (ADR 0027) when `v` and every `e` are
   (see Evidence, item 3). This is independent of the knot and can ship
   separately.

## Evidence

The prototype is on `spike/390-structural-recursive-types`. It adds about 100
lines to the checker's occurs-check helpers and about 70 to mono and canon.

### 1. Receivers: type-check and run through the interpreter and wasm

`cli/tests/structural_recursion.rs` runs each program through the MIR
interpreter and wasmtime, which must print the same lines. All pass.

| receiver | program | result |
| --- | --- | --- |
| the owner's shape | `f = program(x) do x.do_thing(x); x.do_another(x, 5) done` applied to `{n: 10, do_thing: …, do_another: …}` | prints `10`, then `15` |
| parameter | `step = program(p) do p.moved(p) done`, `step(ball).x` | `3` |
| call result | `b2 = ball.moved(ball)`, `b3 = b2.moved(b2)` | `5` |
| spread copy | `c = {...ball, speed: 5}`, `c.moved(c).x` | `6` |
| update loop | `run = program(m, n) do if n == 0 then m.draw(m) else run(m.update(m), n - 1) done done` | `12` |

where `ball = {x: 1, speed: 2, moved: program(self) do {...self, x: self.x + self.speed} done}`.

Known hole: `m = run(init(), 4)` followed by `m.draw(m)`, where `run` returns
its accumulator and `m` has two methods, is rejected with the generic "cannot
construct an infinite record type". Cause: `tie_row_knot` replaces only the
mentions whose row *prefix* equals the first one it finds. `update` returns
`{...self, x: …}`, a record with prefix `[x, x | ρ]`, while `draw` takes
`{x | ρ}`. Two mentions of one row variable with different prefixes need
simultaneous knots. The construction exists (nest the `μ`s, Bekić-style, one
binder per distinct mention, `n!` copies in the worst case, `n` is the number of
distinct prefixes and is 2 or 3 in practice), but the prototype does not build
it. It is the first item under "What is left". A mention under an enclosing `μ`
binder also carries the binder as a free variable in its prefix, so the
construction must unfold it first.

### 2. Mono and layout identity (ADR 0010)

`lower_ty` overflowed the stack: lowering a `μ` unfolds its head, and the
unfolded head contains the same `μ` again. The fix is three small parts:

- `lower_rec` keys each type that contains a `μ` over a function or record by
  its `canonical` form (`canon.rs` already computes the minimal automaton of a
  recursive type, which handles records and functions as it does variants), and
  reserves a signature id or a layout id *before* lowering the body, so the
  back edge finds the id. Both ends of the cycle get an id this way: the
  function and the record are separate nodes of one cycle, and entering from
  either one must give the same two ids. (A first attempt that keyed only the
  `μ` node produced two isomorphic copies, `Closure(0)` against `Closure(1)`,
  and the MIR verifier rejected the program.)
- A `μ` whose cycle passes through a variant keeps its old path
  (`variant_layout`). `loops_without_variant` tells them apart; without it, the
  existing recursive-list and tree programs took the new path and failed
  verification (8 failures in the first full run).
- `specialize_body` unfolds a lambda's recorded type before matching `Func`.

Layout identity: a `μ` record's layout is the canonical form's id, so two
types that denote the same infinite tree share one layout, and an unrolled
copy does too. Two *different* trees (`{moved, x}` against `{moved, x, speed}`)
get different layouts, as ADR 0010 requires for different field sets. The
reserved layout is not deduplicated against a structurally equal
non-recursive layout, which cannot exist: a layout with a cycle through its own
closure field is never equal to an acyclic one.

### 3. `{...v, x: 5}` as a syntactic value

Adding `Spread` to `is_syntactic_value` (a spread of a value base with value
fields) generalizes the copy. Measured on the prototype:

| program | master | prototype |
| --- | --- | --- |
| `b = {id: program(v) do v done, n: 1}`, `a = {...b, k: 5}`, `a.id(1)`, `a.id(true)` | type error: expected `Number`, found `Bool` | prints `1`, `true` |
| `a = {...b, n: 7}`, `c = {...a, k: 5}`, `c.id(2)`, `c.id("s")` | type error | prints `2`, `s` |

Mono re-lowers a generalized value at each use's ground type, so each use gets
its own layout; the spread is pure (it copies fields), so ADR 0027's
once-evaluated-value hazard does not apply. The knot does not need this: `c =
{...ball, speed: 5}; c.moved(c)` works with `c` monomorphic. So this is a
separate, small ergonomic decision. Recommend accepting it, in its own PR.

### 4. Error quality

Programs and exact messages on the prototype (`p.moved` and friends are
generalized `step` functions, so messages point at the call of `step`, not at
the method call):

```
# missing method
step = program(p) do p.moved(p) done
print(step({x: 1}))
2:7: record is missing field `moved`

# misspelled field inside a method
ball = {x: 1, moved: program(self) do {...self, x: self.xx + 1} done}
3:7: record is missing field `xx`           # points at step(ball)

# extra argument (the dot-call arity typo, spelled out)
step = program(p) do p.moved(p, p) done
3:7: function expects 1 argument(s) but got 2

# method returning the wrong shape
step = program(p) do q = p.moved(p); q.moved(q) done
ball = {x: 1, moved: program(self) do self.x done}
3:7: type mismatch: expected `{moved: μt464. ({moved: t464 | t461}) -> t462 | t461}`, found `Number`
```

Only the last leaks a `μt…` type and raw type-variable names. The fix is in
the type printer, not the unifier: print a `μ` node as `…` at its back edge
and name the record by the fields the program read (`{moved: …}`), and map the
mismatch to "the method `moved` returns a number, but it is called again with
that result". The spans are the second problem: because `step` is generalized
first and unified with `ball` at the call, the error points at the call of
`step`. That is the same limitation as every higher-order error today. The
messages of the dot-call work (#386) are not on master yet, so the comparison
the ticket asks for is deferred to when they land.

### 5. The Coq boundary

`proofs/goat_ln.ott` has `typ ::= Number | Bool | (T) -> T | {R} | a` and rows;
no `μ`, no variants, no tags. Like recursive variants, `μ` records are outside
the ADR 0030 fragment, and the claim does not need to widen for goat to ship
this: the parser claim (T1–T3) is about syntax, and `GoatSound`'s statement is
about the core language.

To widen, two routes:

- **Iso-recursive** (recommended if it is ever done). Add `mu a. T` to `typ`
  and `fold`/`unfold` to `exp` as erasable coercions, with
  `unfold : (mu a. T) -> T[a := mu a. T]`. The checker would have to elaborate
  its implicit steps to explicit ones, so the new proof obligation is that
  elaboration (the Rust checker is not verified, so the claim would be about
  the declarative system). Preservation and progress get two easy cases because
  the coercions erase at runtime. `typ` has no binder today (type variables are
  named atoms with substitution, ADR 0008), so `mu` needs a named-binder
  substitution lemma.
- **Equi-recursive.** Type equality becomes coinductive bisimilarity of regular
  trees, `GoatMeta`'s inversion lemmas (canonical forms, projection) must be
  restated up to that relation, and `GoatHM`'s unification soundness needs
  Huet-style unification of regular trees in place of first-order unification.
  This matches the Rust implementation (canonical forms and `assumed` pairs in
  `unify_ty`), but it is a much larger re-proof than the iso route.

Neither is needed now. The ADR 0030 position stays: the proofs cover what
`goat_ln.ott` models, and ADR 0028's reason for not widening records (a
near-total Coq re-model) does not apply here because this is a type-only
addition guarded by a syntactic criterion.

### 6. Compile cost against master

Two measurements, both on a loaded machine, so read them as "no difference
visible", not as precise ratios:

- `goat build` (check, mono, wasm) over the 25 programs in `examples/`, five
  passes, release binaries: master 1.82 s and 1.45 s in two runs, prototype
  2.24 s and 1.46 s. Process start-up dominates; none of the examples contains a
  `μ` record, and the new code runs only on an occurs-check failure (checker)
  or on a type that contains a `μ` (mono).
- `checker/tests/scale.rs` (the linear-scaling assertions) passes unchanged in
  the prototype's full run: 1500 tests passed, 0 failed.

One cost to watch: mono now calls `has_structural_rec` on every function and
record type it lowers, which walks the type, so lowering a deeply nested
non-recursive record is quadratic in its depth. It did not show on the
examples; if it shows, cache the answer per lowered type.

## What is left to accept it

1. **Multi-mention knots.** Build the nested-`μ` construction for several
   distinct prefixes and unfold enclosing binders first; makes the
   `m = run(init(), 4); m.draw(m)` shape check. Without this, a kid hits the
   generic "infinite record type" message on a natural program.
2. **Error rendering.** Never print a `μ` or a bare type variable; describe the
   receiver by the methods the program used. Also give the knot-failure case a
   dot-call message.
3. **Tests that pin the guard.** A cycle through a record field and a function
   type, a cycle through only one, and the pure-extension spread, all in
   `checker/tests/structural_recursion.rs` on the spike branch; these port as
   they are.
4. **Mono.** Port `lower_rec`, `loops_without_variant` and the `specialize_body`
   unfolding, plus tests that the existing recursive-variant programs keep their
   layouts. Check every site that matches `Ty::Func` on a ground type for an
   unfold (the spike found one; `print_value` and the float-parameter probe
   already unfold).
5. **Decide the proof route** (iso or none) before the next Coq phase, not now.

## Consequences

- ADR 0028's rule that records are never recursive is amended: a record may be
  recursive when the cycle passes through a record field and a function type.
  The pure-extension spread rejection is unchanged because that cycle has no
  function type.
- ADR 0031 item 7 is superseded once this is accepted: methods work on a
  parameter, a call result and a spread copy, and the targeted infinite-type
  message becomes a fallback for the multi-mention hole only.
- `μ` can now appear in more types the checker prints, so item 2 above is
  required before this is user-visible.
- Unification, mono and canonicalization already handle `μ` for variants, so no
  new type constructor enters the pipeline.
