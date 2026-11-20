# Closed tags: design pass

Refs #500. Owner decision of 2026-11-20 (#452 Q3): every tag is closed. A lone
`tag Ping` becomes a group of one, and lists become a built-in closed recursive
group. This is a design pass only. No semantics or wording question is decided
here; section 4 lists each one with options and a recommendation for the owner.

Measurements below use `goat check` on small programs at `425a26a`. "Spike"
means a scratch edit of the checker, run against the full suite and reverted;
none of it is in this branch.

## 1. Current behaviour

A tag is either **lone** (`tag Ping`: no group, no payload type) or in a
**group** (`tag Light = Red | Green`, or any declaration with a `|`, a name, or
a payload type). Constructing a lone tag gives an open row `[Ping: t | ρ]`;
constructing a grouped tag gives the group's closed type. The prelude's
`Empty`, `Link`, `DictLeaf`, `DictNode`, `Found`, `Missing` are lone, and so are
the host's event and shape tags (`Tick`, `KeyDown`, `Circle`, `Line`, ...). Only
the host's `Key` is a group.

| Program | Result today |
|---|---|
| `tag Ping` `tag Pong` `x = if true then Ping else Pong done` | accepted; only the warning "tag `Ping` is constructed but never matched anywhere" (the two rows merge into `[Ping, Pong \| ρ]`) |
| `tag Stop` `x = if true then [1, 2] else Stop done` | accepted; the same warning for `Stop` |
| `xs = [1, "a"]` | accepted (`[Link: {0: Number, 1: [Link: {0: String, ...}]}]`) |
| `xs = [1, "a"]` `length(xs)` | error at the use: `type mismatch: expected Number, found String`, with the note "...and the list meets here" |
| `[Ping, 1]` (unused) | accepted |
| `Link(1, 2)` | accepted; type `[Link: {0: Number, 1: Number} \| t]` |
| `[[2, "b"], [1, "z"]]` | accepted (the inner lists are never forced); `docs/llm.md:414` relies on it |
| `f = program(p) do match p do Ping then 1 done done` `f(Ping)` | accepted; a lone tag needs no `else` because the row is closed at the match |
| the same `f` with `else 2`, then `f([1])` | error: `the tag Link is not allowed here; the other side never has it` |
| the same `f` with `else 2`, then `f(Pong)` | accepted: with an `else`, the parameter stays an open row, so it takes any tag |
| `tag Light = Red \| Green` `f = ... match l do Red then 1 done` `f(Green)` | error at the call: `the tag Green is not allowed here; the other side never has it` |
| `tag Light = Red \| Green` `x = if true then Red else [1] done` | error: `the tag Link is not allowed here` |
| `[a, b] = [3, 4]` | accepted (the literal's row is exactly known) |
| `[1] + [2]` | error: `` `+` needs numbers or records of numbers `` |

How a group's payload types are declared, which matters for the lists question:
**they are written in the declaration, as concrete names, and are not inferred.**
`payload_ty` in `checker/src/lower.rs` accepts `Number`, `Int`, `Bool`, `Unit`,
`String`, a record type of those, or the group's own name. Anything else is a
spanned error ("a tag payload can't be `n` yet"), so the `tag Num(n) | Word(s)`
in the ticket text is rejected today. ADR 0016 defers generic named types
(`tag Box(a) = ...`). So **a closed group cannot carry a type-varying payload
today**, and a lone tag only gets one because it is not a group.

Mechanics, for later sections:

- `Group { tags: Vec<(String, Ty)>, recursive }` (`checker/src/ty.rs`).
  `Group::instantiate(binder)` builds `μbinder. [tags]` with `Group::SELF`
  replaced by the binder. `construct_grouped` (`infer.rs`) instantiates at each
  construction and unifies the payload with the declared one. Two instances of
  a recursive group unify through `unify_ty`'s `Ty::Rec` case (unfold, with the
  `assumed` set to end the cycle), so each construction has its own binder.
- A list is already *consumed* as a closed type: `length : (μt. [Empty, Link:
  {0: a, 1: t}]) -> Number`. Only the *constructors* are open
  (`[Empty | t]`, `[Link: {...} | t]`). The host vocabulary already builds the
  closed list type in `vocab.rs::list`.
- List-specific code: `kinds.rs::is_list_tag` (used by the `Appendable`
  constraint and `constrain_list`), `infer.rs::is_list_of_variants` (the check
  that `draw` returns a list of shapes), `mark_element` (the "list meets here"
  note), `lower.rs::lower_list`, `query.rs::LIST_TAGS` (editor tag lists), and
  in mono `canon.rs`, `mono/reload.rs`, `mono/interactive.rs`,
  `mono/structural.rs` (all recognise the list by the names `Empty` and `Link`).

## 2. The design

### 2.1 Lone tag = a group of one, with a per-use payload parameter

A lone tag has no declared payload type, so a group of one needs one that is
not written. The mechanism that gives it one is the same that lets lists carry
any element: a group whose payload mentions a **type parameter**, replaced by a
fresh type variable each time the group is instantiated. A lone tag `Disc` is the
group `[Disc: a]` with `a` fresh at every construction: `Disc(1)` is
`[Disc: Number]` and `Disc("a")` is `[Disc: String]`. Each is closed. They clash
only when something forces them to be one type, as `[1, "a"]` does today.
No annotation is needed anywhere.

Spike: `Group` gained a `PARAM` variable beside `SELF`; `instantiate` took a
second fresh variable; `declare_tags` gave a lone non-prelude tag the payload
`PARAM`. `Disc(1)` and `Disc("a")` both check; `match` on a lone tag needs no
`else`; mixing two lone tags fails (section 2.3).

Where a group has several tags with no declared payload type, each tag would
need its own parameter, and a recursive group like the dictionary
(`DictNode(left, key, value, right, height)`) needs two (key and value) shared
across tags. So the group carries a parameter *list*, not one variable. How a
parameter is introduced is a syntax question for built-ins only, if users never
write parametric groups (decision D1).

### 2.2 Lists = a built-in closed recursive group with one parameter

`μl. [Empty, Link: {0: a, 1: l}]`, which is the type `vocab.rs::list` and every
list consumer already use. Spike: the list group installed from Rust in
`lower_with_vocab` (the prelude's `tag Empty`/`tag Link` removed), `a` the
parameter. Results:

| Program | Spike result |
|---|---|
| `[1, "a"]` | error at the brackets: `type mismatch: expected Number, found String`, spanning the whole `[1, "a"]` |
| `if true then [1, 2] else ["a"] done` | error at `["a"]`, same message |
| `x = [[1], ["a"]]` | error at the outer brackets, same message |
| `Link(1, 2)` | error: ``expected `μa. [Empty, Link: {0: Number, 1: a}]`, found `Number` `` |
| `[]` | `μt0. [Empty, Link: {0: t1, 1: t0}]` (polymorphic: `[]` is a list of anything) |
| `[1, 2]` | `μt6. [Empty, Link: {0: Number, 1: t6}]` |
| `length([1,2,3])`, `f([1]) + f(["a"])` with `f` over any list | accepted |
| `g = ... match xs do [] then 0 done`, then `g([1])` | error: `the tag Link is not allowed here` (partial matches still narrow, see 2.5) |
| the prelude (`change_each`, `sort`, `dict`, ...) | type-checks unchanged |

So the answer to "can a closed group carry a payload whose type varies": yes,
with one parameter per group instantiated fresh at each construction, which
needs no change to unification (two instances of the Rec unify through the
existing unfold-and-assume path; the spike's suite results confirm it).
The element type is not part of the group's *name*, so it does not get a
declaration form; it falls out of unification.

`[1, "a"]` is rejected because `Link(1, Link("a", Empty))` unifies the outer
`Link`'s payload `{0: Number, 1: <inner list>}` with `{0: a, 1: self}`, which
forces the inner list's element to `Number`. **The error span is the whole
bracket today because `lower_list` gives every `Link` the span of the whole
list.** Giving each `Link` its element's span would point at `"a"`, and
`checker/tests/list_elements.rs` (five tests that assert which element is
blamed) would then keep passing. That is an implementation detail, not a wording
choice.

### 2.3 Mixing groups

Two groups never unify: `if c then Ping else Pong done` (each a closed group of
one) fails with `the tag Pong is not allowed here; the other side never has it`
at `Pong` (spike). A list against a lone tag, and a list against a grouped tag,
fail the same way with `Link` or `Empty` named. The message is the existing
closed-row mismatch and does not say that the tags were declared apart. Which
wording to give it is decision D2.

A `match` whose arms name tags of different groups fails today only when it
meets a value, at the *call*, with `the tag Box is expected here, but this
value is never Box` (spike, `area(Disc(2))`). `lower` knows each tag's group, so
the mismatch can instead be reported at the arms, spanned, before inference.
That is decision D4.

### 2.4 Interactions

- **Recursive groups and equi-recursive knots (ADR 0032).** Groups keep using
  `Ty::Rec` with a fresh binder per instantiation. The list stops using the
  inferred knots (`tie_row_knot`, `under_tag`, `plug_row`) because its type
  is a known `Rec` from the start; those knots stay for inferred recursive
  *records*, and for rows narrowed by partial matches (2.5). Nothing in the
  knot code changes. The unfold budgets (`MAX_UNFOLDINGS_PER_UNIFY`,
  `MAX_KNOTS_PER_UNIFY`) are unaffected; a list of lists adds one `Rec` level
  per nesting, as `Tree` already does.
- **Width-polymorphic variant layouts (ADR 0010).** ADR 0010 exists because a
  let-bound open-row value can be matched at two widths. With every user tag
  closed, a value of a group has one type, so the example in the ADR (`s =
  Circle(5)` matched at `[Circle]` and `[Circle, Square]`) is a type error
  (`narrow(s)`: the tag `Square` is not allowed here), exactly as it already is
  for a group (spike). Mono's layout *families* (`Mono::variant_layout`,
  `Mono::agrees`) stay correct and are not touched. They stay needed for host
  event and shape rows (D5) and for rows narrowed by partial matches. Removing
  them is a follow-up, not part of this change.
- **Host vocabulary (ADR 0020).** The vocabulary says its families are closed,
  but `lower` declares event and shape tags as lone (open rows narrowed to the
  tags the program handles), and only `Key` is a group. Whether those families
  become groups is decision D5. The vocabulary's own payload types are concrete,
  so no parameter is involved. The list type in a payload (`Polyline(points)`)
  already uses `vocab.rs::list`, which is the closed form.
- **Structural ordering (ADR 0036).** A tag's rank is its declaration order and
  tags are compared only inside one type. Under closed tags a comparison across
  groups (`Ping < Pong`) is a type error, so ranks matter only within a group.
  The table stays program-wide; the amendment text changes ("a tag declared by
  itself ranks by where it first appears" stops being observable between
  tags). `Empty < Link` is unchanged. Mono's derived compare is unchanged.
- **Reload contract (ADR 0035).** The reload image names tags and walks lists
  by shape (`mono/reload.rs::list` detects `Empty` plus `Link` with positional
  fields). The list type is already closed there, so nothing changes. Two
  consequences: a variant with the shape of a list but a different element
  (`Link(1, "AAA")` built by hand) can no longer be written, so the reload test
  `a_variant_shaped_like_the_list_but_with_a_string_tail_reloads_as_an_ordinary_variant`
  has to be rebuilt around a user group with a list-like shape; and adding a
  second tag to a lone tag changes its type from `[Ping: a]` to `[Ping, Pong]`,
  which reloads as a reshaped type (reset), like any group edit.
- **Naming.** `Empty` and `Link` become reserved tag names of the list group,
  like the host's. Tests that use them as ordinary tags need other names.

### 2.5 What stays open

Two things keep an open row inside the checker even after this change, and the
owner should know they are not removed:

1. A `match` with an `else` leaves the scrutinee as `[Ping: a | ρ]`, which any
   other group unifies with (`f(Pong)` is accepted in the spike). Closing this
   means making every arm pin the scrutinee to the group the arm's tag belongs
   to (decision D3).
2. A `match` with no `else` narrows the scrutinee to exactly the tags it names
   (`[Red]`) and a wider value is rejected at the call, not at the match.
   The host contract (ADR 0015: a program handles a subset of the event
   vocabulary; ADR 0020 §2) *depends* on that narrowing.

## 3. Breakage

### 3.1 Spike results

Two spikes on `425a26a`, full workspace `cargo test --workspace --no-fail-fast`
(about 1750 tests):

| Spike | What it did | Failing tests |
|---|---|---|
| Lists only | list group built in Rust; prelude's `Empty`/`Link` removed | 28 distinct tests |
| Lists + lone tags | also: every non-prelude lone tag becomes a group of one with a payload parameter | 128 distinct test names (the same suite also repeats a test in `differential`, `wamr` and `native`) |

The second number is inflated by one cause: 76 failures are the message
`duplicate tag`. Many tests (and `examples/tags.goat`) write `tag Circle`,
`tag Triangle`, `tag Up` and so on, which are **host tag names**. Today a lone
redeclaration of a host tag silently joins the host's tag; a group of one is a
second declaration and is rejected as a duplicate. This is decision D6.

Failures by cause, from the first spike (lists):

1. **Heterogeneous lists that were never forced.** `docs/llm.md:414`
   (`h = [[2, "b"], [1, "z"], [2, "a"]]` under `sort`) and the matching ADR 0036
   text; a handful of tests.
2. **Tests that assert the open type.** `tests::constructing_a_tag_gives_an_open_row`
   (`"[Empty | t0]"`), `building_a_recursive_value_types_as_an_open_recursive_variant`,
   `rebuilding_a_scrutinee_ties_the_row_itself`, `match_types_to_its_arm_bodies`
   (matches `Full` against `Empty`/`Link`), and the like: rewrite to the closed
   type.
3. **Destructuring a literal by length.** `[a, b] = [3, 4]` fails with
   `` `match` doesn't handle `Link` `` (and then `Empty`). Today the literal's
   row records exactly its length, so the single-arm lowered `match` is
   exhaustive; a closed list has no length. Tests:
   `a_fixed_length_pattern_rejects_a_list_that_may_be_longer`,
   `list_destructuring_and_parameters` (also run through `differential`).
   This is a real behaviour change for kids (decision D7).
4. **`draw = program(m) do [] done`.** The host check `is_list_of_variants`
   wants the element to be a variant already, but `[]` has an unconstrained
   element. Needs to accept an unresolved element; five `interactive`/`canvas`/
   `native` tests fail for this one reason.
5. **Editor tag lists.** `query.rs::LIST_TAGS` and the web completion list
   `Link`/`Empty` among the host's tags; tests in `web/src/lib.rs` and
   `goat/tests/highlight.rs` changed.
6. **Reload test** named in 2.4, and `mir/tests/mono.rs::a_recursive_value_matched_at_two_widths_has_one_layout`
   (uses `Empty`/`Link` beside another tag in one row).
7. **Error blame** (`checker/tests/list_elements.rs`, 5 tests) fails only
   because of the whole-list span (2.2); fixable as said.

From the second spike (lone tags): the `duplicate tag` family above, plus every
test that mixes lone tags in one `if` or `match`, and the `lib.rs` tests that
assert open types (`match_with_else_keeps_the_row_open`,
`open_tag_fits_a_closed_match_but_a_stranger_does_not`,
`branches_building_different_tags_merge_into_one_open_row`). Those tests
document the very behaviour being removed, so they are rewritten or deleted,
not fixed.

### 3.2 Programs, examples, docs

| Where | What breaks | Migration |
|---|---|---|
| `examples/tags.goat` | `tag Circle`, `tag Square` matched together; also `Circle` is a host tag | `tag Shape = Circle(Number) \| Square(Number)`... payload types must then be named, see D1; rename if D6 forbids host names |
| `examples/` other than `tags.goat` | none (the other 31 examples type-check in the spike; the canvas ones need the canvas host and fail `check` before and after) | none |
| `docs/llm.md` (lists, tags, ordering) | the `h = [[2,"b"], ...]` example (line 414); no text there calls a lone tag open | edit |
| `docs/plan.md` line ~110 "a lone `tag Foo` stays an open tag"; Phase 7 text on open rows | text | edit; ADR 0016 amendment |
| ADR 0010, 0020, 0036 | prose about open rows and rank order | short amendments |
| prelude | `Empty`/`Link` declarations replaced by the built-in group; `DictLeaf`/`DictNode`/`Found`/`Missing` must become groups too, and need parameters for key and value (D1) | prelude edit, no logic change (spike: the prelude type-checks unchanged with lists built in) |
| user programs | any mixing of unrelated lone tags in one match or `if`; heterogeneous list literals; `tag X` where `X` is a host tag name; `[a, b] = [...]` by length | the error names the fix; D2 |

## 4. Decisions for the owner

Each has options, a goat example, and a recommendation. I decided none of them.
Wording in options is a candidate, not a pick.

**D1. How is the payload parameter introduced?**
A lone tag, the list, the dictionary and `Found`/`Missing` need a payload that
varies by use.
- (a) Built-in only. Lone tags and the prelude's groups get parameters from the
  compiler (the list group in Rust; the prelude's `Found`/`DictNode` marked in a
  small table). Users cannot write a parametric multi-tag group. `tag Shot =
  Miss | Hit(Int)` stays as it is. No new syntax.
- (b) Allow a bare lowercase payload name as an implicit parameter in a user
  group: `tag Result = Ok(value) | Failed(reason)`. This is the form the ticket
  text wrote (`tag Num(n) | Word(s)`). It makes capitalization-by-case matter
  for types again, against ADR 0016's principle, and is the "generic named
  types" ADR 0016 deferred.
- (c) Written parameters: `tag List(a) = Empty | Link(a, List(a))`. This is type
  annotation syntax; ruled out by the no-annotations decision.
Recommendation: (a). It meets the ticket, adds no syntax, and (b) can be added
later without breaking (a). Needs the prelude tag declarations spelled so the
compiler knows which are parametric; I would keep them as ordinary `tag Found |
Missing` lines plus a table in Rust.

**D2. How should a mismatch across two groups read?**
```
tag Ping
tag Pong
x = if true then Ping else Pong done
```
- (a) Today's generic message: `the tag Pong is not allowed here; the other side
  never has it`.
- (b) A message that says the two were declared apart and shows the fix:
  `Ping` and `Pong` are different tags with separate declarations; to use them
  in one place declare them together as `tag Ping | Pong`.
- (c) (b) shortened, no code.
And for the list: `xs = [1, "a"]`.
- (a) `type mismatch: expected Number, found String` at `"a"` (needs the span
  change in 2.2).
- (b) `a list holds one kind of thing; this is a String but the earlier items
  are Numbers`.
Recommendation: (b) for both, since the kid sees the fix. Kid-facing wording is
yours. The checker needs a "these two types came from separate declarations"
flag on a `Group` to produce the first.

**D3. Does a `match` pin its scrutinee to the arms' group?**
```
tag Light = Red | Green
f = program(l) do match l do Red then 1 done done   # today: error at the call f(Green)
```
- (a) Pin. Every arm's tag must belong to one group and the scrutinee takes that
  group. The error moves to the match: `match doesn't handle Green`, always, not
  only when a value of the whole group happens to flow in later. A match with an
  `else` over a lone tag becomes `f(Pong)`: an error.
- (b) Keep inferred narrow closed rows (today for groups). Smaller change;
  errors stay at the call.
Host families are the exception either way (D5).
Recommendation: (a). It makes the "closed" promise true for matches and removes
the order-dependence of `close_match`. Cost: medium (`constrain_arm`,
`close_match`, the `else` path in `infer_match`).

**D4. Where is an arm-group mismatch reported?**
```
tag Disc
tag Box
area = program(s) do match s do Disc(r) then r Box(w) then w done done
```
- (a) At the arms, by `lower` (it knows each tag's group), before inference:
  spanned at `Box`.
- (b) Where unification finds it (today, at the first call: `the tag Box is
  expected here, but this value is never Box`).
Recommendation: (a), free if D3 (a) is chosen.

**D5. Do the host's event and shape families become groups?**
- (a) Yes: the vocabulary declares each family as a group. The "handle a subset"
  contract (ADR 0015) then needs an exemption from D3: a host group's match
  without `else` still narrows.
- (b) No for now: they stay the one place with open-row inference, noted as an
  exception to "every tag is closed" in the ADR 0016 amendment.
Recommendation: (b), with the amendment naming the exception. (a) is a separate
ticket; it touches `vocab.rs`, `lower`, the interactive glue and ADR 0015/0020.

**D6. May a program declare a tag with a host tag's name?**
```
tag Circle            # the turtle's own shape tag
```
Today this joins the host's tag silently.
- (a) Error: `Circle` is a tag the host already provides.
- (b) The program's tag shadows the host's inside the program (the host never
  sees the program's `Circle` as a shape).
- (c) Keep silent joining. Not possible once a lone tag is a group of one (a
  second declaration of the same tag).
Recommendation: (a), with the hint of another name. It affects 76 failures in the
spike, the `tags.goat` example, and any kid who names a shape `Circle` in the
turtle. (b) is friendlier but needs a scope rule for tag names.

**D7. Destructuring a list by length.**
```
[a, b] = [3, 4]
```
- (a) Reject: `match doesn't handle Empty` style error on a closed list. The kid
  must write a `match` with `[]` and `[x, ...rest]`.
- (b) Accept a fixed-length pattern on a list *literal* only (the lowering knows
  the length), reject on any other list value.
- (c) Accept always with a runtime trap on the wrong length. Not recommended:
  it is a type hole.
Recommendation: (b) if kids use this form (the examples and `docs/llm.md` do
use destructuring); otherwise (a). Please say whether `[a, b] = xs` for a
non-literal `xs` should be allowed.

**D8. A lone tag matched with an `else`.**
```
tag Ping
f = program(p) do match p do Ping then 1 else 2 done done
```
The `else` can never run.
- (a) Allowed silently.
- (b) A warning: `else can't happen here; Ping is the only tag`.
- (c) An error.
Recommendation: (b). It teaches the rule without breaking programs that were
written when lone tags were open.

**D9. May two groups share a tag name?**
```
tag A = Red | Green
tag B = Red | Blue      # today: duplicate tag `Red`
```
- (a) No (today; one flat namespace, a tag belongs to exactly one declaration).
- (b) Yes; resolve by expected type. Needs bidirectional inference the checker
  does not have; ruled out by ADR 0027's rank-1 ceiling in spirit.
Recommendation: (a). Closing tags does not need it.

**D10. How should a list type print in hover and errors?**
Today: `μt6. [Empty, Link: {0: Number, 1: t6}]`.
- (a) Unchanged.
- (b) `List of Number` / `[Number]`.
Out of scope for this change unless you want it; the printer special-cases
nothing about lists today. Recommendation: (a) now, (b) as its own ticket.

**D11. Rename the list tags?** `Empty`/`Link` become reserved names. Keep as is
(recommended; the sugar `[]`/`[x, ...xs]` hides them and mono/reload recognise
them by name).

**D12. A host-written type that is a list.** A host payload field typed as a
list (`Polyline(points)`) already uses the closed list; no decision, noted.

## 5. Size and risk

| Area | Work | Size | Risk |
|---|---|---|---|
| Checker: parametric `Group`, list group, lone group-of-one | `Group` gains a parameter list; `instantiate` freshens it; `declare_tags` marks lone tags; list group installed in `lower_with_vocab`; `is_list_of_variants` accepts an unresolved element; `kinds.rs::constrain_list` stays valid; per-element `Link` span in `lower_list` | M | Low-medium. The spike did the core in about 40 lines. The unknown is mixed-group diagnostics (D2) |
| Checker: pin on match (D3), arm-group check (D4), `else` warning (D8) | `constrain_arm`, `close_match`, `infer_match`, a `lower` check | M | Medium. It changes errors users see, and the host exception (D5) must be right |
| Checker: tag-name rules (D6, D9) | `declare_tags` | S | Low |
| Checker: tests | rewrite roughly 30 open-type assertions in `lib.rs`, `list_elements.rs`, `interactive.rs`, etc.; add tests for each decision | M | Low |
| mono / codegen | none required. `canon.rs`, `mono/reload.rs`, `interactive.rs`, `structural.rs` already see closed lists. Rebuild `a_recursive_value_matched_at_two_widths_has_one_layout` and the reload shaped-like-list test. Optional later removal of ADR 0010 families | S | Low |
| Prelude | remove two lines, add the parametric marks for the dictionary tags; no logic change (spike) | S | Low |
| Editor | `query.rs::LIST_TAGS`, the web completion and tokenize lists (`web/src/lib.rs`, `web/completion.test.ts`), hover text for the closed list | S | Low. Hover prints the closed form, which is shorter than today's open form |
| Docs, examples | ADR 0016 amendment, edits to ADR 0010/0020/0036 prose, `docs/plan.md`, `docs/llm.md` (the heterogeneous `h` example), `examples/tags.goat` | S-M | Low |
| Proofs phase 3 (#452) | A smaller model: no variant row variables, no scoped-label variants, no `else`-open scrutinee; just groups with a declared parameter list, instantiated per construction, and `Rec`. It needs one more construction rule (instantiate the group, freshen the parameters), which matches the "one construction rule" note on #452. The D3 pin makes the match typing rule one rule too. D5 (b) leaves one open-row case outside the proofs, to be stated in the ADR | reduces the phase-3 work | Low if this lands first, as planned |

Suggested order after the owner answers: (1) parametric `Group` and the list
group, with the span change and the tests; (2) lone tags as groups of one with
D6; (3) the match rules (D3/D4/D8); (4) ADR 0016 amendment, docs, examples,
editor. Steps 1 and 2 can ship separately and each leaves the suite green.
