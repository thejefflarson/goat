# ADR 0020 — A host declares its event/shape/key vocabulary; the compiler stops hard-coding the turtle's

- Status: accepted (2026-11-08)
- Context: #234 (follow-up to #227/#233, which put the host's `foreign` functions
  on `HostInterface`); ADR 0015 (the host-owned `init`/`update`/`draw` contract,
  which already calls the v1 Shape and event vocabulary "reversible, versioned
  data on top of the ABI", and whose §4 "as built #106" note already *closes* the
  event/shape rows to the tags a program handles or draws); ADR 0016 (tags are
  declared, not capitalized — a `tag` declaration is a *closed* variant type; it
  injects the vocab tag *names* as built-in declarations and flags "move the host
  vocabulary into a goat prelude" as a deferred, separable follow-on); ADR 0010
  (mono assigns variant tag numbers globally in sorted-label order, and the
  ADR-0015 reload fingerprint hashes them); ADR 0018 (one Rust conformance suite,
  a thin driver per host); ADR 0019 / PR #243 (the Phase-12 on-device runtime,
  proposed). This ADR extends ADR 0015; it supersedes nothing. Recorded as a
  decision before #234 is built, because #234 gates the second host (#111) and
  the embedded host's vocabulary (#117/#118).

## Context

Today a goat host supplies two things that are, in principle, the same kind of
thing — "what this host and a goat program say to each other" — but live in two
very different places.

The **foreign functions** a program may call ride on `HostInterface`
(`goat/src/lib.rs`): the value carries a `prelude: String` of goat source, the
host's `foreign` declarations are checked like any binding, and a foreign call
lowers to one generic `CallForeign(import, args)` with no per-function code in
the backend. A host changes its foreign surface by changing a string. #227/#233
put it there; it works.

The **event/shape/key vocabulary** does not ride on `HostInterface`. It is
hard-coded in the checker as compile-time constants in `checker/src/vocab.rs`:
`EVENT_TAGS` (`Tick`, `KeyDown`, `KeyUp`, `Pointer{Move,Down,Up}`), `SHAPE_TAGS`
(`Polyline`, `Line`), `KEY_TAGS` (`Up`/`Down`/`Left`/`Right`/`Other`), and the
`event_payload`/`shape_payload`/`key_group` functions that give each tag its goat
type. `HostInterface`'s own doc comment says so outright: the events and shapes
"are fixed by the checker's `vocab` (ADR 0015), so they are not part of this
value." Every host therefore speaks the *turtle's* vocabulary, whatever it is.

That is fine while the turtle is the only interactive host. It stops being fine
at the next one. A p5-style game host (#111) wants its own events and shapes; an
embedded host (#117/#118) wants `ButtonPress`, `Timer`, `SensorReading` in and
LED/GPIO shapes out, not `Polyline` and `Pointer`. #234 asks to make the
vocabulary host-supplied — to thread a vocab *value* through the passes that today
read the constants — and warrants an ADR because the question is not only "where
does the list live" but "what, exactly, is a vocabulary, given that part of it is
backend marshalling code that no list of names can carry."

### What reads the vocabulary today, and how deeply

The checker side is already data-driven; the backend side is not. This is the
whole shape of the cost, so it is worth stating per pass:

| Pass | File | Reads the vocab as | How hard-coded |
|---|---|---|---|
| lower | `checker/src/lower.rs` | `vocab::tag_names()` → declared event/shape tag names; `vocab::key_group()` → the closed `Key` group | **data**: iterates a list, injects declarations |
| infer | `checker/src/infer.rs` (`check_events`/`check_shapes`) | `EVENT_TAGS`/`SHAPE_TAGS` as an allowlist; `event_payload`/`shape_payload` as a payload oracle to unify against | **data**: reads lists and calls the payload functions |
| mono | `mir/src/mono.rs` | `KEY_TAGS` to lay out the full `Key` group when interactive | **data**: extends the tag set |
| mono glue | `mir/src/mono/interactive.rs` | per-tag constructor and scene-streaming code | **structural Rust**: see below |

`checker/src/vocab.rs` is already the single source of truth for the *names and
payload types*, and `lower`/`infer`/`mono.rs` consume it as data. If a
vocabulary were only names and types, #234 would be "pass the struct instead of
reading the const" — mechanical.

It is not only names and types. `mir/src/mono/interactive.rs` encodes, in Rust, a
`match label.as_str()` that knows each tag *structurally*:

- `event_ctors` builds `goat_event_<Tag>` by matching `"Tick"` (one `Float`
  arg), `"KeyDown" | "KeyUp"` (a `String` arg run through `key_of`),
  `"Pointer*"` (two `Float` args assembled into a `{x, y}` record), and
  `unreachable!()` for anything else.
- `key_of` + the `ARROWS` table hard-code that a `KeyboardEvent.key` string maps
  to a `Key` tag — browser keyboard semantics, baked into codegen.
- `shape_func` matches `"Line"` (read fields `x1,y1,x2,y2,color`, call the
  `scene.line` import) and `"Polyline"` (read `color` and the `points` list,
  call `scene.polyline_begin` / `scene.vertex` per point / `scene.polyline_end`),
  and `unreachable!()` otherwise.

So a vocabulary is really three things braided together: (1) an allowlist of tag
names, (2) a payload type per tag, and (3) a **marshalling protocol** — how a
flat tuple of host-native values becomes a goat payload (event construction) and
how a goat payload becomes a sequence of `scene.*` host calls (picture
streaming). The checker needs (1) and (2); the backend glue needs (3). Goat
source can express (1) and (2); it cannot express (3). That is the real design
question #234 forces, and ADR 0015 already anticipated it by calling the
vocabulary "versioned data on top of the ABI" while leaving the data a compiler
constant. This ADR turns that data into something a host supplies — without
loosening what kind of thing it is.

### The vocabulary is closed; "host-configured" does not change that

A host's events, shapes, and keys are each a **closed** set of tags. ADR 0015
subscribes a program to exactly the tags its `update` handles or its `draw`
draws, rejects a tag the host doesn't send (*"the host doesn't send a
`Frobnicate` event"*), and unifies each payload with the vocabulary; its §4 "as
built #106" note records that the checker *closes* the event and shape rows to
those tags, so a key `match` with no `else` must name all five `Key` tags. ADR
0016 makes a `tag` declaration a closed variant type and relies on the same
`close_match` machinery for exhaustiveness.

Making the vocabulary host-supplied is a question of *where the closed set comes
from*, not whether it is closed. **"Configurable per host" is not "open in the
type system."** Each host declares its own closed set of event/shape/key tags;
the set is host-supplied rather than a compiler constant, but within any one
compilation it is fixed and closed. This is deliberately **not**
row-polymorphic or extensible-membership variants — a program cannot add a tag
to a host's vocabulary, and the checker's exhaustiveness guarantee is unchanged.

## Decision

### 1. The vocabulary is a set of closed tag families, supplied per host as a structured `Vocab` on `HostInterface`

A host already has one value that means "what I offer a program" —
`HostInterface`. The vocabulary belongs on it, beside the foreign-function
prelude. `HostInterface` gains a `vocab: Vocab` field; `HostInterface::turtle()`
supplies the turtle's, which is the one that exists today lifted from the
`checker/src/vocab.rs` constants into a value. For each event tag and each shape
tag the descriptor names: the tag, its payload goat type, and its marshalling
(§2). It also carries the key group and the role split — which tags are the event
family and which are the shape family. Each of these is a closed set; the `Vocab`
is the host's declaration of them.

`Vocab` is a **structured descriptor the Rust embedder builds**, not goat source,
for two reasons:

- **The consumer is a Rust embedder.** `HostInterface` is a value the turtle,
  #111, and the Phase-11 embedding API each construct in Rust. A structured
  `Vocab` matches that; a prelude string would make the host round-trip its
  vocabulary through the parser.
- **Source cannot carry the marshalling protocol.** A declaration can give the
  payload *type*; it cannot say that a `Polyline` streams to `scene.polyline_*`
  by walking its `points` list, or that a `Line`'s fields go to `scene.line` in
  the order `x1,y1,x2,y2,color`. That protocol is item (3) above, and it is Rust.
  The payload *types* in a `Vocab` stay goat types; only the marshalling, which
  the language has no way to express, stays in Rust.

This resolves the "move the host vocab into a goat prelude" gesture ADR 0016
deferred: the *source* of the vocabulary moves from a compiler constant to the
host's structured `Vocab` — not to a shared goat prelude. The tag names and
payload types that ADR 0016 injects as built-in declarations now come from the
host's `Vocab` instead of `vocab.rs`, keeping it the single source of truth for a
host's contract while leaving ADR 0016's closed-`tag` semantics exactly as they
are.

**Open variants are a non-goal.** An earlier draft of this ADR framed events and
shapes as *open* tag families and weighed growing goat with new "open-tag-family"
syntax so a host could declare an all-source vocabulary. That framing was wrong
and that option is rejected outright — not deferred research, and not tied to any
future language tier. A host's event, shape, and key families are closed sets;
the checker's exhaustiveness guarantee (§2) depends on that closedness; goat gains
no open-tag syntax. The only thing that is host-configured is *which closed set*
a host declares.

### 2. The checker enforces closedness unchanged; marshalling is derived from payload types

Nothing about host-supplying the vocabulary weakens exhaustiveness. The checker
closes an event/shape variant exactly as it does today: a `match` **without**
`else` closes the scrutinee's variant to the named tags and requires them to be
exhaustive, and `else` is the opt-in catch-all. The grammar makes the `else` arm
optional — `match_expr = { match ~ expr ~ do ~ arm* ~ else_branch? ~ done }`,
`else_branch` optional — and `infer_match` in `checker/src/infer.rs` calls
`close_match` precisely in the no-`else`, variant case. The host's `Vocab`
supplies the allowlist (`check_events`/`check_shapes`) and the payload oracle
that each handled tag unifies against; the closing step is untouched. A program
still handles a *subset* of the host's closed vocabulary (ADR 0015: the host
enables a superset of the handled tags), and every tag it names must be in that
vocabulary. The internal scoped-label rows that inference uses to get there —
records, and an event/shape row extended per arm and then closed — are an
inference detail, never a surfaced open variant.

The structural `match label.as_str()` in `mir/src/mono/interactive.rs` is the one
part that cannot simply read a list, and it is also the part most worth
*removing* rather than merely parameterizing. A `match` with an `unreachable!()`
default is a vocabulary hard-coded in code; adding a host by adding an arm is not
"host-supplied." So the glue is fixed over a flattening convention on payload
types and derived from the type:

- **construct** an event by flattening the payload type's scalar/string leaves,
  left to right, into the `goat_event_<Tag>` parameter list, then rebuilding the
  record/variant structure around them. `Tick(Float)` → one `Float` param;
  `PointerMove({x,y})` → two `Float` params assembled into the record. No tag
  name appears in the rule.
- **stream** a shape by walking the payload type: a scalar/string leaf becomes a
  `scene.*` argument, a `List` becomes a `begin` / per-element / `end` triple.
  The `scene` import name is part of the descriptor (`Line` → `"line"`), the
  argument order is the payload record's field order, and the per-frame vertex
  budget bounds the list walk exactly as it does today.

Deriving the `goat_event_<Tag>` constructors and the scene-streaming glue from a
`Vocab`'s payload types is the expensive part of #234, and it is what lets a new
host add a `Vocab` rather than a backend arm with an `unreachable!()` default.

### 3. The key decode belongs to the host, inside its `Vocab` — keys in browser

One thing in today's tree is genuinely host-semantic and **not** derivable from a
payload type: `key_of` / `ARROWS`, the browser `KeyboardEvent.key` → `Key`
mapping. It is a decoder, not a layout. Baking it into codegen *complects* the
compiler with one host's keyboard — the opposite of host-supplied.

**The key decode belongs to the host, carried in its `Vocab`.** The browser host
does `KeyboardEvent.key → Key` as part of *its* (closed) `Vocab`: the decode
travels with the browser host, where a browser can change it. It is **not**
hard-coded in the compiler backend (today's `key_of`/`ARROWS` in
`mir/src/mono/interactive.rs` go away), and it is **not** forced into a shared
goat prelude that every host inherits. The payload that crosses the ABI for
`KeyDown`/`KeyUp` is a `String`; turning that `String` into a `Key` is the
browser `Vocab`'s concern. With the decode gone from codegen, the backend is
fully generic — it marshals leaves (§2) — and a host with no keyboard (an
embedded sensor host) carries no such decoder, rather than inheriting arrow
strings it will never see.

### 4. Tag numbers stay mono-global and sorted-label; a host never picks a number

ADR 0010 assigns every variant tag a number globally, in sorted-label order over
all tags a program uses, and `mono.rs` adds the key group's tags when the program
is interactive. The ADR-0015 reload fingerprint (FNV-1a over the model's layout)
hashes those numbers, so layout stability depends on the numbering being a pure
function of the tag *set*.

A host-supplied vocabulary changes which tags enter that set, not how they are
numbered. The rule holds unchanged:

- The `Vocab`'s tags join the mono-global set the same way the constants do
  today, and numbering stays sorted-label over the union of (the program's tags
  ∪ the `Vocab`'s tags). The order a host *lists* its tags in the descriptor is
  irrelevant — sorting erases it — so two hosts that declare the same tag set in
  different orders get identical layouts.
- A host **MUST NOT** pin an explicit tag number. Letting a host choose numbers
  would fork ADR 0010's single global rule, let two hosts disagree on a layout
  for the same tag, and make the fingerprint meaningless across them. Tag numbers
  are the compiler's, derived; the host supplies names and types.
- The fingerprint already scopes a saved model to one host's vocabulary, because
  the vocabulary's tags feed the numbering that feeds the hash. A model saved
  under host A's `Vocab` and reloaded under host B's gets a different fingerprint
  and is reset — which is correct, and is the existing invariant, not a new one.

For the turtle, nothing moves: the same tags, sorted the same way, get the same
numbers and the same fingerprint as today. #234 is behavior-neutral for it by
construction.

### 5. Scope and sequencing: a turtle-first refactor that unblocks the second host

#234 is "not needed for the turtle or the #228 driver," and this ADR keeps it
that way: the deliverable is a refactor that lifts `checker/src/vocab.rs` from
constants into `HostInterface::turtle()`'s `Vocab`, with the turtle as the first
and initially only client. ADR 0018's one Rust conformance suite is the proof:
every existing interactive case must pass unchanged with the turtle vocabulary
now supplied as data. A green suite is the whole acceptance test — no new host is
needed to land #234.

Dependencies, stated precisely because the task's "sits behind ADR 0019" is easy
to over-read:

- #234 is a checker/mono refactor. It is **independent of ADR 0019** (PR #243),
  which decides the on-device *runtime* (WAMR, tail calls) — a different layer.
  #234 can land whenever; it needs no runtime decision.
- #234 **unblocks #111** (the Rust p5-style second host) directly. #111 is a
  desktop Rust host and needs no embedded runtime, so it depends on #234 and not
  on ADR 0019.
- #234 **unblocks the vocabulary half of #117/#118** (the embedded host's events
  and shapes). Those hosts *also* need ADR 0019's runtime to run at all, so their
  full delivery sits behind both.

Recommended order: **#234 first** (turtle-first, behavior-neutral refactor; can
start now), then **#111** on top of it, and **#117/#118** once both #234 and ADR
0019 have landed. #234 delivers no user-visible change on its own — it buys the
*ability* to add a host — so sequence it just ahead of the first host that needs
it rather than for its own sake.

## Consequences

- A vocabulary becomes what ADR 0015 already called it — versioned data on top of
  a fixed ABI — now literally host-supplied rather than a checker constant. The
  ABI *shape* (the export set, the owned-pointer convention, exports-as-
  subscription, the scene-streaming protocol) is untouched; §2's convention is
  how a `Vocab` is *realized* onto that unchanged ABI.
- The backend stops carrying one host's vocabulary. Removing the
  `match label.as_str()` arms in favor of type-driven marshalling (§2) means a new
  host adds a `Vocab`, not a backend arm with an `unreachable!()` default —
  host-supplied in the sense that matters.
- "Errors come only from the checker" is preserved and slightly strengthened: a
  host's vocabulary is closed goat types plus a marshalling descriptor, both fixed
  before mono runs, so mono still sees only well-typed closed variants. A host
  that declares an ill-formed payload type is a checker error against that host's
  vocabulary, not a mono panic. Exhaustiveness is exactly as strong as before
  (§2): host-configuring the vocabulary does not open it.
- The turtle is unchanged in behavior and becomes the reference `Vocab`. Moving
  the key decode (§3) out of codegen into the browser `Vocab` is the one
  turtle-facing change, and it is invisible to a program: the same
  `KeyboardEvent.key` → `Key` mapping, now owned by the host that has a keyboard.
- Cost, stated plainly: the checker side (`lower`/`infer`/`mono.rs`) is a
  parameter-threading change — pass the `Vocab` where the constants are read. The
  backend side (`mir/src/mono/interactive.rs`) is a genuine rewrite: `event_ctors`,
  `shape_func`, `points_walk`, and `key_of` go from per-tag `match` arms to one
  type-driven walk (§2), with the key decode leaving codegen entirely (§3). That
  rewrite is the bulk of #234, and it is where the risk is — it must reproduce
  today's exact `scene.*` call sequence for the turtle, which the conformance
  suite pins.

### Reversible (versioned) parts — deliberately not one-way doors

- **The contents of any host's `Vocab`** — which events, shapes, and keys it
  offers, and their payloads. This is the whole point: a host may ship a
  *different* closed set, or grow its set in a later version, without an ADR,
  extending ADR 0015's "the v1 vocabulary is versioned data." Within any one
  compilation the set is still fixed and closed; versioning the set is not opening
  it.
- **The §2 marshalling convention's details** — the exact leaf-flattening order,
  how a `List` maps to begin/element/end. Internal to the compiler and the
  descriptor; changeable as long as every host's conformance cases stay green.
- **The form of a host's key decode inside its `Vocab`** — the browser host owns
  the `KeyboardEvent.key` → `Key` mapping (§3); how that `Vocab` expresses it is
  the host's to change, as long as it stays out of codegen and out of a shared
  prelude.

### One-way doors

- **The public shape of `HostInterface`'s `Vocab`** — what a Rust embedder passes
  to declare a vocabulary — becomes a stable contract once #111 and the embedding
  API depend on it. Getting the descriptor's *form* right (§1) is the durable
  decision here.
- **The marshalling convention as a contract between the descriptor and the
  backend** — once a host relies on "my payload type determines my constructor
  signature and my scene calls," that mapping is load-bearing the way ADR 0015's
  scene-streaming protocol is.

### Deliberately deferred

- **Relationship to WIT (Phase 11/12).** `docs/plan.md` has hosts declare their
  interface via WIT, and WIT already fits the *foreign-function* (import)
  direction. Events and shapes are not functions a program calls — they are
  closed variants the host constructs through compiler glue and a picture streamed
  as data — so WIT does not naturally express them, and this ADR keeps the `Vocab`
  its own concern. Whether #117/#118 express their embedded vocabulary *in* a
  `Vocab` descriptor or derive one from a WIT world is a Phase-12 detail to decide
  when those hosts land, not now.

## As built

- `goat_checker::Vocab` holds `events`, `shapes`, the `keys` group and a goat
  `prelude`. An event tag names its goat payload type and, optionally, a
  `Decode { wire, function }`: the host sends the leaves of `wire` and the goat
  function `function` in the host's prelude turns them into the payload. A shape
  tag names its payload and the `scene.*` imports it streams through
  (`SceneCalls::Call` for flat payloads, `Stream` for one list).
  `Vocab::validate` rejects a vocabulary the backend cannot realize with a
  checker error.
- The turtle's `key_of` (the `KeyboardEvent.key` to `Key` decode) is goat in
  `prelude/turtle_keys.goat`, carried by `Vocab::turtle()`. Lowering adds each
  decoder to the interactive root record (labelled `@<function>`) so inference
  checks its type and mono specializes it for the event constructors.
- Leaf order is the declared field order of the payload type; arguments to a
  `scene.*` call follow it. The backend reads fields by name, so the order mono
  lays records out in does not matter.
- A decoder's tags join the tag set only when something uses it (an
  interactive program's root record does; so does a program that calls it), so
  a turtle program that never decodes an event is numbered exactly as before
  `key_of` moved into the prelude. Tag numbers stay a pure function of the set
  (§4).
