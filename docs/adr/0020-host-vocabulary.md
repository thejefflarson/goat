# ADR 0020 — A host declares its event/shape/key vocabulary; the compiler stops hard-coding the turtle's

- Status: proposed (2026-11-08)
- Context: #234 (follow-up to #227/#233, which put the host's `foreign` functions
  on `HostInterface`); ADR 0015 (the host-owned `init`/`update`/`draw` contract,
  which already calls the v1 Shape and event vocabulary "reversible, versioned
  data on top of the ABI"); ADR 0016 (tags are declared, not capitalized — it
  injects the vocab tag *names* as built-in declarations and flags "move the host
  vocabulary into a goat prelude" as a deferred, separable follow-on); ADR 0010
  (mono assigns variant tag numbers globally in sorted-label order, and the
  ADR-0015 reload fingerprint hashes them); ADR 0018 (one Rust conformance suite,
  a thin driver per host); ADR 0019 / PR #243 (the Phase-12 on-device runtime,
  proposed). This ADR extends ADR 0015; it supersedes nothing. Recorded as a
  decision draft before #234 is built, because #234 gates the second host (#111)
  and the embedded host's vocabulary (#117/#118).

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
vocabulary configurable — to thread a vocab *value* through the passes that today
read the constants — and warrants an ADR because the question is not only "where
does the list live" but "what, exactly, is a vocabulary, given that part of it is
backend marshalling code that no list of names can carry."

### What reads the vocabulary today, and how deeply

The checker side is already data-driven; the backend side is not. This is the
whole shape of the cost, so it is worth stating per pass:

| Pass | File | Reads the vocab as | How hard-coded |
|---|---|---|---|
| lower | `checker/src/lower.rs` | `vocab::tag_names()` → declared tag names; `vocab::key_group()` → the closed `Key` group | **data**: iterates a list, injects declarations |
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
constant. This ADR turns that data into something a host supplies.

## Decision

### 1. The vocabulary rides on `HostInterface`, as structured data, not as goat source

A host already has one value that means "what I offer a program" —
`HostInterface`. The vocabulary belongs on it (option (a) in #234), beside the
foreign-function prelude. The open choice is the *form*: a structured descriptor
the embedder builds in Rust (option (b)), or goat `tag` declarations in the
prelude the host already supplies (option (c)).

**Recommendation: a structured descriptor** — call it `Vocab` — that is the
host-supplied form of today's `checker/src/vocab.rs`. `HostInterface` gains a
`vocab: Vocab` field; `HostInterface::turtle()` supplies the turtle's, which is
the one that exists today lifted from constants into a value. For each event tag
and each shape tag the descriptor names: the tag, its payload goat type, and its
marshalling (below). It also carries the key group and the role split — which
tags are the event family and which are the shape family.

Source declarations (option (c)) are rejected as the *primary* mechanism, for
two concrete reasons, not a preference:

- **Open families have no source syntax.** Events and shapes are *open* tag
  families: ADR 0015 subscribes a program to exactly the tags its `update`
  handles, and an `else` arm adds none. `lower.rs` reflects this by injecting
  event/shape tags *ungrouped* (group `None`), unlike the `Key` group, which is
  closed. But ADR 0016's `tag` declaration always *closes* a set. So there is no
  way, in goat source today, to declare "these tags exist with these payloads, as
  an open family." Option (c) would need new language syntax for an open tag
  family — a bigger change than #234, and one that touches every program, not
  just hosts.
- **Source cannot carry the marshalling protocol.** A `tag` declaration gives the
  payload *type*; it does not say that a `Polyline` streams to `scene.polyline_*`
  by walking its `points` list, or that a `Line`'s fields go to `scene.line` in
  the order `x1,y1,x2,y2,color`. That protocol is item (3) above, and it is Rust.

The descriptor is also the right fit for who the consumer is. `HostInterface` is
a value a *Rust embedder* constructs — the turtle, #111, the Phase-11 embedding
API all build one in Rust. A structured `Vocab` matches that; a prelude string
would make the host round-trip its vocabulary through the parser to say something
the parser cannot fully say anyway.

> This does not abandon ADR 0016's "move the host vocab into a goat prelude"
> direction. ADR 0016 moved the vocab tag *names* into built-in declarations
> sourced from `vocab.rs`; this ADR moves the *source of those declarations* from
> a constant to the host's `Vocab`. The payload types stay goat types. What stays
> in Rust is only the marshalling the language has no way to express.

### 2. Marshalling is derived from payload types under one convention, not matched per tag

The structural `match label.as_str()` in `mir/src/mono/interactive.rs` is the
part that cannot simply read a list, and it is also the part most worth
*removing* rather than merely parameterizing. A `match` with an `unreachable!()`
default is exactly a vocabulary hard-coded in code; adding a host by adding an arm
is not "configurable."

**Recommendation: fix a flattening convention over payload types, and derive the
glue from the type.** Make every payload that crosses the ABI a tree of
host-native *leaves* — scalars (`Int`/`Float`), `String`, and records/lists of
those — and let the backend:

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

This leaves one genuinely host-semantic thing in today's tree that is **not**
derivable from a type: `key_of` / `ARROWS`, the browser `KeyboardEvent.key` →
`Key` mapping. It is a decoder, not a layout. Baking it into codegen *complects*
the compiler with one host's keyboard — the opposite of configurable.

**Recommendation: decouple it.** The `KeyDown`/`KeyUp` payload that crosses the
ABI is a `String`; the string→`Key` mapping becomes goat prelude code the turtle
`Vocab` ships (a `key_of : String -> Key` the turtle's `update` calls), not
compiler glue. Then the backend is fully generic — it marshals leaves — and each
host's decode semantics live where a host can change them: in that host's
`Vocab` prelude, checked like any goat code. A host with no keyboard (an embedded
sensor host) simply has no such decoder, instead of inheriting arrow strings it
will never see.

This is the sharpest point in the ADR, and §"Open questions" flags it for a
recorded decision: whether the arrow decode moves to the prelude (recommended,
backend stays generic) or stays a per-`Vocab` backend hook (smaller diff,
backend keeps one escape hatch).

### 3. Tag numbers stay mono-global and sorted-label; a host never picks a number

ADR 0010 assigns every variant tag a number globally, in sorted-label order over
all tags a program uses, and `mono.rs` adds the key group's tags when the program
is interactive. The ADR-0015 reload fingerprint (FNV-1a over the model's layout)
hashes those numbers, so layout stability depends on the numbering being a pure
function of the tag *set*.

A configurable vocabulary changes which tags enter that set, not how they are
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

### 4. Scope and sequencing: a turtle-first refactor that unblocks the second host

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
  "configurable" in the sense that matters.
- "Errors come only from the checker" is preserved and slightly strengthened: a
  host's vocabulary is goat types plus a marshalling descriptor, both fixed before
  mono runs, so mono still sees only well-typed closed variants. A host that
  declares an ill-formed payload type is a checker error against that host's
  prelude, not a mono panic.
- The turtle is unchanged in behavior and becomes the reference `Vocab`. Decoupling
  the key decode (§2) is the one turtle-facing change, and it is invisible to a
  program: the turtle `Vocab`'s prelude supplies the `key_of` its `update` already
  effectively calls.
- Cost, stated plainly: the checker side (`lower`/`infer`/`mono.rs`) is a
  parameter-threading change — pass the `Vocab` where the constants are read. The
  backend side (`mir/src/mono/interactive.rs`) is a genuine rewrite: `event_ctors`,
  `shape_func`, `points_walk`, and `key_of` go from per-tag `match` arms to one
  type-driven walk plus the decoupled decoder. That rewrite is the bulk of #234,
  and it is where the risk is — it must reproduce today's exact `scene.*` call
  sequence for the turtle, which the conformance suite pins.

### Reversible (versioned) parts — deliberately not one-way doors

- **The contents of any host's `Vocab`** — which events, shapes, and keys it
  offers, and their payloads. This is the whole point: growable per host without
  an ADR, extending ADR 0015's "the v1 vocabulary is versioned data."
- **The §2 marshalling convention's details** — the exact leaf-flattening order,
  how a `List` maps to begin/element/end. Internal to the compiler and the
  descriptor; changeable as long as every host's conformance cases stay green.
- **Where the key decode lives** (prelude vs. backend hook) — the §2 open
  question; either choice is reversible until a non-turtle host ships a decoder.

### One-way doors

- **The public shape of `HostInterface`'s `Vocab`** — what a Rust embedder passes
  to declare a vocabulary — becomes a stable contract once #111 and the embedding
  API (#111's "keep the embedding API honest") depend on it. Getting the
  descriptor's *form* right (§1) is the durable decision here.
- **The marshalling convention as a contract between the descriptor and the
  backend** — once a host relies on "my payload type determines my constructor
  signature and my scene calls," that mapping is load-bearing the way ADR 0015's
  scene-streaming protocol is.

## Open questions (flagged for a recorded decision)

If this ADR is accepted, the main loop should record the resolutions as an
amendment here (ADR 0015's pattern).

1. **The key decode (§2), the sharp one.** Move the browser `KeyboardEvent.key` →
   `Key` mapping out of `mir/src/mono/interactive.rs` into the turtle `Vocab`'s
   goat prelude (**recommended** — the backend becomes fully generic and no host
   inherits another's keyboard), or keep a per-`Vocab` backend decode hook (a
   smaller diff, but the backend keeps one host-semantic escape hatch that every
   future host must reason about)?
2. **Descriptor form (§1).** A structured Rust `Vocab` (**recommended**) versus
   growing goat with open-tag-family syntax so option (c) — an all-source
   vocabulary — becomes possible. The latter is the ADR-0016-gestured end state
   but a language change well beyond #234; recording "not now, and here is why"
   keeps the gesture from being read as a commitment.
3. **Relationship to WIT (Phase 11/12).** `docs/plan.md` has hosts declare their
   interface via WIT, and WIT already fits the *foreign-function* (import)
   direction. Events and shapes are not functions a program calls — they are
   variants the host constructs through compiler glue and a picture streamed as
   data — so WIT does not naturally express them, and this ADR keeps the `Vocab`
   its own concern. Whether #117/#118 express their embedded vocabulary *in* a
   `Vocab` descriptor or derive one from a WIT world is a Phase-12 detail to
   decide when those land, not now.
