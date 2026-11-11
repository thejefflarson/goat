# ADR 0009 — Strings are UTF-8 byte sequences, literals are immortal data-segment objects

- Status: accepted (2026-11-02)
- Context: Phase 5 (strings), ADR 0002, `docs/mir.md`, `docs/plan.md`

## Context

Phase 5 gives strings a runtime. Three choices are expensive to reverse once
programs, the host ABI, and later phases (concat, equality, lists of strings)
depend on them: how a literal is laid out in memory, how much string
functionality Phase 5 commits to, and what a string's bytes mean.

## Decision

1. **Layout.** A string is a heap object `[header][len: u32][bytes…]`
   (ADR 0002's header). A literal is an immortal object (`rc == u32::MAX`) that
   lives in the data segment, so it is never allocated, retained, or freed.
   Mono emits only the raw UTF-8 bytes of each distinct literal, one `DataId`
   per entry in `Program.data`; each backend builds the object and chooses the
   offsets. Identical literals share one entry.
2. **Phase 5 surface.** A string can be bound, passed, returned, and stored in
   a record, and the program can print it only as the program root, through the
   host import `goat.print_string(ptr)`. Printing mid-program, concatenation,
   and equality arrive in Phase 8. Mortal strings and host-provided strings
   (which need allocation and a drop path) arrive in Phase 8.5.
3. **Encoding.** A string is a sequence of UTF-8 bytes. `len` is the **byte**
   length. There is no codepoint indexing and no normalization; any later
   operation that needs code points iterates the bytes. This is the one-way
   door: it matches the WIT canonical ABI's UTF-8 `string`, so strings cross
   the component boundary without transcoding.

## Consequences

- Backends and the interpreter treat every string pointer as immortal in
  Phase 5, so reference counting never touches one and `live` allocations are
  unaffected by string literals.
- The interpreter surfaces the root string's bytes as `Outcome.root_string`;
  compiled backends call `goat.print_string` with the object pointer.
- Making a string mortal later changes only the allocation site and the drop
  path; the layout and the `Ptr(Str)` type stay.
- `char_at` makes the first string a program builds at run time: the backend
  allocates `12 + n` bytes through the runtime allocator (`rc = 1`, `len = n`,
  the code point's bytes copied from the source), and the normal drop path frees
  it like a host-supplied string. A code point is a non-continuation byte plus
  the continuation bytes after it; the scan and the copy are bounded by the
  header's `len`, so they stay inside the string even if it is not valid UTF-8.
  Code points are the unit for `char_count` and `char_at`; grapheme clusters are
  not provided.
- Because `len` counts bytes, a string with multi-byte characters has a `len`
  larger than its character count; user-facing length, if added, must say so.
