# Differential test: the proven algorithm against the Rust checker

ADR 0037 (decision 6) ties the inference algorithm proved in `proofs/` to
`checker/src/infer.rs` by running both on the same programs.

- `proofs/GoatInfer.v` is the algorithm (Hindley-Milner algorithm W with Leijen
  row unification). `proofs/GoatInferSound.v` proves it sound: every type it
  infers is derivable in `typing` (`infer_closed_sound`, no admits, no axioms).
- `proofs/GoatExtract.v` extracts it to OCaml (`goat_infer.ml`).
- `checker/examples/core_corpus.rs` collects programs and writes, for each one
  in the core fragment, its term (locally nameless s-expression) and the Rust
  checker's verdict (`ERR`, or `OK` and the type).
- `driver.ml` runs the extracted algorithm on each term and exits non-zero if
  acceptance differs or the types differ up to renaming of variables.

Run it with `make -C proofs differential` (it is part of `make -C proofs ci`
and of the `coq` workflow).

## Which programs are compared

Every goat source the repository holds: `examples/*.goat`, the `goat` blocks of
`docs/llm.md`, every string literal of the Rust sources under `checker/` and
`parser/` (tests included), a short list of hand-written programs, 4000
programs from a fixed-seed generator of the core, and 6000 from a fixed-seed
typed generator of the phase-1 forms. A program is compared when it is in the
fragment of `proofs/goat_ln.ott`: numerals, Float literals, strings, unit,
booleans, functions, calls, `if` with an `else`, the twelve binary operators on
Int, Float, String and Bool, `let` of a syntactic value that does not name
itself, record literals with distinct labels, and field access, binding every
name it uses. Anything else (the prelude, tags, `::`, dot calls, `self`, a `let`
of a computed value, an operator on records or on Unit) is outside the
calculus and skipped.

Two more kinds of program are skipped because the owner deferred them to phase
2 (generic operators): a program the checker accepts with a numeric type
variable left in a generalized function (`add = program(a, b) do a + b done`),
and a program that applies an operator to two operands whose types only a later
use settles (`program(x) do x > x done("a")`). The algorithm infers a function
before it sees the call, so it has no signature for such an operator.

## Where `float(e)` goes

The calculus has no implicit Int-to-Float widening, so the corpus writer
elaborates it from the checker's node types and the driver then requires the
proven algorithm to accept the result. It writes `float(e)` around

- an Int literal whose node type is Float (the context settled it);
- the Int operand of `+ - * < <= > >= == !=` whose other operand is a Float;
- each Int operand of `/` (a quotient is always a Float);
- an Int argument to a call whose callee's parameter is a Float.

If the checker widened anywhere else, the elaborated program would be rejected
and the driver would report a mismatch. A rejected program has no node types
and is written with no coercions. This is a differential check, not a theorem:
a full proof would need a model of the checker's elaborator.

The calculus is curried, so a program whose functions and calls all take one
parameter or argument (`U` lines) is compared in both directions. A program with
several (`N` lines) is compared only when the Rust checker accepts it, since the
Rust checker rejects a partial call that the curried calculus accepts.

A `let` of a computed value is skipped because the Rust checker does not
generalize it (the value restriction, ADR 0027) and the calculus does.

## Types up to renaming

Both sides print the type in one form: functions curried, record fields in label
order (labels numbered by first occurrence in the program; a stable sort, so
repeated labels keep their order), type and row variables numbered by first
occurrence. Rust's `Int` is the calculus's `Number`.

## What it does not show

A disagreement is caught only on a tested program. The generator and the
corpus are finite, which is the gap ADR 0037 accepts.
